//! Tests for weakest-precondition VC generation.
//!
//! The oracle here is a bounded model check. It enumerates every assignment
//! with small values and looks for one that satisfies the assumptions but
//! falsifies the goal. It cannot prove a VC valid, but it catches wrong VCs
//! without a solver. The Z3 tests at the end check the real proofs.

use std::collections::BTreeMap;

use tpt_proof_contract::smt::{check, encode, SolverConfig};
use tpt_proof_contract::vc::{Expr, Sort, Vc};
use tpt_proof_contract::wp::{generate, Function, Stmt, WpError};
use tpt_proof_contract::Outcome;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Val {
    Int(i64),
    Bool(bool),
}

fn int(v: Val) -> i64 {
    match v {
        Val::Int(n) => n,
        Val::Bool(_) => panic!("expected an integer"),
    }
}

fn boolean(v: Val) -> bool {
    match v {
        Val::Bool(b) => b,
        Val::Int(_) => panic!("expected a boolean"),
    }
}

fn eval(expr: &Expr, env: &BTreeMap<String, Val>) -> Val {
    match expr {
        Expr::Int(n) => Val::Int(*n),
        Expr::Bool(b) => Val::Bool(*b),
        Expr::Var(name) => env[name],
        Expr::Add(a, b) => Val::Int(int(eval(a, env)) + int(eval(b, env))),
        Expr::Sub(a, b) => Val::Int(int(eval(a, env)) - int(eval(b, env))),
        Expr::Mul(a, b) => Val::Int(int(eval(a, env)) * int(eval(b, env))),
        Expr::Div(a, b) => Val::Int(int(eval(a, env)) / int(eval(b, env))),
        Expr::Rem(a, b) => Val::Int(int(eval(a, env)) % int(eval(b, env))),
        Expr::Lt(a, b) => Val::Bool(int(eval(a, env)) < int(eval(b, env))),
        Expr::Le(a, b) => Val::Bool(int(eval(a, env)) <= int(eval(b, env))),
        Expr::Eq(a, b) => Val::Bool(eval(a, env) == eval(b, env)),
        Expr::Not(a) => Val::Bool(!boolean(eval(a, env))),
        Expr::And(items) => Val::Bool(items.iter().all(|e| boolean(eval(e, env)))),
        Expr::Or(items) => Val::Bool(items.iter().any(|e| boolean(eval(e, env)))),
        Expr::Implies(a, b) => Val::Bool(!boolean(eval(a, env)) || boolean(eval(b, env))),
    }
}

/// Searches every assignment with integers in `-range..=range` for one where
/// the assumptions hold and the goal fails.
fn find_counterexample(vc: &Vc, range: i64) -> Option<BTreeMap<String, Val>> {
    let domains: Vec<(String, Vec<Val>)> = vc
        .vars
        .iter()
        .map(|(name, sort)| {
            let values = match sort {
                Sort::Int => (-range..=range).map(Val::Int).collect(),
                Sort::Bool => vec![Val::Bool(false), Val::Bool(true)],
            };
            (name.clone(), values)
        })
        .collect();
    let total: usize = domains.iter().map(|(_, values)| values.len()).product();
    for index in 0..total {
        let mut rest = index;
        let mut env = BTreeMap::new();
        for (name, values) in &domains {
            env.insert(name.clone(), values[rest % values.len()]);
            rest /= values.len();
        }
        let assumptions_hold = vc.assumptions.iter().all(|a| boolean(eval(a, &env)));
        if assumptions_hold && !boolean(eval(&vc.goal, &env)) {
            return Some(env);
        }
    }
    None
}

fn var(name: &str) -> Expr {
    Expr::Var(name.to_string())
}

fn int_lit(n: i64) -> Expr {
    Expr::Int(n)
}

fn add(a: Expr, b: Expr) -> Expr {
    Expr::Add(Box::new(a), Box::new(b))
}

fn sub(a: Expr, b: Expr) -> Expr {
    Expr::Sub(Box::new(a), Box::new(b))
}

fn lt(a: Expr, b: Expr) -> Expr {
    Expr::Lt(Box::new(a), Box::new(b))
}

fn le(a: Expr, b: Expr) -> Expr {
    Expr::Le(Box::new(a), Box::new(b))
}

fn eq(a: Expr, b: Expr) -> Expr {
    Expr::Eq(Box::new(a), Box::new(b))
}

fn assign(name: &str, value: Expr) -> Stmt {
    Stmt::Assign {
        var: name.to_string(),
        value,
    }
}

/// `sum(n)`: sets x to n by counting i up to n.
fn count_to_n(invariant: Expr) -> Function {
    Function {
        name: "count_to_n".to_string(),
        vars: vec![
            ("n".to_string(), Sort::Int),
            ("i".to_string(), Sort::Int),
            ("x".to_string(), Sort::Int),
        ],
        requires: vec![le(int_lit(0), var("n"))],
        ranges: vec![],
        body: vec![
            assign("i", int_lit(0)),
            assign("x", int_lit(0)),
            Stmt::While {
                cond: lt(var("i"), var("n")),
                invariant,
                body: vec![
                    assign("x", add(var("x"), int_lit(1))),
                    assign("i", add(var("i"), int_lit(1))),
                ],
            },
        ],
        ensures: vec![eq(var("x"), var("n"))],
    }
}

fn good_invariant() -> Expr {
    Expr::And(vec![
        le(int_lit(0), var("i")),
        le(var("i"), var("n")),
        eq(var("x"), var("i")),
    ])
}

#[test]
fn loop_with_a_correct_invariant_has_no_counterexample() {
    let vcs = generate(&count_to_n(good_invariant())).expect("generates");
    assert_eq!(vcs.len(), 1);
    encode(&vcs[0]).expect("the VC is well-sorted");
    assert_eq!(find_counterexample(&vcs[0], 2), None);
}

#[test]
fn loop_with_a_wrong_invariant_has_a_counterexample() {
    // x == i + 1 is false on entry, where x = i = 0.
    let wrong = Expr::And(vec![
        le(int_lit(0), var("i")),
        le(var("i"), var("n")),
        eq(var("x"), add(var("i"), int_lit(1))),
    ]);
    let vcs = generate(&count_to_n(wrong)).expect("generates");
    assert!(find_counterexample(&vcs[0], 2).is_some());
}

#[test]
fn wrong_postcondition_has_a_counterexample() {
    let mut function = count_to_n(good_invariant());
    function.ensures = vec![eq(var("x"), add(var("n"), int_lit(1)))];
    let vcs = generate(&function).expect("generates");
    assert!(find_counterexample(&vcs[0], 2).is_some());
}

#[test]
fn assert_inside_a_loop_is_checked_on_every_iteration() {
    // The assertion i < 1 fails on the second iteration, where i = 1.
    let mut function = count_to_n(good_invariant());
    if let Stmt::While { body, .. } = &mut function.body[2] {
        body.insert(0, Stmt::Assert(lt(var("i"), int_lit(1))));
    }
    let vcs = generate(&function).expect("generates");
    assert!(find_counterexample(&vcs[0], 2).is_some());
}

#[test]
fn havoc_stops_a_loop_from_hiding_its_effects() {
    // After the loop x may be anything satisfying the invariant, so x == 1
    // cannot be guaranteed when the body sets x to 0. (Constants stay in the oracle range.)
    let function = Function {
        name: "clobber".to_string(),
        vars: vec![("i".to_string(), Sort::Int), ("x".to_string(), Sort::Int)],
        requires: vec![eq(var("x"), int_lit(1))],
        ranges: vec![],
        body: vec![
            assign("i", int_lit(0)),
            Stmt::While {
                cond: lt(var("i"), int_lit(1)),
                invariant: Expr::Bool(true),
                body: vec![assign("x", int_lit(0)), assign("i", int_lit(1))],
            },
        ],
        ensures: vec![eq(var("x"), int_lit(1))],
    };
    let vcs = generate(&function).expect("generates");
    assert!(find_counterexample(&vcs[0], 2).is_some());
}

#[test]
fn if_statement_absolute_value() {
    let abs = |post: Expr| Function {
        name: "abs".to_string(),
        vars: vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        requires: vec![],
        ranges: vec![],
        body: vec![Stmt::If {
            cond: lt(var("x"), int_lit(0)),
            then_branch: vec![assign("y", sub(int_lit(0), var("x")))],
            else_branch: vec![assign("y", var("x"))],
        }],
        ensures: vec![post],
    };

    let good = generate(&abs(le(int_lit(0), var("y")))).expect("generates");
    assert_eq!(find_counterexample(&good[0], 2), None);

    let bad = generate(&abs(eq(var("y"), var("x")))).expect("generates");
    assert!(find_counterexample(&bad[0], 2).is_some());
}

#[test]
fn assumptions_are_used_in_the_vc() {
    let function = Function {
        name: "assume".to_string(),
        vars: vec![("x".to_string(), Sort::Int)],
        requires: vec![],
        ranges: vec![],
        body: vec![
            Stmt::Assume(lt(int_lit(0), var("x"))),
            Stmt::Assert(le(int_lit(1), var("x"))),
        ],
        ensures: vec![Expr::Bool(true)],
    };
    let vcs = generate(&function).expect("generates");
    assert_eq!(find_counterexample(&vcs[0], 2), None);
}

#[test]
fn assignment_to_an_undeclared_variable_is_an_error() {
    let function = Function {
        name: "bad".to_string(),
        vars: vec![("x".to_string(), Sort::Int)],
        requires: vec![],
        ranges: vec![],
        body: vec![assign("z", int_lit(1))],
        ensures: vec![Expr::Bool(true)],
    };
    assert_eq!(
        generate(&function),
        Err(WpError::UndeclaredVariable("z".to_string()))
    );
}

#[test]
#[ignore = "requires z3 on PATH"]
fn z3_proves_the_loop_vc() {
    let vcs = generate(&count_to_n(good_invariant())).expect("generates");
    let outcome = check(&vcs[0], &SolverConfig::default());
    assert_eq!(outcome, Outcome::SolverUnsat, "got {outcome:?}");
}

/// `x := x + 1` on a variable bounded to `0..=2`.
fn bump_bounded(requires: Vec<Expr>) -> Function {
    Function {
        name: "bump".to_string(),
        vars: vec![("x".to_string(), Sort::Int)],
        requires,
        body: vec![assign("x", add(var("x"), int_lit(1)))],
        ensures: vec![Expr::Bool(true)],
        ranges: vec![("x".to_string(), 0, 2)],
    }
}

#[test]
fn overflow_is_an_obligation_on_assignment() {
    // With x = 2 the new value 3 is out of 0..=2.
    let function = bump_bounded(vec![le(int_lit(0), var("x"))]);
    let vcs = generate(&function).expect("generates");
    assert!(find_counterexample(&vcs[0], 2).is_some());
}

#[test]
fn no_overflow_when_the_precondition_keeps_the_value_in_range() {
    let function = bump_bounded(vec![le(int_lit(0), var("x")), le(var("x"), int_lit(1))]);
    let vcs = generate(&function).expect("generates");
    assert_eq!(find_counterexample(&vcs[0], 2), None);
}

#[test]
fn bounded_loop_variables_are_in_range_at_the_loop_head() {
    // i is bounded to 0..=2. The loop only increments it while i < 2, so
    // i == 2 holds on exit. Without the range facts the havoced i could be
    // anything, which the oracle domain cannot show directly; the VC still
    // must have no counterexample in range.
    let function = Function {
        name: "count".to_string(),
        vars: vec![("i".to_string(), Sort::Int)],
        requires: vec![le(int_lit(0), var("i")), le(var("i"), int_lit(2))],
        body: vec![Stmt::While {
            cond: lt(var("i"), int_lit(2)),
            invariant: Expr::And(vec![le(int_lit(0), var("i")), le(var("i"), int_lit(2))]),
            body: vec![assign("i", add(var("i"), int_lit(1)))],
        }],
        ensures: vec![eq(var("i"), int_lit(2))],
        ranges: vec![("i".to_string(), 0, 2)],
    };
    let vcs = generate(&function).expect("generates");
    assert_eq!(find_counterexample(&vcs[0], 2), None);
}

#[test]
fn bad_ranges_are_rejected() {
    let mut function = bump_bounded(vec![]);
    function.ranges = vec![("x".to_string(), 3, 1)];
    assert_eq!(
        generate(&function),
        Err(WpError::EmptyRange("x".to_string()))
    );

    function.ranges = vec![("y".to_string(), 0, 1)];
    assert_eq!(
        generate(&function),
        Err(WpError::UndeclaredVariable("y".to_string()))
    );

    let mut boolean = bump_bounded(vec![]);
    boolean.vars = vec![("x".to_string(), Sort::Bool)];
    boolean.body = vec![];
    assert_eq!(
        generate(&boolean),
        Err(WpError::NotAnInteger("x".to_string()))
    );
}
