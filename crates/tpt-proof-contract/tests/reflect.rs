//! Proof reconstruction: Z3's proofs are checked by the kernel.
//!
//! The fixture tests use a proof captured from Z3 5.3.3, so they run without a
//! solver. The ignored tests call `z3` the same way the solver tests do.

use tpt_proof_contract::reflect::{reconstruct, ReflectError};
use tpt_proof_contract::{verify, Expr, Outcome, SolverConfig, Sort, Vc};

fn var(name: &str) -> Expr {
    Expr::Var(name.to_string())
}

fn int(n: i64) -> Expr {
    Expr::Int(n)
}

fn add(a: Expr, b: Expr) -> Expr {
    Expr::Add(Box::new(a), Box::new(b))
}

fn le(a: Expr, b: Expr) -> Expr {
    Expr::Le(Box::new(a), Box::new(b))
}

/// `0 <= x` and `x <= 10` imply `x + y <= 10 + y`.
fn bounded_sum_vc() -> Vc {
    Vc {
        name: "bounded sum".to_string(),
        vars: vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        assumptions: vec![le(int(0), var("x")), le(var("x"), int(10))],
        goal: le(add(var("x"), var("y")), add(int(10), var("y"))),
    }
}

/// The proof Z3 5.3.3 prints for the script of [`bounded_sum_vc`]: a rewrite of
/// the comparison to `x <= 10`, lifted through `not`, then unit resolution.
const BOUNDED_SUM_PROOF: &str = "unsat
((set-logic ALL)
(proof
(let (($x32 (<= x 10)))
(let (($x42 (not $x32)))
(let ((@x44 (monotonicity (rewrite (= (<= (+ x y) (+ 10 y)) $x32)) (= (not (<= (+ x y) (+ 10 y))) $x42))))
(let ((@x45 (mp (asserted (not (<= (+ x y) (+ 10 y)))) @x44 $x42)))
(let ((@x33 (asserted $x32)))
(unit-resolution @x33 @x45 false))))))))
";

#[test]
fn reconstructs_z3s_proof_of_a_linear_integer_vc() {
    let vc = bounded_sum_vc();
    let theorem = reconstruct(&vc, BOUNDED_SUM_PROOF).expect("the kernel should accept the proof");
    // The proof uses the cancellation axiom for `<=`, in both directions.
    assert!(theorem.axioms().contains("le_cancel_right_fwd"));
    assert!(theorem.axioms().contains("le_cancel_right_bwd"));
}

#[test]
fn an_asserted_formula_that_is_not_an_assumption_is_refused() {
    let tampered = BOUNDED_SUM_PROOF.replace("(asserted $x32)", "(asserted (<= x 9))");
    let vc = bounded_sum_vc();
    assert!(matches!(
        reconstruct(&vc, &tampered),
        Err(ReflectError::Malformed(_))
    ));
}

#[test]
fn a_proof_that_does_not_conclude_false_is_refused() {
    let proof = BOUNDED_SUM_PROOF.replace("(unit-resolution @x33 @x45 false)", "@x33");
    let vc = bounded_sum_vc();
    assert!(matches!(
        reconstruct(&vc, &proof),
        Err(ReflectError::Malformed(_))
    ));
}

#[test]
fn an_unknown_rule_is_reported_not_accepted() {
    let proof =
        BOUNDED_SUM_PROOF.replace("(unit-resolution @x33 @x45 false)", "(th-lemma @x33 false)");
    let vc = bounded_sum_vc();
    match reconstruct(&vc, &proof) {
        Err(ReflectError::Unsupported(what)) => assert!(what.contains("th-lemma")),
        other => panic!("expected an unsupported rule, got {other:?}"),
    }
}

#[test]
fn output_without_a_proof_is_malformed() {
    let vc = bounded_sum_vc();
    assert!(matches!(
        reconstruct(&vc, "sat\n(error \"proof is not available\")"),
        Err(ReflectError::Malformed(_))
    ));
}

#[test]
#[ignore = "requires z3 on PATH"]
fn verify_proves_a_valid_vc_through_the_kernel() {
    let outcome = verify(&bounded_sum_vc(), &SolverConfig::default());
    assert_eq!(outcome, Outcome::Verified, "got {outcome:?}");
}

#[test]
#[ignore = "requires z3 on PATH"]
fn verify_finds_a_counterexample_to_a_false_vc() {
    let vc = Vc {
        name: "false claim".to_string(),
        vars: vec![("x".to_string(), Sort::Int)],
        assumptions: vec![le(int(0), var("x"))],
        goal: le(var("x"), int(5)),
    };
    match verify(&vc, &SolverConfig::default()) {
        Outcome::Failed { counterexample } => assert!(counterexample.contains("x")),
        other => panic!("expected a counterexample, got {other:?}"),
    }
}

#[test]
#[ignore = "requires z3 on PATH"]
fn verify_proves_a_propositional_vc_through_the_kernel() {
    // Assumptions: `p` and `p implies q`. Goal: `q`.
    let p = var("p");
    let vc = Vc {
        name: "modus ponens".to_string(),
        vars: vec![("p".to_string(), Sort::Bool), ("q".to_string(), Sort::Bool)],
        assumptions: vec![p.clone(), Expr::Implies(Box::new(p), Box::new(var("q")))],
        goal: var("q"),
    };
    let outcome = verify(&vc, &SolverConfig::default());
    assert_eq!(outcome, Outcome::Verified, "got {outcome:?}");
}

fn lt(a: Expr, b: Expr) -> Expr {
    Expr::Lt(Box::new(a), Box::new(b))
}

fn eq(a: Expr, b: Expr) -> Expr {
    Expr::Eq(Box::new(a), Box::new(b))
}

#[test]
#[ignore = "requires z3 on PATH"]
fn verify_proves_a_conjunct_through_the_kernel() {
    let vc = Vc {
        name: "conjunction".to_string(),
        vars: vec![("p".to_string(), Sort::Bool), ("q".to_string(), Sort::Bool)],
        assumptions: vec![Expr::And(vec![var("p"), var("q")])],
        goal: var("p"),
    };
    assert_eq!(verify(&vc, &SolverConfig::default()), Outcome::Verified);
}

#[test]
#[ignore = "requires z3 on PATH"]
fn verify_proves_congruence_of_addition_through_the_kernel() {
    let vc = Vc {
        name: "congruence".to_string(),
        vars: vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        assumptions: vec![eq(var("x"), var("y"))],
        goal: eq(add(var("x"), int(1)), add(var("y"), int(1))),
    };
    assert_eq!(verify(&vc, &SolverConfig::default()), Outcome::Verified);
}

#[test]
#[ignore = "requires z3 on PATH"]
fn verify_proves_a_negated_comparison_through_the_kernel() {
    let vc = Vc {
        name: "negated comparison".to_string(),
        vars: vec![("x".to_string(), Sort::Int)],
        assumptions: vec![le(var("x"), int(3))],
        goal: Expr::Not(Box::new(lt(int(3), var("x")))),
    };
    assert_eq!(verify(&vc, &SolverConfig::default()), Outcome::Verified);
}

#[test]
#[ignore = "requires z3 on PATH"]
fn a_vc_that_needs_a_farkas_certificate_is_unchecked_not_verified() {
    // Z3 proves this with a `th-lemma` (Farkas) step, which is not reconstructed
    // yet, so the answer must not be `Verified`.
    let vc = Vc {
        name: "strict to non-strict".to_string(),
        vars: vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        assumptions: vec![lt(var("x"), var("y"))],
        goal: le(add(var("x"), int(1)), var("y")),
    };
    match verify(&vc, &SolverConfig::default()) {
        Outcome::Unchecked { reason } => assert!(reason.contains("unsupported"), "{reason}"),
        other => panic!("expected Unchecked, got {other:?}"),
    }
}

#[test]
#[ignore = "requires z3 on PATH"]
fn a_one_item_conjunction_matches_the_solvers_form() {
    // The translator builds `And([p])`, which the solver prints as `p`.
    let vc = Vc {
        name: "unit conjunction".to_string(),
        vars: vec![("p".to_string(), Sort::Bool)],
        assumptions: vec![Expr::And(vec![var("p")])],
        goal: var("p"),
    };
    assert_eq!(verify(&vc, &SolverConfig::default()), Outcome::Verified);
}
