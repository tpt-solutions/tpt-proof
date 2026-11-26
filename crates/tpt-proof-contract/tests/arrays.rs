//! Arrays of integers in verification conditions: the solver's theory of arrays,
//! and the readable form of an array in a counterexample. These use z3, and skip
//! with a message when it is not on the PATH.

#[path = "../../../tests-support/tools.rs"]
mod tools;

use tpt_proof_contract::smt::{self, EncodeError};
use tpt_proof_contract::{Expr, Outcome, SolverConfig, Sort, Vc};

fn var(name: &str) -> Expr {
    Expr::Var(name.to_string())
}

fn int(n: i64) -> Expr {
    Expr::Int(n)
}

fn select(array: Expr, index: Expr) -> Expr {
    Expr::Select(Box::new(array), Box::new(index))
}

fn store(array: Expr, index: Expr, value: Expr) -> Expr {
    Expr::Store(Box::new(array), Box::new(index), Box::new(value))
}

fn eq(a: Expr, b: Expr) -> Expr {
    Expr::Eq(Box::new(a), Box::new(b))
}

#[test]
fn a_read_after_a_write_returns_the_written_value() {
    if tools::skip_unless("z3") {
        return;
    }
    let vc = Vc {
        name: "read after write".to_string(),
        vars: vec![
            ("a".to_string(), Sort::IntArray),
            ("i".to_string(), Sort::Int),
            ("v".to_string(), Sort::Int),
        ],
        assumptions: vec![],
        goal: eq(
            select(store(var("a"), var("i"), var("v")), var("i")),
            var("v"),
        ),
    };
    assert!(matches!(
        smt::check(&vc, &SolverConfig::default()),
        Outcome::SolverUnsat
    ));
}

#[test]
fn a_read_of_an_unwritten_array_fails_with_the_array_in_the_model() {
    if tools::skip_unless("z3") {
        return;
    }
    let vc = Vc {
        name: "unconstrained read".to_string(),
        vars: vec![("a".to_string(), Sort::IntArray)],
        assumptions: vec![],
        goal: eq(select(var("a"), int(0)), int(0)),
    };
    match smt::check(&vc, &SolverConfig::default()) {
        Outcome::Failed { counterexample } => {
            assert!(counterexample.contains("a"), "{counterexample}");
            let values = smt::counterexample_values(&counterexample);
            let (_, value) = values
                .iter()
                .find(|(name, _)| name == "a")
                .expect("the array has a value in the model");
            assert!(
                value.starts_with("all ") || value.contains("except"),
                "{value}"
            );
        }
        other => panic!("expected a counterexample, got {other:?}"),
    }
}

#[test]
fn an_index_must_be_an_integer_and_an_array_must_be_an_array() {
    let vc = Vc {
        name: "sorts".to_string(),
        vars: vec![
            ("a".to_string(), Sort::IntArray),
            ("i".to_string(), Sort::Int),
        ],
        assumptions: vec![],
        goal: eq(select(var("i"), int(0)), int(0)),
    };
    assert!(matches!(
        smt::encode(&vc),
        Err(EncodeError::SortMismatch { .. })
    ));
    let vc = Vc {
        goal: eq(select(var("a"), var("a")), int(0)),
        ..vc
    };
    assert!(matches!(
        smt::encode(&vc),
        Err(EncodeError::SortMismatch { .. })
    ));
}

#[test]
fn a_remainder_by_a_positive_divisor_is_in_range_for_the_solver_but_not_yet_for_the_kernel() {
    if tools::skip_unless("z3") {
        return;
    }
    // 0 <= x mod 4 < 4 for every integer x. The solver proves it. The kernel has
    // the Euclidean laws of `mod`, but Z3 reasons about the bound with a rewrite
    // that the reflection does not yet derive, so the answer must not be Verified.
    let mod4 = Expr::Rem(Box::new(var("x")), Box::new(int(4)));
    let vc = Vc {
        name: "remainder range".to_string(),
        vars: vec![("x".to_string(), Sort::Int)],
        assumptions: vec![],
        goal: Expr::And(vec![
            Expr::Le(Box::new(int(0)), Box::new(mod4.clone())),
            Expr::Lt(Box::new(mod4), Box::new(int(4))),
        ]),
    };
    assert!(matches!(
        tpt_proof_contract::check(&vc, &SolverConfig::default()),
        Outcome::SolverUnsat
    ));
    match tpt_proof_contract::verify(&vc, &SolverConfig::default()) {
        Outcome::Unchecked { reason } => assert!(reason.contains("unsupported"), "{reason}"),
        other => panic!("expected Unchecked, got {other:?}"),
    }
}
