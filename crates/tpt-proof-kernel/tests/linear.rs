#![allow(clippy::result_large_err)]
//! The linear equivalence rule: `a -> b` for constraints with the same linear form.

use tpt_proof_kernel::arith::INT;
use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop, Sort, Term};

fn kernel() -> Kernel {
    let mut kernel = Kernel::new();
    for name in ["x", "y"] {
        kernel
            .declare_function_sorted(name, Vec::new(), Sort::named(INT))
            .expect("declare an integer");
    }
    kernel
}

fn c(n: &str) -> Term {
    Term::constant(n)
}

fn le(a: Term, b: Term) -> Prop {
    Prop::Pred("<=".to_string(), vec![a, b])
}

fn prove(a: Prop, b: Prop) -> Result<tpt_proof_kernel::Theorem, KernelError> {
    let claim = Prop::imp(a.clone(), b.clone());
    kernel().check_proof(&ProofTerm::Linear(a, b), &claim)
}

#[test]
fn a_constraint_and_its_rearrangement_are_equivalent() {
    // x <= -1 + y has difference x + 1 - y; x + (-1) * y <= -1 has x - y + 1.
    let a = le(
        c("x"),
        Term::app("+", vec![Term::app("neg", vec![c("1")]), c("y")]),
    );
    let b = le(
        Term::app(
            "+",
            vec![
                c("x"),
                Term::app("*", vec![Term::app("neg", vec![c("1")]), c("y")]),
            ],
        ),
        Term::app("neg", vec![c("1")]),
    );
    prove(a.clone(), b.clone()).expect("the forms agree");
    prove(b, a).expect("and in the other direction");
}

#[test]
fn different_linear_forms_are_refused() {
    assert!(prove(
        le(c("x"), c("y")),
        le(c("x"), Term::app("+", vec![c("y"), c("1")]))
    )
    .is_err());
}

#[test]
fn a_non_linear_side_is_refused() {
    let product = Term::app("*", vec![c("x"), c("y")]);
    assert!(prove(le(product.clone(), c("0")), le(product, c("0"))).is_err());
}

#[test]
fn a_side_that_is_not_a_comparison_is_refused() {
    assert!(prove(Prop::atom("false"), Prop::atom("false")).is_err());
}

#[test]
fn an_equation_matches_with_either_sign() {
    // x = 1 + y has difference x - 1 - y; 1 + y = x has the negation.
    let a = Prop::Eq(c("x"), Term::app("+", vec![c("1"), c("y")]));
    let b = Prop::Eq(Term::app("+", vec![c("1"), c("y")]), c("x"));
    prove(a.clone(), b.clone()).expect("the same equation, reversed");
    prove(b, a).expect("and back");
}

#[test]
fn an_equation_and_an_inequality_are_not_interchanged() {
    assert!(prove(Prop::Eq(c("x"), c("y")), le(c("x"), c("y"))).is_err());
}

#[test]
fn equations_with_different_forms_are_refused() {
    assert!(prove(Prop::Eq(c("x"), c("y")), Prop::Eq(c("x"), c("x"))).is_err());
}
