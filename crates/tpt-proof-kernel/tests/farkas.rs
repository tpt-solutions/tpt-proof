#![allow(clippy::result_large_err)]
//! The Farkas rule: accepted certificates, and the ways a certificate is refused.

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

fn x() -> Term {
    Term::constant("x")
}

fn y() -> Term {
    Term::constant("y")
}

fn le(a: Term, b: Term) -> Prop {
    Prop::Pred("<=".to_string(), vec![a, b])
}

/// `not (a <= b)`, which over the integers is `b + 1 <= a`.
fn gt(a: Term, b: Term) -> Prop {
    Prop::imp(le(a, b), Prop::atom("false"))
}

fn plus(a: Term, b: Term) -> Term {
    Term::app("+", vec![a, b])
}

fn check(
    premises: Vec<Prop>,
    coefficients: Vec<i128>,
) -> Result<tpt_proof_kernel::Theorem, KernelError> {
    let claim = premises
        .iter()
        .rev()
        .fold(Prop::atom("false"), |acc, p| Prop::imp(p.clone(), acc));
    kernel().check_proof(&ProofTerm::Farkas(premises, coefficients), &claim)
}

#[test]
fn y_at_most_x_and_x_plus_one_at_most_y_is_a_contradiction() {
    // y <= x and x + 1 <= y: summing gives 1 <= 0.
    let thm = check(
        vec![le(y(), x()), le(plus(x(), Term::constant("1")), y())],
        vec![1, 1],
    )
    .expect("the certificate is valid");
    assert!(thm.axioms().is_empty(), "the rule uses no axioms");
}

#[test]
fn two_strict_inequalities_in_opposite_directions_are_a_contradiction() {
    // x < y and y < x, written with `not (<=)`.
    check(vec![gt(y(), x()), gt(x(), y())], vec![1, 1]).expect("valid");
}

#[test]
fn coefficients_scale_the_premises() {
    // 2 * (x <= 0) and 2 * (1 <= x) give 2 <= 0 is false: 2 * x + 2 * (1 - x) = 2.
    check(
        vec![le(x(), Term::constant("0")), le(Term::constant("1"), x())],
        vec![2, 2],
    )
    .expect("valid");
}

#[test]
fn a_consistent_pair_is_refused() {
    // x <= y and y <= x together are consistent: the sum is 0, not a positive constant.
    assert!(check(vec![le(x(), y()), le(y(), x())], vec![1, 1]).is_err());
}

#[test]
fn a_remaining_variable_is_refused() {
    // With coefficient 0 on the second premise, x - y is left over.
    assert!(check(vec![le(x(), y()), le(y(), x())], vec![1, 0]).is_err());
}

#[test]
fn a_negative_coefficient_is_refused() {
    assert!(check(
        vec![le(y(), x()), le(plus(x(), Term::constant("1")), y())],
        vec![1, -1]
    )
    .is_err());
}

#[test]
fn a_ground_false_inequality_is_refused_when_it_is_not_positive() {
    // The premise `1 <= 0` is false, so it refutes itself: its constraint is
    // 1 - 0 = 1 <= 0, a positive constant, and the certificate is accepted.
    check(vec![le(Term::constant("1"), Term::constant("0"))], vec![1]).expect("valid");
    // 0 <= 1 gives -1, which is not a positive constant.
    assert!(check(vec![le(Term::constant("0"), Term::constant("1"))], vec![1]).is_err());
}

#[test]
fn a_non_linear_premise_is_refused() {
    let product = Term::app("*", vec![x(), y()]);
    assert!(check(vec![le(product, Term::constant("0"))], vec![1]).is_err());
}

#[test]
fn a_mismatched_certificate_length_is_refused() {
    assert!(check(vec![le(y(), x())], vec![1, 1]).is_err());
    assert!(check(vec![], vec![]).is_err());
}

#[test]
fn the_claim_must_match_the_premises() {
    let premises = vec![le(y(), x()), le(plus(x(), Term::constant("1")), y())];
    let wrong = Prop::atom("false");
    assert!(kernel()
        .check_proof(&ProofTerm::Farkas(premises, vec![1, 1]), &wrong)
        .is_err());
}

#[test]
fn a_strict_premise_is_a_constraint() {
    // x < y and y <= x: x + 1 <= y and y <= x give 1 <= 0.
    let strict = Prop::Pred("<".to_string(), vec![x(), y()]);
    check(vec![strict.clone(), le(y(), x())], vec![1, 1]).expect("valid");
    // x < y alone is consistent.
    assert!(check(vec![strict], vec![1]).is_err());
}
