//! Conditional terms (`Term::Ite`): sorts, ground evaluation, and their use in proofs.

use tpt_proof_kernel::arith::INT;
use tpt_proof_kernel::axioms::declare_standard;
use tpt_proof_kernel::formula::Formula;
use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop, Sort, Term};

fn c(n: &str) -> Term {
    Term::constant(n)
}

fn lt(a: Term, b: Term) -> Prop {
    Prop::Pred("<".to_string(), vec![a, b])
}

fn ite(cond: Prop, a: Term, b: Term) -> Term {
    Term::Ite(Box::new(cond), Box::new(a), Box::new(b))
}

#[test]
fn a_ground_conditional_is_evaluated_by_the_tautology_rule() {
    // if 0 < 1 then 2 else 3 = 2, decided by evaluating the condition.
    let kernel = Kernel::new();
    let claim = Prop::Eq(ite(lt(c("0"), c("1")), c("2"), c("3")), c("2"));
    kernel
        .check_proof(&ProofTerm::Taut(Formula::Atom(claim.clone())), &claim)
        .expect("the true branch");
    let wrong = Prop::Eq(ite(lt(c("0"), c("1")), c("2"), c("3")), c("3"));
    assert!(kernel
        .check_proof(&ProofTerm::Taut(Formula::Atom(wrong.clone())), &wrong)
        .is_err());
}

#[test]
fn a_conditional_with_a_free_variable_is_refused_at_top_level() {
    let mut kernel = Kernel::new();
    kernel
        .declare_function_sorted("x", Vec::new(), Sort::named(INT))
        .expect("declare x");
    // The variable `v` is not in scope in the bare term, so the term is refused.
    let term = ite(lt(Term::var("v"), c("1")), Term::constant("x"), c("0"));
    assert!(matches!(
        kernel.check_term(&term),
        Err(KernelError::UnboundIndividual(_))
    ));
}

#[test]
fn branches_of_different_sorts_are_refused() {
    let mut kernel = Kernel::new();
    kernel
        .declare_function_sorted("arr", Vec::new(), Sort::ind())
        .expect("declare an individual");
    let term = ite(lt(c("0"), c("1")), c("0"), c("arr"));
    assert!(matches!(
        kernel.check_term(&term),
        Err(KernelError::SortMismatch { .. })
    ));
}

#[test]
fn a_standard_law_applies_to_a_conditional_term() {
    // Reflexivity of the order at a conditional, through the ordinary axiom.
    let mut kernel = Kernel::new();
    declare_standard(&mut kernel).expect("standard axioms");
    let term = ite(lt(c("0"), c("1")), c("2"), c("3"));
    let claim = Prop::Eq(Term::app("+", vec![term.clone(), c("0")]), term.clone());
    let proof = ProofTerm::IndApp(Box::new(ProofTerm::Axiom("add_zero".to_string())), term);
    kernel
        .check_proof(&proof, &claim)
        .expect("x + 0 = x at a conditional");
}

#[test]
fn a_negative_divisor_is_evaluated_euclidean_as_in_smt_lib() {
    // 7 = (-2) * (-3) + 1, so 7 div (-2) = -3 and 7 mod (-2) = 1.
    let kernel = Kernel::new();
    let quotient = Prop::Eq(
        Term::app("div", vec![c("7"), Term::app("neg", vec![c("2")])]),
        Term::app("neg", vec![c("3")]),
    );
    kernel
        .check_proof(&ProofTerm::Taut(Formula::Atom(quotient.clone())), &quotient)
        .expect("the quotient");
    let remainder = Prop::Eq(
        Term::app("mod", vec![c("7"), Term::app("neg", vec![c("2")])]),
        c("1"),
    );
    kernel
        .check_proof(
            &ProofTerm::Taut(Formula::Atom(remainder.clone())),
            &remainder,
        )
        .expect("the remainder");
}
