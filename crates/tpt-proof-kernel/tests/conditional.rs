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

fn taut_imp(a: Prop, b: Prop) -> ProofTerm {
    ProofTerm::Taut(Formula::Imp(
        Box::new(Formula::Atom(a)),
        Box::new(Formula::Atom(b)),
    ))
}

#[test]
fn equivalent_conditions_give_equal_conditionals() {
    // 0 < 1 and 2 < 3 are both true, so the conditionals agree.
    let kernel = Kernel::new();
    let p = lt(c("0"), c("1"));
    let p2 = lt(c("2"), c("3"));
    let rule = ProofTerm::IteCondition(
        Box::new(taut_imp(p.clone(), p2.clone())),
        Box::new(taut_imp(p2.clone(), p.clone())),
        c("4"),
        c("5"),
    );
    let claim = Prop::Eq(
        ite(p.clone(), c("4"), c("5")),
        ite(p2.clone(), c("4"), c("5")),
    );
    kernel
        .check_proof(&rule, &claim)
        .expect("equivalent conditions");
}

#[test]
fn a_backward_proof_that_is_not_the_converse_is_refused() {
    let kernel = Kernel::new();
    let p = lt(c("0"), c("1"));
    let p2 = lt(c("2"), c("3"));
    let rule = ProofTerm::IteCondition(
        Box::new(taut_imp(p.clone(), p2.clone())),
        Box::new(taut_imp(p.clone(), p.clone())),
        c("4"),
        c("5"),
    );
    let claim = Prop::Eq(
        ite(p.clone(), c("4"), c("5")),
        ite(p2.clone(), c("4"), c("5")),
    );
    assert!(matches!(
        kernel.check_proof(&rule, &claim),
        Err(KernelError::IteRejected(_))
    ));
}

#[test]
fn a_false_equivalence_is_refused_by_its_proofs() {
    // 0 < 1 (true) and 1 < 0 (false) are not equivalent: the forward proof fails.
    let kernel = Kernel::new();
    let p = lt(c("0"), c("1"));
    let p2 = lt(c("1"), c("0"));
    let rule = ProofTerm::IteCondition(
        Box::new(taut_imp(p.clone(), p2.clone())),
        Box::new(taut_imp(p2.clone(), p.clone())),
        c("4"),
        c("5"),
    );
    let claim = Prop::Eq(
        ite(p.clone(), c("4"), c("5")),
        ite(p2.clone(), c("4"), c("5")),
    );
    assert!(kernel.check_proof(&rule, &claim).is_err());
}

#[test]
fn the_conditional_laws_apply_to_constant_conditions() {
    use tpt_proof_kernel::axioms::declare_standard;
    let mut kernel = Kernel::new();
    declare_standard(&mut kernel).expect("standard axioms");
    let truth = Prop::imp(Prop::atom("false"), Prop::atom("false"));
    let instance = |axiom: &str, a: &str, b: &str| {
        ProofTerm::IndApp(
            Box::new(ProofTerm::IndApp(
                Box::new(ProofTerm::Axiom(axiom.to_string())),
                c(a),
            )),
            c(b),
        )
    };
    let on_true = Prop::Eq(ite(truth, c("4"), c("5")), c("4"));
    kernel
        .check_proof(&instance("ite_true", "4", "5"), &on_true)
        .expect("the true branch");
    let on_false = Prop::Eq(ite(Prop::atom("false"), c("4"), c("5")), c("5"));
    kernel
        .check_proof(&instance("ite_false", "4", "5"), &on_false)
        .expect("the else branch");
    // The laws do not swap the branches.
    assert!(kernel
        .check_proof(&instance("ite_false", "4", "5"), &on_true)
        .is_err());
}
