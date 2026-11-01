//! Quantification over individuals, predicate symbols, and the scope checks
//! that keep individual variables bound.

use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop, Term};

fn var(name: &str) -> Term {
    Term::var(name)
}

fn constant(name: &str) -> Term {
    Term::constant(name)
}

fn pred(symbol: &str, args: Vec<Term>) -> Prop {
    Prop::Pred(symbol.to_string(), args)
}

fn axiom(name: &str) -> ProofTerm {
    ProofTerm::Axiom(name.to_string())
}

/// Constants `a` and `b`, predicates `P/1` and `R/2`.
fn signature() -> Kernel {
    let mut kernel = Kernel::new();
    kernel.declare_function("a", 0).expect("declare a");
    kernel.declare_function("b", 0).expect("declare b");
    kernel.declare_predicate("P", 1).expect("declare P");
    kernel.declare_predicate("R", 2).expect("declare R");
    kernel
}

#[test]
fn individual_introduction_proves_a_universal() {
    let kernel = signature();
    // all x. x = x
    let term = ProofTerm::IndLam("x".to_string(), Box::new(ProofTerm::Refl(var("x"))));
    let claimed = Prop::forall_ind("x", Prop::Eq(var("x"), var("x")));
    let thm = kernel.check_proof(&term, &claimed).expect("checks");
    assert!(thm.axioms().is_empty());
}

#[test]
fn individual_elimination_instantiates_a_universal_axiom() {
    let mut kernel = signature();
    kernel
        .declare_axiom(
            "all_p",
            Prop::forall_ind("x", pred("P", vec![var("x")])),
            "test axiom",
        )
        .expect("declare");
    let term = ProofTerm::IndApp(Box::new(axiom("all_p")), constant("a"));
    let thm = kernel
        .check_proof(&term, &pred("P", vec![constant("a")]))
        .expect("instantiation checks");
    assert!(thm.axioms().contains("all_p"));
}

#[test]
fn instantiation_avoids_capturing_the_bound_variable() {
    let mut kernel = signature();
    // ax : all x. all y. R(x, y)
    kernel
        .declare_axiom(
            "ax",
            Prop::forall_ind(
                "x",
                Prop::forall_ind("y", pred("R", vec![var("x"), var("y")])),
            ),
            "test axiom",
        )
        .expect("declare");
    // all y. ax[x := y]  must be  all y. all y'. R(y, y'), not all y. R(y, y).
    let term = ProofTerm::IndLam(
        "y".to_string(),
        Box::new(ProofTerm::IndApp(Box::new(axiom("ax")), var("y"))),
    );
    let correct = Prop::forall_ind(
        "y",
        Prop::forall_ind("z", pred("R", vec![var("y"), var("z")])),
    );
    assert!(kernel.check_proof(&term, &correct).is_ok());

    let captured = Prop::forall_ind("y", pred("R", vec![var("y"), var("y")]));
    assert!(matches!(
        kernel.check_proof(&term, &captured),
        Err(KernelError::TypeMismatch { .. })
    ));
}

#[test]
fn generalizing_over_a_hypothesis_that_mentions_the_variable_is_rejected() {
    let kernel = signature();
    // all u. (P(u) -> all u. P(u))  is unsound: the hypothesis P(u) mentions the
    // outer u, so the inner generalization over u depends on it.
    let inner = ProofTerm::IndLam("u".to_string(), Box::new(ProofTerm::Var("h".to_string())));
    let term = ProofTerm::IndLam(
        "u".to_string(),
        Box::new(ProofTerm::Lam(
            "h".to_string(),
            pred("P", vec![var("u")]),
            Box::new(inner),
        )),
    );
    let err = kernel
        .check_proof(
            &term,
            &Prop::forall_ind(
                "u",
                Prop::imp(
                    pred("P", vec![var("u")]),
                    Prop::forall_ind("u", pred("P", vec![var("u")])),
                ),
            ),
        )
        .expect_err("the hypothesis mentions the variable being generalized");
    assert!(matches!(err, KernelError::InvalidGeneralization { .. }));
}

#[test]
fn a_closed_axiom_can_be_generalized_over_any_variable() {
    let mut kernel = signature();
    kernel
        .declare_axiom("pa", pred("P", vec![constant("a")]), "test axiom")
        .expect("declare");
    // The axiom mentions no individual variable, so generalizing is fine.
    let term = ProofTerm::IndLam("x".to_string(), Box::new(axiom("pa")));
    assert!(kernel
        .check_proof(
            &term,
            &Prop::forall_ind("x", pred("P", vec![constant("a")]))
        )
        .is_ok());
}

#[test]
fn unbound_individuals_are_rejected_in_claims_and_terms() {
    let kernel = signature();
    assert_eq!(
        kernel.check_proof(&ProofTerm::Refl(var("x")), &Prop::Eq(var("x"), var("x"))),
        Err(KernelError::UnboundIndividual("x".to_string()))
    );

    let mut with_all = signature();
    with_all
        .declare_axiom(
            "all_p",
            Prop::forall_ind("x", pred("P", vec![var("x")])),
            "test axiom",
        )
        .expect("declare");
    let term = ProofTerm::IndApp(Box::new(axiom("all_p")), var("z"));
    assert_eq!(
        with_all.check_proof(&term, &pred("P", vec![var("z")])),
        Err(KernelError::UnboundIndividual("z".to_string()))
    );
}

#[test]
fn open_axioms_are_rejected() {
    let mut kernel = signature();
    assert_eq!(
        kernel.declare_axiom("open", pred("P", vec![var("x")]), "test axiom"),
        Err(KernelError::UnboundIndividual("x".to_string()))
    );
}

#[test]
fn predicates_must_be_declared_with_the_right_arity() {
    let mut kernel = signature();
    assert_eq!(
        kernel.declare_axiom("q", pred("Q", vec![constant("a")]), "test axiom"),
        Err(KernelError::UnknownPredicate("Q".to_string()))
    );
    assert_eq!(
        kernel.declare_axiom(
            "bad",
            pred("P", vec![constant("a"), constant("b")]),
            "test axiom",
        ),
        Err(KernelError::ArityMismatch {
            symbol: "P".to_string(),
            expected: 1,
            found: 2,
        })
    );
}

#[test]
fn individual_elimination_needs_a_universal() {
    let mut kernel = signature();
    kernel
        .declare_axiom("pa", pred("P", vec![constant("a")]), "test axiom")
        .expect("declare");
    let term = ProofTerm::IndApp(Box::new(axiom("pa")), constant("b"));
    assert!(matches!(
        kernel.check_proof(&term, &pred("P", vec![constant("b")])),
        Err(KernelError::NotForallInd(_))
    ));
}

#[test]
fn predicate_atoms_are_compared_by_symbol_and_arguments() {
    let mut kernel = signature();
    kernel
        .declare_axiom("pa", pred("P", vec![constant("a")]), "test axiom")
        .expect("declare");
    assert!(kernel
        .check_proof(&axiom("pa"), &pred("P", vec![constant("a")]))
        .is_ok());
    assert!(matches!(
        kernel.check_proof(&axiom("pa"), &pred("P", vec![constant("b")])),
        Err(KernelError::TypeMismatch { .. })
    ));
}
