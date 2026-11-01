//! Tests for propositional quantification: introduction, elimination, capture
//! avoidance, alpha-equivalence, and the generalization side condition.

use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop};

fn var(name: &str) -> ProofTerm {
    ProofTerm::Var(name.to_string())
}

fn axiom(name: &str) -> ProofTerm {
    ProofTerm::Axiom(name.to_string())
}

fn lam(name: &str, domain: Prop, body: ProofTerm) -> ProofTerm {
    ProofTerm::Lam(name.to_string(), domain, Box::new(body))
}

fn ty_lam(name: &str, body: ProofTerm) -> ProofTerm {
    ProofTerm::TyLam(name.to_string(), Box::new(body))
}

fn ty_app(function: ProofTerm, argument: Prop) -> ProofTerm {
    ProofTerm::TyApp(Box::new(function), argument)
}

fn atom(name: &str) -> Prop {
    Prop::atom(name)
}

/// `forall p. p -> p`, proved by `Λp. λx:p. x`.
fn poly_identity() -> ProofTerm {
    ty_lam("p", lam("x", atom("p"), var("x")))
}

/// `forall p. forall q. p -> q -> p`, proved by `Λp. Λq. λx:p. λy:q. x`.
fn poly_k() -> ProofTerm {
    ty_lam(
        "p",
        ty_lam("q", lam("x", atom("p"), lam("y", atom("q"), var("x")))),
    )
}

#[test]
fn polymorphic_identity_checks() {
    let kernel = Kernel::new();
    let claimed = Prop::forall("p", Prop::imp(atom("p"), atom("p")));
    let thm = kernel
        .check_proof(&poly_identity(), &claimed)
        .expect("forall p. p -> p should check");
    assert!(thm.axioms().is_empty());
}

#[test]
fn quantified_claims_match_up_to_renaming() {
    let kernel = Kernel::new();
    // The binder name in the claim does not matter.
    let claimed = Prop::forall("zzz", Prop::imp(atom("zzz"), atom("zzz")));
    assert!(kernel.check_proof(&poly_identity(), &claimed).is_ok());
}

#[test]
fn instantiation_substitutes() {
    let kernel = Kernel::new();
    let term = ty_app(poly_identity(), atom("B"));
    let thm = kernel
        .check_proof(&term, &Prop::imp(atom("B"), atom("B")))
        .expect("instantiating at B should give B -> B");
    assert_eq!(thm.prop(), &Prop::imp(atom("B"), atom("B")));
}

#[test]
fn instantiation_at_a_quantified_proposition() {
    let kernel = Kernel::new();
    // Instantiate the identity at (forall q. q): gives (forall q. q) -> (forall q. q).
    let inner = Prop::forall("q", atom("q"));
    let term = ty_app(poly_identity(), inner.clone());
    let claimed = Prop::imp(inner.clone(), inner);
    assert!(kernel.check_proof(&term, &claimed).is_ok());
}

#[test]
fn instantiation_avoids_capture() {
    let kernel = Kernel::new();
    // K : forall p. forall q. p -> q -> p.
    // Instantiating p := q (the free q) must not capture it. The result is
    // forall q'. q -> q' -> q, which is not forall q. q -> q -> q.
    let term = ty_app(poly_k(), atom("q"));
    let correct = Prop::forall("r", Prop::imp(atom("q"), Prop::imp(atom("r"), atom("q"))));
    assert!(kernel.check_proof(&term, &correct).is_ok());

    let captured = Prop::forall("q", Prop::imp(atom("q"), Prop::imp(atom("q"), atom("q"))));
    let err = kernel
        .check_proof(&term, &captured)
        .expect_err("a captured free variable must not be accepted");
    assert!(matches!(err, KernelError::TypeMismatch { .. }));
}

#[test]
fn instantiating_a_non_quantified_term_is_rejected() {
    let mut kernel = Kernel::new();
    kernel
        .declare_axiom("ax_a", atom("A"), "test axiom")
        .expect("declare");
    let err = kernel
        .check_proof(&ty_app(axiom("ax_a"), atom("B")), &atom("B"))
        .expect_err("A is not quantified");
    assert_eq!(err, KernelError::NotAForall(atom("A")));
}

#[test]
fn generalizing_over_a_hypothesis_is_rejected() {
    let kernel = Kernel::new();
    // Inside λx:A, the hypothesis x : A mentions A, so ΛA cannot generalize over A.
    // (ΛA. λx:A. x is fine: there the hypothesis is bound inside the lambda.)
    let term = lam("x", atom("A"), ty_lam("A", var("x")));
    let err = kernel
        .check_proof(&term, &Prop::imp(atom("A"), Prop::forall("A", atom("A"))))
        .expect_err("hypothesis mentions the bound variable");
    assert!(matches!(err, KernelError::InvalidGeneralization { .. }));
}

#[test]
fn generalizing_over_an_axiom_that_mentions_the_variable_is_rejected() {
    let mut kernel = Kernel::new();
    kernel
        .declare_axiom("ax_a", atom("A"), "test axiom")
        .expect("declare");
    // Without the side condition this would prove forall A. A from the axiom A.
    let term = ty_lam("A", axiom("ax_a"));
    let err = kernel
        .check_proof(&term, &Prop::forall("A", atom("A")))
        .expect_err("the axiom mentions the bound variable");
    assert!(matches!(err, KernelError::InvalidGeneralization { .. }));
}

#[test]
fn generalizing_over_an_unrelated_axiom_is_allowed() {
    let mut kernel = Kernel::new();
    kernel
        .declare_axiom("ax_b", atom("B"), "test axiom")
        .expect("declare");
    let term = ty_lam("A", axiom("ax_b"));
    let thm = kernel
        .check_proof(&term, &Prop::forall("A", atom("B")))
        .expect("the axiom does not mention A");
    assert!(thm.axioms().contains("ax_b"));
}

#[test]
fn assumption_mentioning_the_variable_blocks_generalization() {
    let mut kernel = Kernel::new();
    let assumed = kernel.assume(atom("A")).expect("assume");
    assert!(assumed.axioms().contains("assumption#1"));
    kernel
        .declare_axiom("ax_a", atom("A"), "test axiom")
        .expect("declare");
    let term = ty_lam("A", axiom("assumption#1"));
    assert!(kernel
        .check_proof(&term, &Prop::forall("A", atom("A")))
        .is_err());
}
