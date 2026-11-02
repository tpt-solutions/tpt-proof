//! Leibniz substitution: from `t = s` and a proof of `P[x := t]`, derive `P[x := s]`.

use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop, Term};

fn constant(name: &str) -> Term {
    Term::constant(name)
}

fn axiom(name: &str) -> ProofTerm {
    ProofTerm::Axiom(name.to_string())
}

fn eq(left: Term, right: Term) -> Prop {
    Prop::Eq(left, right)
}

/// Constants `a` and `b`, and unary predicate `P`.
fn signature() -> Kernel {
    let mut kernel = Kernel::new();
    kernel.declare_function("a", 0).expect("declare a");
    kernel.declare_function("b", 0).expect("declare b");
    kernel.declare_predicate("P", 1).expect("declare P");
    kernel
}

/// The motive `P(x)`.
fn p_of_x() -> Prop {
    Prop::Pred("P".to_string(), vec![Term::var("x")])
}

#[test]
fn leibniz_moves_a_property_along_an_equation() {
    let mut kernel = signature();
    kernel
        .declare_axiom("ab", eq(constant("a"), constant("b")), "test axiom")
        .expect("declare ab");
    kernel
        .declare_axiom(
            "pa",
            Prop::Pred("P".to_string(), vec![constant("a")]),
            "test axiom",
        )
        .expect("declare pa");

    let term = ProofTerm::Leibniz(
        "x".to_string(),
        p_of_x(),
        Box::new(axiom("ab")),
        Box::new(axiom("pa")),
    );
    let claim = Prop::Pred("P".to_string(), vec![constant("b")]);
    let thm = kernel.check_proof(&term, &claim).expect("leibniz checks");
    assert!(thm.axioms().contains("ab"));
    assert!(thm.axioms().contains("pa"));
}

#[test]
fn leibniz_runs_in_both_directions_with_symmetry() {
    let mut kernel = signature();
    kernel
        .declare_axiom("ab", eq(constant("a"), constant("b")), "test axiom")
        .expect("declare ab");
    kernel
        .declare_axiom(
            "pb",
            Prop::Pred("P".to_string(), vec![constant("b")]),
            "test axiom",
        )
        .expect("declare pb");

    // From b = a (by symmetry) and P(b), derive P(a).
    let term = ProofTerm::Leibniz(
        "x".to_string(),
        p_of_x(),
        Box::new(ProofTerm::Sym(Box::new(axiom("ab")))),
        Box::new(axiom("pb")),
    );
    let claim = Prop::Pred("P".to_string(), vec![constant("a")]);
    assert!(kernel.check_proof(&term, &claim).is_ok());
}

#[test]
fn leibniz_rejects_a_proof_of_the_wrong_instance() {
    let mut kernel = signature();
    kernel
        .declare_axiom("ab", eq(constant("a"), constant("b")), "test axiom")
        .expect("declare ab");
    // The proof is of P(b), but the equation a = b needs P(a).
    kernel
        .declare_axiom(
            "pb",
            Prop::Pred("P".to_string(), vec![constant("b")]),
            "test axiom",
        )
        .expect("declare pb");

    let term = ProofTerm::Leibniz(
        "x".to_string(),
        p_of_x(),
        Box::new(axiom("ab")),
        Box::new(axiom("pb")),
    );
    let claim = Prop::Pred("P".to_string(), vec![constant("b")]);
    assert!(matches!(
        kernel.check_proof(&term, &claim),
        Err(KernelError::TypeMismatch { .. })
    ));
}

#[test]
fn leibniz_rejects_a_claim_that_is_not_the_substituted_motive() {
    let mut kernel = signature();
    kernel
        .declare_axiom("ab", eq(constant("a"), constant("b")), "test axiom")
        .expect("declare ab");
    kernel
        .declare_axiom(
            "pa",
            Prop::Pred("P".to_string(), vec![constant("a")]),
            "test axiom",
        )
        .expect("declare pa");

    // The rule proves P(b), so claiming P(a) is wrong.
    let term = ProofTerm::Leibniz(
        "x".to_string(),
        p_of_x(),
        Box::new(axiom("ab")),
        Box::new(axiom("pa")),
    );
    let claim = Prop::Pred("P".to_string(), vec![constant("a")]);
    assert!(kernel.check_proof(&term, &claim).is_err());
}

#[test]
fn leibniz_requires_an_equation() {
    let mut kernel = signature();
    kernel
        .declare_axiom("pa", Prop::atom("Q"), "test axiom")
        .expect("declare pa");
    let term = ProofTerm::Leibniz(
        "x".to_string(),
        p_of_x(),
        Box::new(axiom("pa")),
        Box::new(axiom("pa")),
    );
    assert!(matches!(
        kernel.check_proof(&term, &Prop::atom("Q")),
        Err(KernelError::NotAnEquality(_))
    ));
}
