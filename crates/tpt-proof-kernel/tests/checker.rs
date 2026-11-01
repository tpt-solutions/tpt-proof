//! Kernel tests through the public API only, the same view an outside auditor has.
//! The bogus-proof cases matter most: the kernel must reject every invalid term.

use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop};

fn var(name: &str) -> ProofTerm {
    ProofTerm::Var(name.to_string())
}

fn axiom(name: &str) -> ProofTerm {
    ProofTerm::Axiom(name.to_string())
}

fn constant(name: &str) -> ProofTerm {
    ProofTerm::Const(name.to_string())
}

fn lam(name: &str, domain: Prop, body: ProofTerm) -> ProofTerm {
    ProofTerm::Lam(name.to_string(), domain, Box::new(body))
}

fn app(function: ProofTerm, argument: ProofTerm) -> ProofTerm {
    ProofTerm::App(Box::new(function), Box::new(argument))
}

fn a() -> Prop {
    Prop::atom("A")
}

fn b() -> Prop {
    Prop::atom("B")
}

/// A kernel with axioms `ax_a : A` and `ax_ab : A -> B`.
fn kernel_with_axioms() -> Kernel {
    let mut kernel = Kernel::new();
    kernel
        .declare_axiom("ax_a", a(), "test axiom")
        .expect("declare ax_a");
    kernel
        .declare_axiom("ax_ab", Prop::imp(a(), b()), "test axiom")
        .expect("declare ax_ab");
    kernel
}

#[test]
fn identity_checks() {
    let kernel = Kernel::new();
    let id = lam("x", a(), var("x"));
    let thm = kernel
        .check_proof(&id, &Prop::imp(a(), a()))
        .expect("identity should check");
    assert_eq!(thm.prop(), &Prop::imp(a(), a()));
    assert!(thm.axioms().is_empty());
}

#[test]
fn k_combinator_checks() {
    let kernel = Kernel::new();
    let k = lam("x", a(), lam("y", b(), var("x")));
    let claimed = Prop::imp(a(), Prop::imp(b(), a()));
    assert!(kernel.check_proof(&k, &claimed).is_ok());
}

#[test]
fn shadowing_uses_innermost_binding() {
    let kernel = Kernel::new();
    // λx:A. λx:B. x  proves  A -> (B -> B), not A -> (B -> A).
    let term = lam("x", a(), lam("x", b(), var("x")));
    assert!(kernel
        .check_proof(&term, &Prop::imp(a(), Prop::imp(b(), b())))
        .is_ok());
    assert!(kernel
        .check_proof(&term, &Prop::imp(a(), Prop::imp(b(), a())))
        .is_err());
}

#[test]
fn wrong_claim_is_rejected() {
    let kernel = Kernel::new();
    let id = lam("x", a(), var("x"));
    let err = kernel
        .check_proof(&id, &Prop::imp(a(), b()))
        .expect_err("identity does not prove A -> B");
    assert!(matches!(err, KernelError::TypeMismatch { .. }));
}

#[test]
fn modus_ponens_records_both_axioms() {
    let kernel = kernel_with_axioms();
    let term = app(axiom("ax_ab"), axiom("ax_a"));
    let thm = kernel.check_proof(&term, &b()).expect("MP should check");
    assert_eq!(thm.prop(), &b());
    let deps: Vec<&str> = thm.axioms().iter().map(String::as_str).collect();
    assert_eq!(deps, ["ax_a", "ax_ab"]);
}

#[test]
fn applying_non_function_is_rejected() {
    let kernel = kernel_with_axioms();
    let term = app(axiom("ax_a"), axiom("ax_a"));
    let err = kernel
        .check_proof(&term, &a())
        .expect_err("A is not a function");
    assert_eq!(err, KernelError::NotAFunction(a()));
}

#[test]
fn wrong_argument_type_is_rejected() {
    let kernel = kernel_with_axioms();
    // ax_ab expects an A, but is given a proof of A -> B.
    let term = app(axiom("ax_ab"), axiom("ax_ab"));
    let err = kernel
        .check_proof(&term, &b())
        .expect_err("argument mismatch");
    assert!(matches!(err, KernelError::TypeMismatch { .. }));
}

#[test]
fn unbound_variable_is_rejected() {
    let kernel = Kernel::new();
    let err = kernel
        .check_proof(&var("y"), &a())
        .expect_err("y is not bound");
    assert_eq!(err, KernelError::UnboundVariable("y".to_string()));
}

#[test]
fn unknown_axiom_is_rejected() {
    let kernel = Kernel::new();
    let err = kernel
        .check_proof(&axiom("missing"), &a())
        .expect_err("no such axiom");
    assert_eq!(err, KernelError::UnknownAxiom("missing".to_string()));
}

#[test]
fn unknown_theorem_is_rejected() {
    let kernel = Kernel::new();
    let err = kernel
        .check_proof(&constant("missing"), &a())
        .expect_err("no such theorem");
    assert_eq!(err, KernelError::UnknownTheorem("missing".to_string()));
}

#[test]
fn assumption_is_tracked_as_dependency() {
    let mut kernel = Kernel::new();
    let assumed = kernel.assume(a()).expect("assume");
    assert_eq!(assumed.prop(), &a());
    assert_eq!(
        assumed.axioms().iter().collect::<Vec<_>>(),
        ["assumption#1"]
    );
}

#[test]
fn declared_theorem_is_reusable_and_carries_its_dependencies() {
    let mut kernel = kernel_with_axioms();
    // t1 : A -> B, from ax_ab alone.
    kernel
        .declare_theorem("t1", &axiom("ax_ab"), &Prop::imp(a(), b()))
        .expect("t1");
    // t2 : B, from t1 applied to ax_a.
    kernel
        .declare_theorem("t2", &app(constant("t1"), axiom("ax_a")), &b())
        .expect("t2");

    let t2 = kernel.theorem("t2").expect("t2 stored");
    let deps: Vec<&str> = t2.axioms().iter().map(String::as_str).collect();
    assert_eq!(deps, ["ax_a", "ax_ab"]);
}

#[test]
fn failed_theorem_is_not_stored() {
    let mut kernel = kernel_with_axioms();
    let err = kernel
        .declare_theorem("bad", &axiom("ax_a"), &b())
        .expect_err("ax_a does not prove B");
    assert!(matches!(err, KernelError::TypeMismatch { .. }));
    assert!(kernel.theorem("bad").is_none());
}

#[test]
fn duplicate_names_are_rejected() {
    let mut kernel = kernel_with_axioms();
    let err = kernel
        .declare_axiom("ax_a", a(), "again")
        .expect_err("duplicate axiom");
    assert_eq!(err, KernelError::DuplicateName("ax_a".to_string()));

    kernel
        .declare_theorem("t", &axiom("ax_a"), &a())
        .expect("t");
    let err = kernel
        .declare_axiom("t", a(), "clashes with theorem")
        .expect_err("name shared with theorem");
    assert_eq!(err, KernelError::DuplicateName("t".to_string()));
}

#[test]
fn axiom_records_its_justification() {
    let kernel = kernel_with_axioms();
    let ax = kernel.axiom("ax_a").expect("ax_a");
    assert_eq!(ax.justification, "test axiom");
    assert_eq!(ax.prop, a());
}
