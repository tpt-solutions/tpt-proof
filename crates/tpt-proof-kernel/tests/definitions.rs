//! Non-recursive definitions: `Kernel::define_function`.

use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop, Sort, Term};

fn ind() -> Sort {
    Sort::ind()
}

/// Unary `f`, and the individual constant `a`.
fn signature() -> Kernel {
    let mut kernel = Kernel::new();
    kernel.declare_function("f", 1).expect("declare f");
    kernel.declare_function("a", 0).expect("declare a");
    kernel
}

#[test]
fn a_definition_gives_its_defining_equation_as_an_axiom() {
    let mut kernel = signature();
    // g(x) = f(x)
    kernel
        .define_function(
            "g",
            &[("x", ind())],
            &ind(),
            &Term::app("f", vec![Term::var("x")]),
        )
        .expect("define g");

    // forall x. g(x) = f(x), from the definition `g_def` instantiated.
    let proof = ProofTerm::IndLam(
        "x".to_string(),
        ind(),
        Box::new(ProofTerm::IndApp(
            Box::new(ProofTerm::Axiom("g_def".to_string())),
            Term::var("x"),
        )),
    );
    let claim = Prop::forall_ind(
        "x",
        Prop::Eq(
            Term::app("g", vec![Term::var("x")]),
            Term::app("f", vec![Term::var("x")]),
        ),
    );
    let thm = kernel.check_proof(&proof, &claim).expect("checks");
    assert!(thm.axioms().contains("g_def"));
}

#[test]
fn a_definition_can_be_used_in_terms_like_any_symbol() {
    let mut kernel = signature();
    kernel
        .define_function(
            "g",
            &[("x", ind())],
            &ind(),
            &Term::app("f", vec![Term::var("x")]),
        )
        .expect("define g");
    // g(a) = f(a) holds, so g(g(a)) is a well-formed term.
    let term = Term::app("g", vec![Term::app("g", vec![Term::constant("a")])]);
    assert_eq!(kernel.check_term(&term), Ok(ind()));
}

#[test]
fn a_recursive_definition_is_rejected() {
    let mut kernel = signature();
    // The body mentions `g`, which is not declared until the body is checked.
    let body = Term::app("g", vec![Term::var("x")]);
    assert_eq!(
        kernel.define_function("g", &[("x", ind())], &ind(), &body),
        Err(KernelError::UnknownFunction("g".to_string()))
    );
    // Nothing was declared, so the name is still free.
    assert!(kernel.function_signature("g").is_none());
    assert!(kernel.axiom("g_def").is_none());
}

#[test]
fn a_body_of_the_wrong_sort_is_rejected() {
    let mut kernel = signature();
    // Declare a second sort and a function into it.
    kernel.declare_sort("Other").expect("declare sort");
    kernel
        .declare_function_sorted("h", vec![ind()], Sort::named("Other"))
        .expect("declare h");
    assert_eq!(
        kernel.define_function(
            "g",
            &[("x", ind())],
            &ind(),
            &Term::app("h", vec![Term::var("x")]),
        ),
        Err(KernelError::SortMismatch {
            expected: ind(),
            found: Sort::named("Other"),
        })
    );
}

#[test]
fn a_body_may_only_use_its_parameters() {
    let mut kernel = signature();
    assert_eq!(
        kernel.define_function(
            "g",
            &[("x", ind())],
            &ind(),
            &Term::app("f", vec![Term::var("y")]),
        ),
        Err(KernelError::UnboundIndividual("y".to_string()))
    );
}

#[test]
fn a_symbol_cannot_be_defined_twice() {
    let mut kernel = signature();
    assert_eq!(
        kernel.define_function("f", &[("x", ind())], &ind(), &Term::var("x")),
        Err(KernelError::DuplicateName("f".to_string()))
    );
    kernel
        .define_function("g", &[("x", ind())], &ind(), &Term::var("x"))
        .expect("define g");
    assert_eq!(
        kernel.define_function("g", &[("x", ind())], &ind(), &Term::var("x")),
        Err(KernelError::DuplicateName("g_def".to_string()))
    );
}

#[test]
fn a_definition_with_no_parameters_is_a_constant_equation() {
    let mut kernel = signature();
    kernel
        .define_function("c", &[], &ind(), &Term::app("f", vec![Term::constant("a")]))
        .expect("define c");
    let proof = ProofTerm::Axiom("c_def".to_string());
    let claim = Prop::Eq(
        Term::constant("c"),
        Term::app("f", vec![Term::constant("a")]),
    );
    assert!(kernel.check_proof(&proof, &claim).is_ok());
}
