// Kernel errors carry whole propositions; see the crate-level allowance in src/lib.rs.
#![allow(clippy::result_large_err)]

//! Structural recursion over inductive sorts: defining equations, and the checks
//! that keep a definition conservative.

use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop, Sort, Term};

fn nat() -> Sort {
    Sort::named("Nat")
}

fn zero() -> Term {
    Term::constant("zero")
}

fn succ(term: Term) -> Term {
    Term::app("succ", vec![term])
}

fn double_of(term: Term) -> Term {
    Term::app("double", vec![term])
}

fn nat_kernel() -> Kernel {
    let mut kernel = Kernel::new();
    kernel
        .declare_inductive("Nat", &[("zero", vec![]), ("succ", vec![nat()])])
        .expect("declare Nat");
    kernel
}

/// `double(zero) = zero`, `double(succ(a0)) = succ(succ(double(a0)))`.
fn define_double(kernel: &mut Kernel) -> Result<(), KernelError> {
    kernel.define_by_recursion(
        "double",
        &nat(),
        &nat(),
        &[
            ("zero", zero()),
            ("succ", succ(succ(double_of(Term::var("a0"))))),
        ],
    )
}

#[test]
fn defining_equations_are_generated_and_usable() {
    let mut kernel = nat_kernel();
    define_double(&mut kernel).expect("double is structural");

    // double(succ(zero)) = succ(succ(zero)).
    // The step equation at zero: double(succ(zero)) = succ(succ(double(zero))).
    // Then congruence with the base equation double(zero) = zero.
    let step = ProofTerm::IndApp(
        Box::new(ProofTerm::Axiom("double_succ".to_string())),
        zero(),
    );
    let base = ProofTerm::Axiom("double_zero".to_string());
    let inner = ProofTerm::Cong("succ".to_string(), vec![base]);
    let outer = ProofTerm::Cong("succ".to_string(), vec![inner]);
    let term = ProofTerm::Trans(Box::new(step), Box::new(outer));

    let claim = Prop::Eq(double_of(succ(zero())), succ(succ(zero())));
    let thm = kernel
        .check_proof(&term, &claim)
        .expect("the computation checks");
    assert!(thm.axioms().contains("double_zero"));
    assert!(thm.axioms().contains("double_succ"));
}

#[test]
fn a_wrong_computed_value_is_rejected() {
    let mut kernel = nat_kernel();
    define_double(&mut kernel).expect("double is structural");
    let term = ProofTerm::Axiom("double_zero".to_string());
    // double(zero) is zero, not succ(zero).
    assert!(matches!(
        kernel.check_proof(&term, &Prop::Eq(double_of(zero()), succ(zero()))),
        Err(KernelError::TypeMismatch { .. })
    ));
}

#[test]
fn every_constructor_needs_a_case() {
    let mut kernel = nat_kernel();
    assert_eq!(
        kernel.define_by_recursion("double", &nat(), &nat(), &[("zero", zero())]),
        Err(KernelError::MissingCase("succ".to_string()))
    );
}

#[test]
fn cases_must_name_constructors_of_the_sort_once() {
    let mut kernel = nat_kernel();
    assert_eq!(
        kernel.define_by_recursion(
            "double",
            &nat(),
            &nat(),
            &[("zero", zero()), ("pred", zero())],
        ),
        Err(KernelError::UnknownConstructor("pred".to_string()))
    );
    assert_eq!(
        kernel.define_by_recursion(
            "double",
            &nat(),
            &nat(),
            &[("zero", zero()), ("zero", zero()), ("succ", zero())],
        ),
        Err(KernelError::DuplicateName("zero".to_string()))
    );
}

#[test]
fn recursive_calls_must_be_on_recursive_arguments() {
    let mut kernel = nat_kernel();
    // Calling double(succ(a0)) would not be structural.
    assert_eq!(
        kernel.define_by_recursion(
            "double",
            &nat(),
            &nat(),
            &[("zero", zero()), ("succ", double_of(succ(Term::var("a0")))),],
        ),
        Err(KernelError::NotStructural("double".to_string()))
    );
}

#[test]
fn a_call_on_a_non_recursive_argument_is_rejected() {
    let mut kernel = Kernel::new();
    kernel
        .declare_inductive("Opt", &[("none", vec![]), ("some", vec![Sort::ind()])])
        .expect("declare Opt");
    kernel.declare_function("a", 0).expect("declare a");
    // some(a0) with a0 of sort Ind. Any argument of sort Opt would be recursive,
    // so a call on a non-recursive argument is caught by the sort check.
    assert_eq!(
        kernel.define_by_recursion(
            "unwrap",
            &Sort::named("Opt"),
            &Sort::ind(),
            &[
                ("none", Term::constant("a")),
                ("some", Term::app("unwrap", vec![Term::var("a0")])),
            ],
        ),
        Err(KernelError::SortMismatch {
            expected: Sort::named("Opt"),
            found: Sort::ind(),
        })
    );
}

#[test]
fn case_bodies_must_have_the_result_sort() {
    let mut kernel = nat_kernel();
    kernel.declare_function("a", 0).expect("declare a");
    // The body `a` is of sort Ind, but double returns Nat.
    assert!(matches!(
        kernel.define_by_recursion(
            "double",
            &nat(),
            &nat(),
            &[
                ("zero", Term::constant("a")),
                ("succ", succ(double_of(Term::var("a0")))),
            ],
        ),
        Err(KernelError::SortMismatch { .. })
    ));
}

#[test]
fn a_rejected_definition_leaves_no_trace() {
    let mut kernel = nat_kernel();
    let _ = kernel.define_by_recursion("double", &nat(), &nat(), &[("zero", zero())]);
    // The failed attempt did not declare double, so it can be declared now.
    define_double(&mut kernel).expect("double can be defined after a failure");
}

#[test]
fn a_definition_cannot_be_redeclared() {
    let mut kernel = nat_kernel();
    define_double(&mut kernel).expect("first definition");
    assert_eq!(
        define_double(&mut kernel),
        Err(KernelError::DuplicateName("double".to_string()))
    );
}

#[test]
fn an_equation_name_clash_rolls_back_the_definition() {
    let mut kernel = nat_kernel();
    kernel
        .declare_axiom("double_zero", Prop::Eq(zero(), zero()), "test")
        .expect("declare");
    assert_eq!(
        define_double(&mut kernel),
        Err(KernelError::DuplicateName("double_zero".to_string()))
    );
    // Rolled back: the symbol is free again, and a fresh name works.
    kernel
        .declare_function("double", 1)
        .expect("symbol was rolled back");
}
