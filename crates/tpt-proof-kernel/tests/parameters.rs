//! Structural recursion with extra parameters: addition on naturals.

// Kernel errors carry whole propositions; see the crate-level allowance in src/lib.rs.
#![allow(clippy::result_large_err)]

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

fn add(left: Term, right: Term) -> Term {
    Term::app("add", vec![left, right])
}

fn nat_kernel() -> Kernel {
    let mut kernel = Kernel::new();
    kernel
        .declare_inductive("Nat", &[("zero", vec![]), ("succ", vec![nat()])])
        .expect("declare Nat");
    kernel.declare_function("a", 0).expect("declare a");
    kernel
}

/// `add(zero, p0) = p0`, `add(succ(a0), p0) = succ(add(a0, p0))`.
fn define_add(kernel: &mut Kernel) -> Result<(), KernelError> {
    kernel.define_by_recursion_with_params(
        "add",
        &nat(),
        &[nat()],
        &nat(),
        &[
            ("zero", Term::var("p0")),
            ("succ", succ(add(Term::var("a0"), Term::var("p0")))),
        ],
    )
}

#[test]
fn addition_computes_by_its_equations() {
    let mut kernel = nat_kernel();
    define_add(&mut kernel).expect("add is structural in its first argument");

    // add(succ(zero), succ(zero)) = succ(succ(zero)).
    // add_succ with a0 := zero, p0 := succ(zero):
    //   add(succ(zero), succ(zero)) = succ(add(zero, succ(zero)))
    // add_zero with p0 := succ(zero): add(zero, succ(zero)) = succ(zero)
    // Congruence under succ gives the result.
    let step = ProofTerm::IndApp(
        Box::new(ProofTerm::IndApp(
            Box::new(ProofTerm::Axiom("add_succ".to_string())),
            succ(zero()),
        )),
        zero(),
    );
    let base = ProofTerm::IndApp(
        Box::new(ProofTerm::Axiom("add_zero".to_string())),
        succ(zero()),
    );
    let term = ProofTerm::Trans(
        Box::new(step),
        Box::new(ProofTerm::Cong("succ".to_string(), vec![base])),
    );
    let claim = Prop::Eq(add(succ(zero()), succ(zero())), succ(succ(zero())));
    let thm = kernel.check_proof(&term, &claim).expect("the sum checks");
    assert!(thm.axioms().contains("add_succ"));
    assert!(thm.axioms().contains("add_zero"));
}

#[test]
fn the_first_argument_must_be_structural() {
    let mut kernel = nat_kernel();
    // The recursive call is on p0, not on a recursive argument.
    assert_eq!(
        kernel.define_by_recursion_with_params(
            "add",
            &nat(),
            &[nat()],
            &nat(),
            &[
                ("zero", Term::var("p0")),
                ("succ", add(Term::var("p0"), Term::var("p0"))),
            ],
        ),
        Err(KernelError::NotStructural("add".to_string()))
    );
}

#[test]
fn a_nested_call_in_an_extra_argument_is_checked_too() {
    let mut kernel = nat_kernel();
    // add(a0, add(succ(a0), p0)): the inner call has no recursive first argument.
    assert_eq!(
        kernel.define_by_recursion_with_params(
            "add",
            &nat(),
            &[nat()],
            &nat(),
            &[
                ("zero", Term::var("p0")),
                (
                    "succ",
                    add(Term::var("a0"), add(succ(Term::var("a0")), Term::var("p0")),),
                ),
            ],
        ),
        Err(KernelError::NotStructural("add".to_string()))
    );
}

#[test]
fn parameters_are_checked_for_scope_and_sort() {
    let mut kernel = nat_kernel();
    // p1 does not exist: only p0 is a parameter.
    assert_eq!(
        kernel.define_by_recursion_with_params(
            "add",
            &nat(),
            &[nat()],
            &nat(),
            &[("zero", Term::var("p1")), ("succ", succ(zero()))],
        ),
        Err(KernelError::UnboundIndividual("p1".to_string()))
    );
    // An extra argument of the wrong sort.
    assert!(matches!(
        kernel.define_by_recursion_with_params(
            "add",
            &nat(),
            &[nat()],
            &nat(),
            &[
                ("zero", Term::var("p0")),
                ("succ", add(Term::var("a0"), Term::constant("a"))),
            ],
        ),
        Err(KernelError::SortMismatch { .. })
    ));
    // An undeclared parameter sort.
    assert_eq!(
        kernel.define_by_recursion_with_params(
            "other",
            &nat(),
            &[Sort::named("Missing")],
            &nat(),
            &[("zero", zero()), ("succ", succ(zero()))],
        ),
        Err(KernelError::UnknownSort("Missing".to_string()))
    );
}

#[test]
fn a_rejected_parameterised_definition_leaves_no_trace() {
    let mut kernel = nat_kernel();
    let _ = kernel.define_by_recursion_with_params(
        "add",
        &nat(),
        &[nat()],
        &nat(),
        &[("zero", Term::var("p0"))],
    );
    define_add(&mut kernel).expect("add can be defined after the failure");
}
