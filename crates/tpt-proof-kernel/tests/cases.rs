//! Case analysis on an inductive sort: `ProofTerm::Cases`.

use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop, Sort, Term};

fn nat() -> Sort {
    Sort::named("Nat")
}

/// `Nat` with constructors `zero` and `succ : Nat -> Nat`.
fn signature() -> Kernel {
    let mut kernel = Kernel::new();
    kernel
        .declare_inductive("Nat", &[("zero", vec![]), ("succ", vec![nat()])])
        .expect("declare Nat");
    kernel
}

/// `forall x:Nat. x = x`, the claim that case analysis proves below.
fn reflexive_claim() -> Prop {
    Prop::forall_sorted("x", nat(), Prop::Eq(Term::var("x"), Term::var("x")))
}

/// The proof of `forall x:Nat. x = x` by cases: `Refl(zero)`, and
/// `forall a0. Refl(succ(a0))` for `succ`.
fn reflexive_cases() -> ProofTerm {
    ProofTerm::Cases(
        "x".to_string(),
        nat(),
        Prop::Eq(Term::var("x"), Term::var("x")),
        vec![
            ProofTerm::Refl(Term::constant("zero")),
            ProofTerm::IndLam(
                "a0".to_string(),
                nat(),
                Box::new(ProofTerm::Refl(Term::app("succ", vec![Term::var("a0")]))),
            ),
        ],
    )
}

#[test]
fn cases_proves_a_property_for_every_constructor() {
    let kernel = signature();
    let thm = kernel
        .check_proof(&reflexive_cases(), &reflexive_claim())
        .expect("cases checks");
    assert!(thm.axioms().is_empty());
}

#[test]
fn cases_needs_one_case_per_constructor() {
    let kernel = signature();
    let term = ProofTerm::Cases(
        "x".to_string(),
        nat(),
        Prop::Eq(Term::var("x"), Term::var("x")),
        vec![ProofTerm::Refl(Term::constant("zero"))],
    );
    assert_eq!(
        kernel.check_proof(&term, &reflexive_claim()),
        Err(KernelError::WrongNumberOfCases {
            sort: nat(),
            expected: 2,
            found: 1,
        })
    );
}

#[test]
fn cases_rejects_a_case_that_proves_the_wrong_premise() {
    let kernel = signature();
    // The `succ` case proves `zero = zero` instead of `succ(a0) = succ(a0)`.
    let term = ProofTerm::Cases(
        "x".to_string(),
        nat(),
        Prop::Eq(Term::var("x"), Term::var("x")),
        vec![
            ProofTerm::Refl(Term::constant("zero")),
            ProofTerm::IndLam(
                "a0".to_string(),
                nat(),
                Box::new(ProofTerm::Refl(Term::constant("zero"))),
            ),
        ],
    );
    assert!(matches!(
        kernel.check_proof(&term, &reflexive_claim()),
        Err(KernelError::TypeMismatch { .. })
    ));
}

#[test]
fn cases_rejects_a_claim_that_is_not_the_motive_generalized() {
    let kernel = signature();
    // Claims `forall x. x = zero`, which the cases do not prove.
    let claim = Prop::forall_sorted("x", nat(), Prop::Eq(Term::var("x"), Term::constant("zero")));
    assert!(kernel.check_proof(&reflexive_cases(), &claim).is_err());
}

#[test]
fn cases_requires_an_inductive_sort() {
    let kernel = signature();
    let term = ProofTerm::Cases(
        "x".to_string(),
        Sort::ind(),
        Prop::Eq(Term::var("x"), Term::var("x")),
        vec![],
    );
    assert_eq!(
        kernel.check_proof(
            &term,
            &Prop::forall_ind("x", Prop::Eq(Term::var("x"), Term::var("x")))
        ),
        Err(KernelError::NotInductive(Sort::ind().0))
    );
}

#[test]
fn cases_cannot_generalize_over_a_variable_a_hypothesis_mentions() {
    let kernel = signature();
    // Inside `all x`, the hypothesis `x = x` refers to that x. Splitting on the
    // inner x would generalize over a variable the hypothesis fixes.
    let term = ProofTerm::IndLam(
        "x".to_string(),
        nat(),
        Box::new(ProofTerm::Lam(
            "h".to_string(),
            Prop::Eq(Term::var("x"), Term::var("x")),
            Box::new(reflexive_cases()),
        )),
    );
    assert!(matches!(
        kernel.check_proof(
            &term,
            &Prop::forall_sorted(
                "x",
                nat(),
                Prop::imp(Prop::Eq(Term::var("x"), Term::var("x")), reflexive_claim(),),
            ),
        ),
        Err(KernelError::InvalidGeneralization { .. })
    ));
}

#[test]
fn case_premise_avoids_capturing_free_individuals_of_the_motive() {
    let kernel = signature();
    // The motive mentions a free individual `a0`. The premise for `succ` must
    // not reuse that name for its binder, or the substitution would capture it.
    let motive = Prop::Eq(Term::var("x"), Term::var("a0"));
    let premise = kernel
        .case_premise("x", &nat(), &motive, "succ")
        .expect("premise");
    let expected = Prop::forall_sorted(
        "a0'",
        nat(),
        Prop::Eq(Term::app("succ", vec![Term::var("a0'")]), Term::var("a0")),
    );
    assert!(premise.alpha_eq(&expected), "{premise}");
}
