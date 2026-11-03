//! Structural induction on an inductive sort: `ProofTerm::Induct` and
//! `Kernel::induction_premise`.

use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop, Sort, Term};

fn nat() -> Sort {
    Sort::named("Nat")
}

fn var(name: &str) -> Term {
    Term::var(name)
}

fn succ(term: Term) -> Term {
    Term::app("succ", vec![term])
}

fn f(term: Term) -> Term {
    Term::app("f", vec![term])
}

fn zero() -> Term {
    Term::constant("zero")
}

/// `Nat` with `zero` and `succ`, a function `f : Nat -> Nat`, and the axioms
/// `f(zero) = zero` and `forall n. f(succ(n)) = f(n)`.
fn kernel() -> Kernel {
    let mut kernel = Kernel::new();
    kernel
        .declare_inductive("Nat", &[("zero", vec![]), ("succ", vec![nat()])])
        .expect("declare Nat");
    kernel
        .declare_function_sorted("f", vec![nat()], nat())
        .expect("declare f");
    kernel
        .declare_axiom("f_zero", Prop::Eq(f(zero()), zero()), "test axiom")
        .expect("declare f_zero");
    kernel
        .declare_axiom(
            "f_succ",
            Prop::forall_sorted("n", nat(), Prop::Eq(f(succ(var("n"))), f(var("n")))),
            "test axiom",
        )
        .expect("declare f_succ");
    kernel
}

/// `forall x:Nat. f(x) = zero`, which needs induction: the successor case uses
/// the claim for its argument.
fn claim() -> Prop {
    Prop::forall_sorted("x", nat(), Prop::Eq(f(var("x")), zero()))
}

/// The proof by induction: the `zero` case from `f_zero`, and the `succ` case
/// from `f_succ` and the hypothesis `ih : f(a0) = zero`.
fn induction_proof() -> ProofTerm {
    let motive = Prop::Eq(f(var("x")), zero());
    ProofTerm::Induct(
        "x".to_string(),
        nat(),
        motive,
        vec![
            ProofTerm::Axiom("f_zero".to_string()),
            ProofTerm::IndLam(
                "a0".to_string(),
                nat(),
                Box::new(ProofTerm::Lam(
                    "ih".to_string(),
                    Prop::Eq(f(var("a0")), zero()),
                    Box::new(ProofTerm::Trans(
                        Box::new(ProofTerm::IndApp(
                            Box::new(ProofTerm::Axiom("f_succ".to_string())),
                            var("a0"),
                        )),
                        Box::new(ProofTerm::Var("ih".to_string())),
                    )),
                )),
            ),
        ],
    )
}

#[test]
fn induction_proves_a_claim_that_needs_the_hypothesis() {
    let kernel = kernel();
    let thm = kernel
        .check_proof(&induction_proof(), &claim())
        .expect("induction checks");
    assert!(thm.axioms().contains("f_zero"));
    assert!(thm.axioms().contains("f_succ"));
}

#[test]
fn case_analysis_cannot_prove_the_same_claim() {
    // The same cases under `Cases` get no hypothesis for the successor case, so
    // the successor premise is stronger than the proof, and the kernel rejects it.
    let kernel = kernel();
    let term = ProofTerm::Cases(
        "x".to_string(),
        nat(),
        Prop::Eq(f(var("x")), zero()),
        match induction_proof() {
            ProofTerm::Induct(_, _, _, cases) => cases,
            _ => unreachable!("induction_proof builds Induct"),
        },
    );
    assert!(matches!(
        kernel.check_proof(&term, &claim()),
        Err(KernelError::TypeMismatch { .. })
    ));
}

#[test]
fn the_successor_premise_has_a_hypothesis_for_the_recursive_argument() {
    let kernel = kernel();
    let motive = Prop::Eq(f(var("x")), zero());
    let premise = kernel
        .induction_premise("x", &nat(), &motive, "succ")
        .expect("premise");
    let expected = Prop::forall_sorted(
        "a0",
        nat(),
        Prop::imp(
            Prop::Eq(f(var("a0")), zero()),
            Prop::Eq(f(succ(var("a0"))), zero()),
        ),
    );
    assert!(premise.alpha_eq(&expected), "{premise}");
}

#[test]
fn a_non_recursive_constructor_has_no_hypothesis() {
    let kernel = kernel();
    let motive = Prop::Eq(f(var("x")), zero());
    let premise = kernel
        .induction_premise("x", &nat(), &motive, "zero")
        .expect("premise");
    assert!(premise.alpha_eq(&Prop::Eq(f(zero()), zero())), "{premise}");
}

#[test]
fn the_premise_avoids_capturing_free_individuals_of_the_motive() {
    let kernel = kernel();
    // The motive mentions a free `a0`, so the binder must be renamed, and the
    // hypothesis must use the renamed binder.
    let motive = Prop::Eq(var("x"), var("a0"));
    let premise = kernel
        .induction_premise("x", &nat(), &motive, "succ")
        .expect("premise");
    let expected = Prop::forall_sorted(
        "a0'",
        nat(),
        Prop::imp(
            Prop::Eq(var("a0'"), var("a0")),
            Prop::Eq(succ(var("a0'")), var("a0")),
        ),
    );
    assert!(premise.alpha_eq(&expected), "{premise}");
}

#[test]
fn induction_generalizes_only_when_no_hypothesis_mentions_the_variable() {
    let kernel = kernel();
    // Inside `forall x`, the hypothesis `x = x` refers to that x.
    let term = ProofTerm::IndLam(
        "x".to_string(),
        nat(),
        Box::new(ProofTerm::Lam(
            "h".to_string(),
            Prop::Eq(var("x"), var("x")),
            Box::new(induction_proof()),
        )),
    );
    let claimed = Prop::forall_sorted("x", nat(), Prop::imp(Prop::Eq(var("x"), var("x")), claim()));
    assert!(matches!(
        kernel.check_proof(&term, &claimed),
        Err(KernelError::InvalidGeneralization { .. })
    ));
}

#[test]
fn induction_needs_an_inductive_sort() {
    let kernel = kernel();
    let term = ProofTerm::Induct(
        "x".to_string(),
        Sort::ind(),
        Prop::Eq(var("x"), var("x")),
        vec![],
    );
    assert_eq!(
        kernel.check_proof(&term, &Prop::forall_ind("x", Prop::Eq(var("x"), var("x"))),),
        Err(KernelError::NotInductive(Sort::ind().0))
    );
}

#[test]
fn induction_needs_one_case_per_constructor() {
    let kernel = kernel();
    let term = ProofTerm::Induct(
        "x".to_string(),
        nat(),
        Prop::Eq(f(var("x")), zero()),
        vec![ProofTerm::Axiom("f_zero".to_string())],
    );
    assert_eq!(
        kernel.check_proof(&term, &claim()),
        Err(KernelError::WrongNumberOfCases {
            sort: nat(),
            expected: 2,
            found: 1,
        })
    );
}
