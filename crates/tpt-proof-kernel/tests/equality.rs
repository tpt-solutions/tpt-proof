//! Equality over ground terms: reflexivity, symmetry, transitivity, congruence,
//! and the checks on symbols and arities that make them sound.

use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop, Term};

fn constant(name: &str) -> Term {
    Term::constant(name)
}

fn app(symbol: &str, args: Vec<Term>) -> Term {
    Term::app(symbol, args)
}

fn eq(left: Term, right: Term) -> Prop {
    Prop::Eq(left, right)
}

fn axiom(name: &str) -> ProofTerm {
    ProofTerm::Axiom(name.to_string())
}

/// Constants `a`, `b`, `c`, `d`, and unary `f`, binary `g`.
fn signature() -> Kernel {
    let mut kernel = Kernel::new();
    for name in ["a", "b", "c", "d"] {
        kernel.declare_function(name, 0).expect("declare constant");
    }
    kernel.declare_function("f", 1).expect("declare f");
    kernel.declare_function("g", 2).expect("declare g");
    kernel
}

fn with_equalities(mut kernel: Kernel, axioms: &[(&str, Prop)]) -> Kernel {
    for (name, prop) in axioms {
        kernel
            .declare_axiom(name, prop.clone(), "test axiom")
            .expect("declare axiom");
    }
    kernel
}

#[test]
fn reflexivity_proves_t_equals_t() {
    let kernel = signature();
    let term = ProofTerm::Refl(app("f", vec![constant("a")]));
    let thm = kernel
        .check_proof(
            &term,
            &eq(app("f", vec![constant("a")]), app("f", vec![constant("a")])),
        )
        .expect("refl checks");
    assert!(thm.axioms().is_empty());
}

#[test]
fn reflexivity_rejects_a_different_claim() {
    let kernel = signature();
    let term = ProofTerm::Refl(constant("a"));
    assert!(matches!(
        kernel.check_proof(&term, &eq(constant("a"), constant("b"))),
        Err(KernelError::TypeMismatch { .. })
    ));
}

#[test]
fn undeclared_symbols_are_rejected() {
    let kernel = signature();
    assert_eq!(
        kernel.check_proof(
            &ProofTerm::Refl(constant("zzz")),
            &eq(constant("zzz"), constant("zzz"))
        ),
        Err(KernelError::UnknownFunction("zzz".to_string()))
    );
}

#[test]
fn arity_is_checked_in_terms() {
    let kernel = signature();
    // f takes one argument; f() has none.
    let term = ProofTerm::Refl(app("f", vec![]));
    assert_eq!(
        kernel.check_proof(&term, &eq(app("f", vec![]), app("f", vec![]))),
        Err(KernelError::ArityMismatch {
            symbol: "f".to_string(),
            expected: 1,
            found: 0,
        })
    );
}

#[test]
fn symmetry_flips_an_equality() {
    let kernel = with_equalities(signature(), &[("ab", eq(constant("a"), constant("b")))]);
    let term = ProofTerm::Sym(Box::new(axiom("ab")));
    let thm = kernel
        .check_proof(&term, &eq(constant("b"), constant("a")))
        .expect("sym checks");
    assert!(thm.axioms().contains("ab"));
}

#[test]
fn transitivity_chains_two_equalities() {
    let kernel = with_equalities(
        signature(),
        &[
            ("ab", eq(constant("a"), constant("b"))),
            ("bc", eq(constant("b"), constant("c"))),
        ],
    );
    let term = ProofTerm::Trans(Box::new(axiom("ab")), Box::new(axiom("bc")));
    let thm = kernel
        .check_proof(&term, &eq(constant("a"), constant("c")))
        .expect("trans checks");
    let deps: Vec<&str> = thm.axioms().iter().map(String::as_str).collect();
    assert_eq!(deps, ["ab", "bc"]);
}

#[test]
fn transitivity_rejects_mismatched_middles() {
    let kernel = with_equalities(
        signature(),
        &[
            ("ab", eq(constant("a"), constant("b"))),
            ("cd", eq(constant("c"), constant("d"))),
        ],
    );
    let term = ProofTerm::Trans(Box::new(axiom("ab")), Box::new(axiom("cd")));
    let err = kernel
        .check_proof(&term, &eq(constant("a"), constant("d")))
        .expect_err("b and c differ");
    assert!(matches!(err, KernelError::TransitivityMismatch { .. }));
}

#[test]
fn equality_rules_reject_non_equalities() {
    let mut kernel = signature();
    kernel
        .declare_axiom("p", Prop::atom("P"), "test axiom")
        .expect("declare");
    assert_eq!(
        kernel.check_proof(&ProofTerm::Sym(Box::new(axiom("p"))), &Prop::atom("P")),
        Err(KernelError::NotAnEquality(Prop::atom("P")))
    );
    assert_eq!(
        kernel.check_proof(
            &ProofTerm::Trans(
                Box::new(axiom("p")),
                Box::new(ProofTerm::Refl(constant("a")))
            ),
            &eq(constant("a"), constant("a")),
        ),
        Err(KernelError::NotAnEquality(Prop::atom("P")))
    );
}

#[test]
fn congruence_lifts_argument_equalities() {
    let kernel = with_equalities(signature(), &[("ab", eq(constant("a"), constant("b")))]);
    let term = ProofTerm::Cong("f".to_string(), vec![axiom("ab")]);
    let thm = kernel
        .check_proof(
            &term,
            &eq(app("f", vec![constant("a")]), app("f", vec![constant("b")])),
        )
        .expect("cong checks");
    assert!(thm.axioms().contains("ab"));
}

#[test]
fn congruence_over_two_arguments() {
    let kernel = with_equalities(
        signature(),
        &[
            ("ab", eq(constant("a"), constant("b"))),
            ("cd", eq(constant("c"), constant("d"))),
        ],
    );
    let term = ProofTerm::Cong("g".to_string(), vec![axiom("ab"), axiom("cd")]);
    assert!(kernel
        .check_proof(
            &term,
            &eq(
                app("g", vec![constant("a"), constant("c")]),
                app("g", vec![constant("b"), constant("d")]),
            ),
        )
        .is_ok());
}

#[test]
fn congruence_checks_arity_and_argument_kinds() {
    let kernel = with_equalities(signature(), &[("ab", eq(constant("a"), constant("b")))]);
    // g takes two arguments.
    assert!(matches!(
        kernel.check_proof(
            &ProofTerm::Cong("g".to_string(), vec![axiom("ab")]),
            &eq(constant("a"), constant("b")),
        ),
        Err(KernelError::ArityMismatch { .. })
    ));
    // An argument that proves a non-equality is rejected.
    let mut with_atom = kernel;
    with_atom
        .declare_axiom("p", Prop::atom("P"), "test axiom")
        .expect("declare");
    assert!(matches!(
        with_atom.check_proof(
            &ProofTerm::Cong("f".to_string(), vec![axiom("p")]),
            &eq(app("f", vec![constant("a")]), app("f", vec![constant("a")])),
        ),
        Err(KernelError::NotAnEquality(_))
    ));
}

#[test]
fn equalities_survive_type_abstraction_without_prop_variables() {
    // Equality mentions no propositional variable, so generalizing over one is fine.
    let kernel = signature();
    let term = ProofTerm::TyLam("P".to_string(), Box::new(ProofTerm::Refl(constant("a"))));
    assert!(kernel
        .check_proof(&term, &Prop::forall("P", eq(constant("a"), constant("a"))))
        .is_ok());
}

#[test]
fn trans_of_reflexivity_checks_exactly_when_middles_agree() {
    // A small exhaustive check over the constants: Trans(Refl(s), Refl(t))
    // proves s = t precisely when s and t are the same term.
    let kernel = signature();
    let names = ["a", "b", "c"];
    for left in names {
        for middle in names {
            let term = ProofTerm::Trans(
                Box::new(ProofTerm::Refl(constant(left))),
                Box::new(ProofTerm::Refl(constant(middle))),
            );
            let claim = eq(constant(left), constant(middle));
            let accepted = kernel.check_proof(&term, &claim).is_ok();
            assert_eq!(accepted, left == middle, "{left} {middle}");
        }
    }
}
