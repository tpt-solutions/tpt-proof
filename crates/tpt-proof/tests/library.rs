//! The lemma library: saving a kernel environment and its lemmas, and loading
//! them into another kernel. Loading is untrusted, so each test that edits the
//! text checks that the kernel still does the rejecting.

use tpt_proof::library::{load, save, Lemma, LibraryError};
use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop, Sort, Term};

fn nat() -> Sort {
    Sort::named("Nat")
}

/// `Nat` with `zero` and `succ`, and constants `a` and `b` with `ab : a = b`.
fn kernel() -> Kernel {
    let mut kernel = Kernel::new();
    kernel
        .declare_inductive("Nat", &[("zero", vec![]), ("succ", vec![nat()])])
        .expect("declare Nat");
    kernel.declare_function("a", 0).expect("declare a");
    kernel.declare_function("b", 0).expect("declare b");
    kernel
        .declare_axiom(
            "ab",
            Prop::Eq(Term::constant("a"), Term::constant("b")),
            "test axiom",
        )
        .expect("declare ab");
    kernel
}

/// `forall x:Nat. x = x`, proved by case analysis.
fn refl_by_cases() -> Lemma {
    let motive = Prop::Eq(Term::var("x"), Term::var("x"));
    Lemma {
        name: "refl_by_cases".to_string(),
        prop: Prop::forall_sorted("x", nat(), motive.clone()),
        proof: ProofTerm::Cases(
            "x".to_string(),
            nat(),
            motive,
            vec![
                ProofTerm::Refl(Term::constant("zero")),
                ProofTerm::IndLam(
                    "a0".to_string(),
                    nat(),
                    Box::new(ProofTerm::Refl(Term::app("succ", vec![Term::var("a0")]))),
                ),
            ],
        ),
    }
}

/// `b = a`, from the axiom `ab` by symmetry. It refers to nothing else.
fn sym_ab() -> Lemma {
    Lemma {
        name: "sym_ab".to_string(),
        prop: Prop::Eq(Term::constant("b"), Term::constant("a")),
        proof: ProofTerm::Sym(Box::new(ProofTerm::Axiom("ab".to_string()))),
    }
}

#[test]
fn a_saved_library_loads_with_the_same_theorems_and_axioms() {
    let kernel = kernel();
    let lemmas = [refl_by_cases(), sym_ab()];
    let text = save(&kernel, &lemmas).expect("saves");

    let loaded = load(&text).expect("loads");
    let refl = loaded.theorem("refl_by_cases").expect("theorem loaded");
    assert_eq!(refl.prop(), &lemmas[0].prop);
    assert!(refl.axioms().is_empty());
    let sym = loaded.theorem("sym_ab").expect("theorem loaded");
    assert!(sym.axioms().contains("ab"));
}

#[test]
fn saving_a_loaded_library_gives_the_same_text() {
    let kernel = kernel();
    let text = save(&kernel, &[refl_by_cases(), sym_ab()]).expect("saves");
    let loaded = load(&text).expect("loads");
    let again = save(&loaded, &[refl_by_cases(), sym_ab()]).expect("saves again");
    assert_eq!(again, text);
}

#[test]
fn a_lemma_can_refer_to_an_earlier_lemma() {
    let kernel = kernel();
    let reexport = Lemma {
        name: "reexport".to_string(),
        prop: refl_by_cases().prop,
        proof: ProofTerm::Const("refl_by_cases".to_string()),
    };
    let text = save(&kernel, &[refl_by_cases(), reexport]).expect("saves");
    let loaded = load(&text).expect("loads");
    assert!(loaded.theorem("reexport").is_some());
}

#[test]
fn a_tampered_lemma_is_rejected_by_the_kernel() {
    // The proof is the axiom `ab : a = b`, but the claim is `B`.
    let text = "(function \"a\" () \"Ind\")\n\
                (function \"b\" () \"Ind\")\n\
                (axiom \"ab\" (eq (fun \"a\") (fun \"b\")) \"test axiom\")\n\
                (lemma \"bad\" (atom \"B\") (axiom \"ab\"))\n";
    match load(text) {
        Err(LibraryError::Kernel { declaration, error }) => {
            assert_eq!(declaration, "lemma \"bad\"");
            assert!(
                matches!(error, KernelError::TypeMismatch { .. }),
                "{error:?}"
            );
        }
        other => panic!("expected a kernel rejection, got {other:?}"),
    }
}

#[test]
fn a_lemma_that_refers_to_a_missing_theorem_is_rejected_on_load() {
    let text = "(lemma \"uses_missing\" (atom \"A\") (const \"missing\"))\n";
    assert!(matches!(
        load(text),
        Err(LibraryError::Kernel {
            error: KernelError::UnknownTheorem(_),
            ..
        })
    ));
}

#[test]
fn save_refuses_a_lemma_whose_reference_is_not_in_the_library() {
    let kernel = kernel();
    let dangling = Lemma {
        name: "dangling".to_string(),
        prop: Prop::atom("A"),
        proof: ProofTerm::Const("missing".to_string()),
    };
    assert!(matches!(
        save(&kernel, &[dangling]),
        Err(LibraryError::Kernel {
            error: KernelError::UnknownTheorem(_),
            ..
        })
    ));
}

#[test]
fn truncated_text_is_a_parse_error() {
    assert!(matches!(
        load("(lemma \"x\" (atom \"A\")"),
        Err(LibraryError::Parse(_))
    ));
    assert!(matches!(
        load("(lemma \"unterminated"),
        Err(LibraryError::Parse(_))
    ));
}

#[test]
fn an_unknown_or_short_form_is_malformed_not_a_panic() {
    assert!(matches!(
        load("(bogus \"x\")"),
        Err(LibraryError::Malformed(_))
    ));
    // A lemma with no proof.
    assert!(matches!(
        load("(lemma \"x\" (atom \"A\"))"),
        Err(LibraryError::Malformed(_))
    ));
    // A term form with no name.
    assert!(matches!(
        load("(lemma \"x\" (eq (fun) (fun \"a\")) (refl (fun)))"),
        Err(LibraryError::Malformed(_))
    ));
}

#[test]
fn quotes_backslashes_and_newlines_in_justifications_survive() {
    let mut kernel = Kernel::new();
    kernel
        .declare_axiom("odd", Prop::atom("A"), "says \"hi\" \\ then\nnew line")
        .expect("declare");
    let text = save(&kernel, &[]).expect("saves");
    let loaded = load(&text).expect("loads");
    assert_eq!(
        loaded.axiom("odd").expect("axiom").justification,
        "says \"hi\" \\ then\nnew line"
    );
}
