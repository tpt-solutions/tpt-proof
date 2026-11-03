//! Exports kernel-checked proofs to Lean and, when `lean` is available, asks Lean
//! to check the result.

use std::path::PathBuf;
use std::process::Command;

use tpt_proof_export::{export, ExportError, Lemma};
use tpt_proof_kernel::terms::{ProofTerm, Prop, Sort, Term};
use tpt_proof_kernel::Kernel;

fn atom(name: &str) -> Prop {
    Prop::atom(name)
}

fn eq(a: Term, b: Term) -> Prop {
    Prop::Eq(a, b)
}

fn var(name: &str) -> ProofTerm {
    ProofTerm::Var(name.to_string())
}

/// A kernel with the default sort, a unary `f`, a constant `c` and `d`, and an
/// axiom `c_is_d : c = d`.
fn kernel() -> Kernel {
    let mut kernel = Kernel::new();
    kernel.declare_function("f", 1).expect("declares f");
    kernel.declare_function("c", 0).expect("declares c");
    kernel.declare_function("d", 0).expect("declares d");
    kernel
        .declare_axiom(
            "c_is_d",
            eq(Term::constant("c"), Term::constant("d")),
            "a test axiom",
        )
        .expect("declares axiom");
    kernel
}

/// The lemmas used by most tests. Each one is checked by the kernel first, so
/// the export only ever sees accepted proofs.
fn lemmas(kernel: &mut Kernel) -> Vec<Lemma> {
    let identity = ProofTerm::TyLam(
        "p".to_string(),
        Box::new(ProofTerm::Lam(
            "h".to_string(),
            atom("p"),
            Box::new(var("h")),
        )),
    );
    let identity_prop = Prop::forall("p", Prop::imp(atom("p"), atom("p")));

    let symmetry = ProofTerm::IndLam(
        "x".to_string(),
        Sort::ind(),
        Box::new(ProofTerm::IndLam(
            "y".to_string(),
            Sort::ind(),
            Box::new(ProofTerm::Lam(
                "h".to_string(),
                eq(Term::var("x"), Term::var("y")),
                Box::new(ProofTerm::Sym(Box::new(var("h")))),
            )),
        )),
    );
    let symmetry_prop = Prop::forall_sorted(
        "x",
        Sort::ind(),
        Prop::forall_sorted(
            "y",
            Sort::ind(),
            Prop::imp(
                eq(Term::var("x"), Term::var("y")),
                eq(Term::var("y"), Term::var("x")),
            ),
        ),
    );

    let congruence = ProofTerm::Cong("f".to_string(), vec![ProofTerm::Refl(Term::constant("c"))]);
    let congruence_prop = eq(
        Term::app("f", vec![Term::constant("c")]),
        Term::app("f", vec![Term::constant("c")]),
    );

    let axiom_use = ProofTerm::Axiom("c_is_d".to_string());
    let axiom_prop = eq(Term::constant("c"), Term::constant("d"));

    // Refers to the earlier lemma `identity` through `Const`.
    let uses_identity = ProofTerm::TyApp(
        Box::new(ProofTerm::Const("identity".to_string())),
        atom("q"),
    );
    let uses_identity_prop = Prop::imp(atom("q"), atom("q"));

    // All x y. x = y -> x = c -> y = c, by Leibniz substitution on the motive `x = c`.
    let substitution = ProofTerm::IndLam(
        "x".to_string(),
        Sort::ind(),
        Box::new(ProofTerm::IndLam(
            "y".to_string(),
            Sort::ind(),
            Box::new(ProofTerm::Lam(
                "h".to_string(),
                eq(Term::var("x"), Term::var("y")),
                Box::new(ProofTerm::Lam(
                    "p".to_string(),
                    eq(Term::var("x"), Term::constant("c")),
                    Box::new(ProofTerm::Leibniz(
                        "x".to_string(),
                        eq(Term::var("x"), Term::constant("c")),
                        Box::new(var("h")),
                        Box::new(var("p")),
                    )),
                )),
            )),
        )),
    );
    let substitution_prop = Prop::forall_sorted(
        "x",
        Sort::ind(),
        Prop::forall_sorted(
            "y",
            Sort::ind(),
            Prop::imp(
                eq(Term::var("x"), Term::var("y")),
                Prop::imp(
                    eq(Term::var("x"), Term::constant("c")),
                    eq(Term::var("y"), Term::constant("c")),
                ),
            ),
        ),
    );

    let claims = [
        ("identity", identity, identity_prop),
        ("symmetry", symmetry, symmetry_prop),
        ("congruence", congruence, congruence_prop),
        ("axiom_use", axiom_use, axiom_prop),
        ("uses_identity", uses_identity, uses_identity_prop),
        ("substitution", substitution, substitution_prop),
    ];
    let mut out = Vec::new();
    for (name, proof, prop) in claims {
        kernel
            .declare_theorem(name, &proof, &prop)
            .unwrap_or_else(|err| panic!("kernel rejects `{name}`: {err}"));
        out.push(Lemma {
            name: name.to_string(),
            prop,
            proof,
        });
    }
    out
}

#[test]
fn export_declares_the_environment_and_each_lemma() {
    let mut kernel = kernel();
    let lemmas = lemmas(&mut kernel);
    let text = export(&kernel, &lemmas).expect("exports");
    assert!(text.contains("axiom «sort:Ind» : Type"), "{text}");
    assert!(
        text.contains("axiom «fun:f» : «sort:Ind» → «sort:Ind»"),
        "{text}"
    );
    assert!(text.contains("axiom «fun:c» : «sort:Ind»"), "{text}");
    assert!(
        text.contains("axiom «ax:c_is_d» : («fun:c» = «fun:d»)"),
        "{text}"
    );
    assert!(text.contains("theorem «thm:identity»"), "{text}");
    assert!(
        text.contains("(congr (Eq.refl «fun:f») (Eq.refl «fun:c»))"),
        "{text}"
    );
}

#[test]
fn a_proof_may_refer_only_to_earlier_lemmas() {
    let mut kernel = kernel();
    let mut lemmas = lemmas(&mut kernel);
    lemmas.reverse();
    assert_eq!(
        export(&kernel, &lemmas),
        Err(ExportError::UnknownTheorem("identity".to_string()))
    );
}

#[test]
fn a_proof_may_refer_only_to_declared_axioms() {
    let kernel = Kernel::new();
    let lemma = Lemma {
        name: "bad".to_string(),
        prop: atom("A"),
        proof: ProofTerm::Axiom("missing".to_string()),
    };
    assert_eq!(
        export(&kernel, &[lemma]),
        Err(ExportError::UnknownAxiom("missing".to_string()))
    );
}

#[test]
fn names_that_cannot_be_quoted_are_rejected() {
    let mut kernel = Kernel::new();
    kernel.declare_function("bad»name", 0).expect("declares");
    assert!(matches!(export(&kernel, &[]), Err(ExportError::BadName(_))));
}

/// Writes the export to a temporary file and runs `lean` on it. Lean checks
/// every proof, so a zero exit status is an independent check.
#[test]
#[ignore = "requires lean on PATH"]
fn lean_accepts_the_exported_proofs() {
    let mut kernel = kernel();
    let lemmas = lemmas(&mut kernel);
    let text = export(&kernel, &lemmas).expect("exports");
    let path: PathBuf = std::env::temp_dir().join("tpt_proof_export_test.lean");
    std::fs::write(&path, text).expect("writes the file");
    let output = Command::new("lean").arg(&path).output().expect("runs lean");
    assert!(
        output.status.success(),
        "lean rejected the export:\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn case_analysis_is_refused_rather_than_exported() {
    let mut kernel = Kernel::new();
    kernel
        .declare_inductive(
            "Nat",
            &[("zero", vec![]), ("succ", vec![Sort::named("Nat")])],
        )
        .expect("declare Nat");
    let motive = eq(Term::var("x"), Term::var("x"));
    let proof = ProofTerm::Cases(
        "x".to_string(),
        Sort::named("Nat"),
        motive.clone(),
        vec![
            ProofTerm::Refl(Term::constant("zero")),
            ProofTerm::IndLam(
                "a0".to_string(),
                Sort::named("Nat"),
                Box::new(ProofTerm::Refl(Term::app("succ", vec![Term::var("a0")]))),
            ),
        ],
    );
    let claim = Prop::forall_sorted("x", Sort::named("Nat"), motive);
    kernel
        .declare_theorem("cases_refl", &proof, &claim)
        .expect("kernel accepts the proof");
    let lemma = Lemma {
        name: "cases_refl".to_string(),
        prop: claim,
        proof,
    };
    assert!(matches!(
        export(&kernel, &[lemma]),
        Err(ExportError::UnsupportedRule(_))
    ));
}

#[test]
fn induction_is_refused_rather_than_exported() {
    let kernel = Kernel::new();
    let motive = eq(Term::var("x"), Term::var("x"));
    let lemma = Lemma {
        name: "by_induction".to_string(),
        prop: Prop::forall_sorted("x", Sort::named("Nat"), motive.clone()),
        proof: ProofTerm::Induct("x".to_string(), Sort::named("Nat"), motive, vec![]),
    };
    assert!(matches!(
        export(&kernel, &[lemma]),
        Err(ExportError::UnsupportedRule(_))
    ));
}
