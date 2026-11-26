//! The recipes in `docs/src/cookbook.md` and the tutorial's proof, as tests, so the
//! documented code is known to compile and to prove what it says.

use tpt_proof::library::{self, Lemma};
use tpt_proof::prelude::*;
use tpt_proof::prop;
use tpt_proof::report::dependency_report;
use tpt_proof_export::{export, Lemma as ExportLemma};

#[test]
fn tutorial_proof_closes_by_auto() {
    let a = Prop::atom("A");
    let b = Prop::atom("B");
    let kernel = Kernel::new();
    let target = Prop::imp(
        Prop::imp(a.clone(), b.clone()),
        Prop::imp(a.clone(), Prop::imp(b.clone(), a.clone())),
    );
    assert_eq!(target, prop!("(A -> B) -> A -> (B -> A)"));
    let mut proof = Proof::new(&kernel, target.clone());
    proof.intro("f").unwrap();
    proof.intro("x").unwrap();
    proof.intro("y").unwrap();
    proof.auto().unwrap();
    let theorem = proof.qed().expect("the kernel accepts the proof");
    assert_eq!(theorem.prop(), &target);
}

#[test]
fn cookbook_text_goal_with_auto() {
    let kernel = Kernel::new();
    let mut proof = Proof::new(&kernel, prop!("A -> B -> A"));
    proof.intro("a").unwrap();
    proof.intro("b").unwrap();
    proof.auto().unwrap();
    proof.qed().unwrap();
}

#[test]
fn cookbook_tauto_with_three_hypotheses() {
    let kernel = Kernel::new();
    let mut proof = Proof::new(&kernel, prop!("(A -> B) -> (B -> C) -> A -> C"));
    for name in ["f", "g", "a"] {
        proof.intro(name).unwrap();
    }
    proof.tauto().unwrap();
    proof.qed().unwrap();
}

#[test]
fn cookbook_quantified_goal() {
    let kernel = Kernel::new();
    let mut proof = Proof::new(&kernel, prop!("forall p. p -> p"));
    proof.intro_forall("p").unwrap();
    proof.intro("h").unwrap();
    proof.assumption().unwrap();
    proof.qed().unwrap();
}

#[test]
fn cookbook_axiom_then_theorem_then_library_round_trip() {
    let mut kernel = Kernel::new();
    kernel
        .declare_axiom("ax_a", prop!("A"), "A is taken as given in this example")
        .unwrap();
    let mut proof = Proof::new(&kernel, prop!("A"));
    proof.exact(ProofTerm::Axiom("ax_a".to_string())).unwrap();
    proof.qed().unwrap();
    kernel
        .declare_theorem("a_holds", &ProofTerm::Axiom("ax_a".into()), &prop!("A"))
        .unwrap();

    let report = dependency_report(&kernel).to_string();
    assert!(
        report.contains("a_holds"),
        "the report lists the theorem: {report}"
    );

    let lemmas = vec![Lemma {
        name: "a_holds".into(),
        prop: prop!("A"),
        proof: ProofTerm::Axiom("ax_a".into()),
    }];
    let text = library::save(&kernel, &lemmas).unwrap();
    let (_reloaded, reloaded_lemmas) = library::load_with_lemmas(&text).unwrap();
    assert_eq!(reloaded_lemmas.len(), 1);
    assert_eq!(reloaded_lemmas[0].prop, prop!("A"));

    let lean = export(
        &kernel,
        &[ExportLemma {
            name: "a_holds".into(),
            prop: prop!("A"),
            proof: ProofTerm::Axiom("ax_a".into()),
        }],
    )
    .unwrap();
    assert!(lean.contains("a_holds"));
}

#[test]
fn a_wrong_goal_built_from_text_is_rejected_by_the_kernel() {
    let kernel = Kernel::new();
    let mut proof = Proof::new(&kernel, prop!("A -> B"));
    proof.auto().unwrap();
    assert!(proof.qed().is_err());
}
