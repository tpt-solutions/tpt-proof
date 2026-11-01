//! Tactic tests. The kernel is the judge: a tactic can only succeed if the
//! assembled term checks, and an unsound step is caught at `qed`.

use tpt_proof::prelude::*;
use tpt_proof::tactics::{Proof, ProofError, TacticError};

fn atom(name: &str) -> Prop {
    Prop::atom(name)
}

fn kernel_with_axioms() -> Kernel {
    let mut kernel = Kernel::new();
    kernel
        .declare_axiom("ax_a", atom("A"), "test axiom")
        .expect("declare");
    kernel
        .declare_axiom("ax_ab", Prop::imp(atom("A"), atom("B")), "test axiom")
        .expect("declare");
    kernel
}

#[test]
fn identity_by_intro_and_assumption() {
    let kernel = Kernel::new();
    let mut proof = Proof::new(&kernel, Prop::imp(atom("A"), atom("A")));
    proof.intro("x").expect("intro");
    proof.assumption().expect("assumption");
    let thm = proof.qed().expect("kernel accepts the proof");
    assert_eq!(thm.prop(), &Prop::imp(atom("A"), atom("A")));
}

#[test]
fn polymorphic_identity_by_intro_forall() {
    let kernel = Kernel::new();
    let target = Prop::forall("p", Prop::imp(atom("p"), atom("p")));
    let mut proof = Proof::new(&kernel, target.clone());
    proof.intro_forall("q").expect("intro_forall");
    proof.intro("x").expect("intro");
    proof.assumption().expect("assumption");
    let thm = proof.qed().expect("kernel accepts");
    assert_eq!(thm.prop(), &target);
}

#[test]
fn modus_ponens_backwards_through_an_axiom() {
    let kernel = kernel_with_axioms();
    let mut proof = Proof::new(&kernel, atom("B"));
    proof.apply_axiom("ax_ab").expect("apply");
    assert_eq!(proof.goals().len(), 1);
    assert_eq!(proof.goals()[0].target, atom("A"));
    proof
        .exact(tpt_proof_kernel::ProofTerm::Axiom("ax_a".to_string()))
        .expect("exact");
    let thm = proof.qed().expect("kernel accepts");
    assert!(thm.axioms().contains("ax_a"));
    assert!(thm.axioms().contains("ax_ab"));
}

#[test]
fn apply_hypothesis() {
    let kernel = Kernel::new();
    // A -> B, A |- B
    let target = Prop::imp(
        Prop::imp(atom("A"), atom("B")),
        Prop::imp(atom("A"), atom("B")),
    );
    let mut proof = Proof::new(&kernel, target);
    proof.intro("f").expect("intro f");
    proof.intro("a").expect("intro a");
    proof.apply_hyp("f").expect("apply f");
    proof.assumption().expect("assumption");
    assert!(proof.qed().is_ok());
}

#[test]
fn intro_on_a_non_implication_fails() {
    let kernel = Kernel::new();
    let mut proof = Proof::new(&kernel, atom("A"));
    assert_eq!(
        proof.intro("x"),
        Err(TacticError::NotAnImplication(atom("A")))
    );
}

#[test]
fn unknown_names_fail() {
    let kernel = Kernel::new();
    let mut proof = Proof::new(&kernel, atom("A"));
    assert_eq!(
        proof.apply_axiom("nope"),
        Err(TacticError::NoSuchAxiom("nope".to_string()))
    );
    assert_eq!(
        proof.apply_theorem("nope"),
        Err(TacticError::NoSuchTheorem("nope".to_string()))
    );
    assert_eq!(
        proof.apply_hyp("nope"),
        Err(TacticError::NoSuchHypothesis("nope".to_string()))
    );
}

#[test]
fn open_goals_block_qed() {
    let kernel = Kernel::new();
    let mut proof = Proof::new(&kernel, Prop::imp(atom("A"), atom("A")));
    proof.intro("x").expect("intro");
    assert_eq!(proof.qed(), Err(ProofError::OpenGoals(1)));
}

#[test]
fn no_goals_left_to_apply_to() {
    let kernel = Kernel::new();
    let mut proof = Proof::new(&kernel, Prop::imp(atom("A"), atom("A")));
    proof.intro("x").expect("intro");
    proof.assumption().expect("assumption");
    assert_eq!(proof.assumption(), Err(TacticError::NoGoals));
}

#[test]
fn a_wrong_exact_term_is_rejected_by_the_kernel_at_qed() {
    // The tactic accepts any term. Only the kernel decides correctness.
    let kernel = kernel_with_axioms();
    let mut proof = Proof::new(&kernel, atom("B"));
    proof
        .exact(tpt_proof_kernel::ProofTerm::Axiom("ax_a".to_string()))
        .expect("exact accepts any term");
    match proof.qed() {
        Err(ProofError::Kernel(_)) => {}
        other => panic!("expected the kernel to reject, got {other:?}"),
    }
}

#[test]
fn unsound_generalization_is_rejected_by_the_kernel() {
    // Goal: A -> forall p. p, with axiom A in the context. Generalizing over p
    // after introducing a hypothesis that mentions a free atom is fine in
    // general; but here the axiom mentions the bound name A, so the kernel
    // must refuse. The tactic layer does not stop this, by design.
    let mut kernel = Kernel::new();
    kernel
        .declare_axiom("ax_a", atom("A"), "test axiom")
        .expect("declare");
    let mut proof = Proof::new(&kernel, Prop::forall("A", atom("A")));
    proof.intro_forall("A").expect("intro_forall");
    proof
        .exact(tpt_proof_kernel::ProofTerm::Axiom("ax_a".to_string()))
        .expect("exact");
    assert!(matches!(
        proof.qed(),
        Err(ProofError::Kernel(
            tpt_proof_kernel::KernelError::InvalidGeneralization { .. }
        ))
    ));
}

#[test]
fn intro_forall_rejects_a_name_that_would_clash() {
    let kernel = Kernel::new();
    // forall p. p -> q: renaming p to q would capture the free q.
    let target = Prop::forall("p", Prop::imp(atom("p"), atom("q")));
    let mut proof = Proof::new(&kernel, target);
    assert_eq!(
        proof.intro_forall("q"),
        Err(TacticError::NameClash("q".to_string()))
    );
}

#[test]
fn goal_display_shows_hypotheses_and_target() {
    let kernel = Kernel::new();
    let mut proof = Proof::new(&kernel, Prop::imp(atom("A"), atom("B")));
    proof.intro("a").expect("intro");
    let shown = proof.goals()[0].to_string();
    assert_eq!(shown, "a : A\n⊢ B");
}
