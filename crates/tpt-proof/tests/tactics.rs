//! Tactic tests. The kernel is the judge: a tactic can only succeed if the
//! assembled term checks, and an unsound step is caught at `qed`.

use tpt_proof::prelude::*;
use tpt_proof::tactics::{Proof, ProofError, Suggestion, TacticError};
use tpt_proof_kernel::{Sort, Term};

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

#[test]
fn suggestions_offer_intro_for_an_implication() {
    let kernel = Kernel::new();
    let proof = Proof::new(&kernel, Prop::imp(atom("A"), atom("A")));
    assert_eq!(proof.suggestions(), vec![Suggestion::Intro]);
}

#[test]
fn suggestions_offer_assumption_once_a_hypothesis_matches() {
    let kernel = Kernel::new();
    let mut proof = Proof::new(&kernel, Prop::imp(atom("A"), atom("A")));
    proof.intro("h").expect("intro");
    assert_eq!(proof.suggestions(), vec![Suggestion::Assumption]);
}

#[test]
fn suggestions_offer_axioms_and_theorems_that_conclude_the_goal() {
    let mut kernel = kernel_with_axioms();
    kernel
        .declare_theorem(
            "ab_again",
            &ProofTerm::Axiom("ax_ab".to_string()),
            &Prop::imp(atom("A"), atom("B")),
        )
        .expect("declare");
    let proof = Proof::new(&kernel, atom("B"));
    let suggestions = proof.suggestions();
    assert!(
        suggestions.contains(&Suggestion::ApplyAxiom("ax_ab".to_string())),
        "{suggestions:?}"
    );
    assert!(
        suggestions.contains(&Suggestion::ApplyTheorem("ab_again".to_string())),
        "{suggestions:?}"
    );
}

#[test]
fn suggestions_are_empty_once_no_goals_remain() {
    let kernel = Kernel::new();
    let mut proof = Proof::new(&kernel, Prop::imp(atom("A"), atom("A")));
    proof.intro("h").expect("intro");
    proof.assumption().expect("assumption");
    assert!(proof.suggestions().is_empty());
}

#[test]
fn suggestions_display_as_the_tactic_calls() {
    assert_eq!(Suggestion::Intro.to_string(), "intro <name>");
    assert_eq!(
        Suggestion::ApplyAxiom("ax_ab".to_string()).to_string(),
        "apply_axiom ax_ab"
    );
}

fn nat() -> Sort {
    Sort::named("Nat")
}

/// `Nat` with constructors `zero` and `succ : Nat -> Nat`.
fn nat_kernel() -> Kernel {
    let mut kernel = Kernel::new();
    kernel
        .declare_inductive("Nat", &[("zero", vec![]), ("succ", vec![nat()])])
        .expect("declare Nat");
    kernel
}

/// `forall x:Nat. x = x`.
fn reflexive_target() -> Prop {
    Prop::forall_sorted("x", nat(), Prop::Eq(Term::var("x"), Term::var("x")))
}

#[test]
fn case_split_proves_reflexivity_one_constructor_at_a_time() {
    let kernel = nat_kernel();
    let mut proof = Proof::new(&kernel, reflexive_target());
    proof.case_split().expect("case_split");
    assert_eq!(proof.goals().len(), 2);

    proof
        .exact(ProofTerm::Refl(Term::constant("zero")))
        .expect("zero case");
    proof
        .exact(ProofTerm::IndLam(
            "a0".to_string(),
            nat(),
            Box::new(ProofTerm::Refl(Term::app("succ", vec![Term::var("a0")]))),
        ))
        .expect("succ case");
    let thm = proof.qed().expect("kernel accepts the proof");
    assert_eq!(thm.prop(), &reflexive_target());
}

#[test]
fn case_split_is_suggested_for_an_inductive_forall() {
    let kernel = nat_kernel();
    let proof = Proof::new(&kernel, reflexive_target());
    assert!(proof.suggestions().contains(&Suggestion::CaseSplit));
}

#[test]
fn case_split_needs_a_forall_over_individuals() {
    let kernel = nat_kernel();
    let mut proof = Proof::new(&kernel, atom("A"));
    assert_eq!(
        proof.case_split(),
        Err(TacticError::NotAnIndividualForall(atom("A")))
    );
}

#[test]
fn case_split_needs_an_inductive_sort() {
    let kernel = nat_kernel();
    let target = Prop::forall_ind("x", Prop::Eq(Term::var("x"), Term::var("x")));
    let mut proof = Proof::new(&kernel, target);
    assert_eq!(
        proof.case_split(),
        Err(TacticError::NotInductive(Sort::ind()))
    );
}

/// Constants `a` and `b`, predicate `P/1`, `ab : a = b`, and `pb : P(b)`.
fn rewrite_kernel() -> Kernel {
    let mut kernel = Kernel::new();
    kernel.declare_function("a", 0).expect("declare a");
    kernel.declare_function("b", 0).expect("declare b");
    kernel.declare_predicate("P", 1).expect("declare P");
    kernel
        .declare_axiom(
            "ab",
            Prop::Eq(Term::constant("a"), Term::constant("b")),
            "test axiom",
        )
        .expect("declare ab");
    kernel
        .declare_axiom(
            "pb",
            Prop::Pred("P".to_string(), vec![Term::constant("b")]),
            "test axiom",
        )
        .expect("declare pb");
    kernel
}

fn p_of(term: Term) -> Prop {
    Prop::Pred("P".to_string(), vec![term])
}

#[test]
fn rewrite_with_an_axiom_turns_the_goal_into_the_rewritten_one() {
    let kernel = rewrite_kernel();
    let mut proof = Proof::new(&kernel, p_of(Term::constant("a")));
    proof.rewrite_axiom("ab").expect("rewrite");
    assert_eq!(proof.goals()[0].target, p_of(Term::constant("b")));
    proof
        .exact(ProofTerm::Axiom("pb".to_string()))
        .expect("exact");
    let thm = proof.qed().expect("kernel accepts the rewrite");
    assert_eq!(thm.prop(), &p_of(Term::constant("a")));
    assert!(thm.axioms().contains("ab"));
    assert!(thm.axioms().contains("pb"));
}

#[test]
fn rewrite_with_a_hypothesis_after_intro() {
    let kernel = rewrite_kernel();
    let target = Prop::imp(
        Prop::Eq(Term::constant("a"), Term::constant("b")),
        p_of(Term::constant("a")),
    );
    let mut proof = Proof::new(&kernel, target.clone());
    proof.intro("h").expect("intro");
    proof.rewrite_hyp("h").expect("rewrite");
    proof
        .exact(ProofTerm::Axiom("pb".to_string()))
        .expect("exact");
    let thm = proof.qed().expect("kernel accepts");
    assert_eq!(thm.prop(), &target);
}

#[test]
fn rewrite_needs_the_left_hand_side_in_the_goal() {
    let kernel = rewrite_kernel();
    let mut proof = Proof::new(&kernel, p_of(Term::constant("b")));
    assert_eq!(
        proof.rewrite_axiom("ab"),
        Err(TacticError::RewriteTargetNotFound(Term::constant("a")))
    );
}

#[test]
fn rewrite_needs_an_equation() {
    let kernel = rewrite_kernel();
    let mut proof = Proof::new(&kernel, p_of(Term::constant("b")));
    assert_eq!(
        proof.rewrite_axiom("pb"),
        Err(TacticError::NotAnEquation(p_of(Term::constant("b"))))
    );
}

/// `Nat`, `f : Nat -> Nat`, `f(zero) = zero`, and `forall n. f(succ(n)) = f(n)`.
fn induction_kernel() -> Kernel {
    let mut kernel = nat_kernel();
    kernel
        .declare_function_sorted("f", vec![nat()], nat())
        .expect("declare f");
    kernel
        .declare_axiom(
            "f_zero",
            Prop::Eq(
                Term::app("f", vec![Term::constant("zero")]),
                Term::constant("zero"),
            ),
            "test axiom",
        )
        .expect("declare f_zero");
    kernel
        .declare_axiom(
            "f_succ",
            Prop::forall_sorted(
                "n",
                nat(),
                Prop::Eq(
                    Term::app("f", vec![Term::app("succ", vec![Term::var("n")])]),
                    Term::app("f", vec![Term::var("n")]),
                ),
            ),
            "test axiom",
        )
        .expect("declare f_succ");
    kernel
}

/// `forall x:Nat. f(x) = zero`, which needs induction.
fn induction_target() -> Prop {
    Prop::forall_sorted(
        "x",
        nat(),
        Prop::Eq(Term::app("f", vec![Term::var("x")]), Term::constant("zero")),
    )
}

#[test]
fn induct_then_intro_and_exact_proves_a_claim_that_needs_the_hypothesis() {
    let kernel = induction_kernel();
    let mut proof = Proof::new(&kernel, induction_target());
    proof.induct().expect("induct");
    assert_eq!(proof.goals().len(), 2);

    // The zero case.
    proof
        .exact(ProofTerm::Axiom("f_zero".to_string()))
        .expect("zero case");

    // The succ case: introduce the argument and its hypothesis, then conclude.
    proof.intro_individual("a0").expect("intro_individual");
    proof.intro("ih").expect("intro");
    proof
        .exact(ProofTerm::Trans(
            Box::new(ProofTerm::IndApp(
                Box::new(ProofTerm::Axiom("f_succ".to_string())),
                Term::var("a0"),
            )),
            Box::new(ProofTerm::Var("ih".to_string())),
        ))
        .expect("succ case");

    let thm = proof.qed().expect("kernel accepts the induction");
    assert_eq!(thm.prop(), &induction_target());
    assert!(thm.axioms().contains("f_succ"));
}

#[test]
fn induct_is_suggested_alongside_case_split() {
    let kernel = induction_kernel();
    let proof = Proof::new(&kernel, induction_target());
    let suggestions = proof.suggestions();
    assert!(suggestions.contains(&Suggestion::Induct));
    assert!(suggestions.contains(&Suggestion::CaseSplit));
}

#[test]
fn induct_needs_an_inductive_sort() {
    let kernel = induction_kernel();
    let target = Prop::forall_ind("x", Prop::Eq(Term::var("x"), Term::var("x")));
    let mut proof = Proof::new(&kernel, target);
    assert_eq!(proof.induct(), Err(TacticError::NotInductive(Sort::ind())));
}

#[test]
fn intro_individual_needs_a_forall_over_individuals() {
    let kernel = induction_kernel();
    let mut proof = Proof::new(&kernel, atom("A"));
    assert_eq!(
        proof.intro_individual("y"),
        Err(TacticError::NotAnIndividualForall(atom("A")))
    );
}

#[test]
fn intro_individual_refuses_a_name_the_body_already_uses() {
    let kernel = induction_kernel();
    // The body mentions a free `y`, so renaming the bound `x` to `y` would capture it.
    let target = Prop::forall_sorted("x", nat(), Prop::Eq(Term::var("x"), Term::var("y")));
    let mut proof = Proof::new(&kernel, target);
    assert_eq!(
        proof.intro_individual("y"),
        Err(TacticError::NameClash("y".to_string()))
    );
}

#[test]
fn tauto_closes_a_propositional_goal_with_its_hypotheses() {
    // (A -> B) -> (B -> C) -> A -> C, introduced and then closed by tautology.
    let kernel = Kernel::new();
    let target = Prop::imp(
        Prop::imp(atom("A"), atom("B")),
        Prop::imp(
            Prop::imp(atom("B"), atom("C")),
            Prop::imp(atom("A"), atom("C")),
        ),
    );
    let mut proof = Proof::new(&kernel, target.clone());
    proof.intro("f").expect("intro f");
    proof.intro("g").expect("intro g");
    proof.intro("a").expect("intro a");
    proof.tauto().expect("tauto");
    let thm = proof.qed().expect("the kernel accepts the tautology");
    assert_eq!(thm.prop(), &target);
}

#[test]
fn tauto_uses_false_as_a_hypothesis() {
    // With `false` in scope, every atom follows.
    let kernel = Kernel::new();
    let mut proof = Proof::new(&kernel, Prop::imp(atom("false"), atom("C")));
    proof.intro("bottom").expect("intro");
    proof.tauto().expect("tauto");
    assert!(proof.qed().is_ok());
}

#[test]
fn tauto_refuses_a_quantified_goal() {
    let kernel = Kernel::new();
    let mut proof = Proof::new(&kernel, Prop::forall("p", atom("p")));
    assert!(matches!(
        proof.tauto(),
        Err(TacticError::NotPropositional(_))
    ));
}

#[test]
fn tauto_on_a_non_tautology_is_rejected_at_qed() {
    // The tactic applies the tautology rule, which the kernel refuses here.
    let kernel = Kernel::new();
    let mut proof = Proof::new(&kernel, Prop::imp(atom("A"), atom("B")));
    proof.tauto().expect("the tactic itself applies");
    assert!(proof.qed().is_err());
}
