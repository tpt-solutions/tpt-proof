//! Multiple sorts, inductive types, and induction axioms.

use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop, Sort, Term};

fn nat() -> Sort {
    Sort::named("Nat")
}

fn var(name: &str) -> Term {
    Term::var(name)
}

fn constant(name: &str) -> Term {
    Term::constant(name)
}

fn axiom(name: &str) -> ProofTerm {
    ProofTerm::Axiom(name.to_string())
}

fn pred(symbol: &str, args: Vec<Term>) -> Prop {
    Prop::Pred(symbol.to_string(), args)
}

/// Naturals `zero` and `succ`, a default-sort constant `a`, and a predicate `P`
/// over `Nat`.
fn nat_kernel() -> Kernel {
    let mut kernel = Kernel::new();
    kernel
        .declare_inductive("Nat", &[("zero", vec![]), ("succ", vec![nat()])])
        .expect("declare Nat");
    kernel.declare_function("a", 0).expect("declare a");
    kernel
        .declare_predicate_sorted("P", vec![nat()])
        .expect("declare P");
    kernel
}

fn zero() -> Term {
    constant("zero")
}

fn succ(term: Term) -> Term {
    Term::app("succ", vec![term])
}

#[test]
fn inductive_constructors_have_the_new_sort() {
    let kernel = nat_kernel();
    assert_eq!(kernel.check_term(&zero()), Ok(nat()));
    assert_eq!(kernel.check_term(&succ(zero())), Ok(nat()));
}

#[test]
fn a_term_of_the_wrong_sort_is_rejected() {
    let kernel = nat_kernel();
    // succ expects a Nat, but a is of the default sort Ind.
    assert_eq!(
        kernel.check_term(&succ(constant("a"))),
        Err(KernelError::SortMismatch {
            expected: nat(),
            found: Sort::ind(),
        })
    );
}

#[test]
fn equality_across_sorts_is_rejected() {
    let kernel = nat_kernel();
    let claim = Prop::Eq(zero(), constant("a"));
    assert!(matches!(
        kernel.check_proof(&ProofTerm::Refl(zero()), &claim),
        Err(KernelError::SortMismatch { .. })
    ));
}

#[test]
fn predicate_arguments_must_have_the_declared_sort() {
    let mut kernel = nat_kernel();
    assert_eq!(
        kernel.declare_axiom("bad", pred("P", vec![constant("a")]), "test"),
        Err(KernelError::SortMismatch {
            expected: nat(),
            found: Sort::ind(),
        })
    );
}

#[test]
fn quantifier_over_a_sort_only_takes_values_of_that_sort() {
    let mut kernel = nat_kernel();
    kernel
        .declare_axiom(
            "all_p",
            Prop::forall_sorted("n", nat(), pred("P", vec![var("n")])),
            "test",
        )
        .expect("declare");
    let wrong = ProofTerm::IndApp(Box::new(axiom("all_p")), constant("a"));
    assert_eq!(
        kernel.check_proof(&wrong, &pred("P", vec![constant("a")])),
        Err(KernelError::SortMismatch {
            expected: nat(),
            found: Sort::ind(),
        })
    );
    let right = ProofTerm::IndApp(Box::new(axiom("all_p")), zero());
    assert!(kernel.check_proof(&right, &pred("P", vec![zero()])).is_ok());
}

#[test]
fn introduction_over_a_sort() {
    let kernel = nat_kernel();
    let term = ProofTerm::IndLam("n".to_string(), nat(), Box::new(ProofTerm::Refl(var("n"))));
    assert!(kernel
        .check_proof(
            &term,
            &Prop::forall_sorted("n", nat(), Prop::Eq(var("n"), var("n"))),
        )
        .is_ok());
}

#[test]
fn quantifiers_over_different_sorts_are_different_propositions() {
    let kernel = nat_kernel();
    let term = ProofTerm::IndLam("x".to_string(), nat(), Box::new(ProofTerm::Refl(var("x"))));
    // forall x:Nat. x = x is not forall x:Ind. x = x.
    assert!(matches!(
        kernel.check_proof(&term, &Prop::forall_ind("x", Prop::Eq(var("x"), var("x"))),),
        Err(KernelError::TypeMismatch { .. })
    ));
}

#[test]
fn congruence_over_a_sorted_function() {
    let mut kernel = nat_kernel();
    // ab : zero = succ(zero) is an equality of Nats, so it lifts through succ.
    kernel
        .declare_axiom("ab", Prop::Eq(zero(), succ(zero())), "test")
        .expect("declare");
    let term = ProofTerm::Cong("succ".to_string(), vec![axiom("ab")]);
    assert!(kernel
        .check_proof(&term, &Prop::Eq(succ(zero()), succ(succ(zero()))),)
        .is_ok());
}

#[test]
fn inductive_declarations_are_checked() {
    let mut kernel = Kernel::new();
    assert_eq!(
        kernel.declare_inductive("Empty", &[]),
        Err(KernelError::NoConstructors("Empty".to_string()))
    );
    assert_eq!(
        kernel.declare_inductive("Bad", &[("mk", vec![Sort::named("Missing")])]),
        Err(KernelError::UnknownSort("Missing".to_string()))
    );
    assert_eq!(
        kernel.declare_inductive("Dup", &[("c", vec![]), ("c", vec![])]),
        Err(KernelError::DuplicateName("c".to_string()))
    );
}

#[test]
fn induction_proves_a_property_of_every_natural() {
    let mut kernel = nat_kernel();
    kernel
        .declare_induction("nat_ind", &nat(), "P")
        .expect("declare induction");
    // Base case: P(zero).
    kernel
        .declare_axiom("p_zero", pred("P", vec![zero()]), "test")
        .expect("declare");
    // Step: forall n:Nat. P(n) -> P(succ(n)).
    kernel
        .declare_axiom(
            "p_step",
            Prop::forall_sorted(
                "n",
                nat(),
                Prop::imp(pred("P", vec![var("n")]), pred("P", vec![succ(var("n"))])),
            ),
            "test",
        )
        .expect("declare");

    let term = ProofTerm::App(
        Box::new(ProofTerm::App(
            Box::new(axiom("nat_ind")),
            Box::new(axiom("p_zero")),
        )),
        Box::new(axiom("p_step")),
    );
    let claim = Prop::forall_sorted("n", nat(), pred("P", vec![var("n")]));
    let thm = kernel.check_proof(&term, &claim).expect("induction checks");
    for dep in ["nat_ind", "p_zero", "p_step"] {
        assert!(thm.axioms().contains(dep), "missing dependency {dep}");
    }
}

#[test]
fn induction_needs_every_case() {
    let mut kernel = nat_kernel();
    kernel
        .declare_induction("nat_ind", &nat(), "P")
        .expect("declare induction");
    kernel
        .declare_axiom("p_zero", pred("P", vec![zero()]), "test")
        .expect("declare");
    // Only the base case: the result still wants the step, so it is not a
    // proof of forall n. P(n).
    let term = ProofTerm::App(Box::new(axiom("nat_ind")), Box::new(axiom("p_zero")));
    let claim = Prop::forall_sorted("n", nat(), pred("P", vec![var("n")]));
    assert!(matches!(
        kernel.check_proof(&term, &claim),
        Err(KernelError::TypeMismatch { .. })
    ));
}

#[test]
fn induction_over_a_tree_with_two_recursive_arguments() {
    let mut kernel = Kernel::new();
    let tree = Sort::named("Tree");
    kernel
        .declare_inductive(
            "Tree",
            &[("leaf", vec![]), ("node", vec![tree.clone(), tree.clone()])],
        )
        .expect("declare Tree");
    kernel
        .declare_predicate_sorted("Q", vec![tree.clone()])
        .expect("declare Q");
    kernel
        .declare_induction("tree_ind", &tree, "Q")
        .expect("declare induction");
    kernel
        .declare_axiom("q_leaf", pred("Q", vec![constant("leaf")]), "test")
        .expect("declare");
    // forall l:Tree. forall r:Tree. Q(l) -> Q(r) -> Q(node(l, r))
    kernel
        .declare_axiom(
            "q_node",
            Prop::forall_sorted(
                "l",
                tree.clone(),
                Prop::forall_sorted(
                    "r",
                    tree.clone(),
                    Prop::imp(
                        pred("Q", vec![var("l")]),
                        Prop::imp(
                            pred("Q", vec![var("r")]),
                            pred("Q", vec![Term::app("node", vec![var("l"), var("r")])]),
                        ),
                    ),
                ),
            ),
            "test",
        )
        .expect("declare");

    let term = ProofTerm::App(
        Box::new(ProofTerm::App(
            Box::new(axiom("tree_ind")),
            Box::new(axiom("q_leaf")),
        )),
        Box::new(axiom("q_node")),
    );
    let claim = Prop::forall_sorted("t", tree, pred("Q", vec![var("t")]));
    assert!(kernel.check_proof(&term, &claim).is_ok());
}

#[test]
fn induction_rejects_a_predicate_over_another_sort() {
    let mut kernel = nat_kernel();
    kernel.declare_predicate("Untyped", 1).expect("declare");
    assert!(matches!(
        kernel.declare_induction("bad", &nat(), "Untyped"),
        Err(KernelError::SortMismatch { .. })
    ));
}

#[test]
fn induction_is_only_for_inductive_sorts() {
    let mut kernel = nat_kernel();
    assert_eq!(
        kernel.declare_induction("bad", &Sort::ind(), "P"),
        Err(KernelError::NotInductive("Ind".to_string()))
    );
}
