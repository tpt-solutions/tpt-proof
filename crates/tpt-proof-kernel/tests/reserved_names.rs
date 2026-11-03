//! Reserved names: `false` and `#r` cannot be bound, and built-in names cannot
//! be declared.
//!
//! `false` is evaluated as the constant false by the tautology rule, and the
//! encodings of `and` and `or` bind `#r`. If a generalization could bind either
//! name, the rule would reason about a letter that the kernel treats as a
//! constant, which proves any proposition.

use tpt_proof_kernel::formula::Formula;
use tpt_proof_kernel::terms::{ProofTerm, Prop, Sort};
use tpt_proof_kernel::{Kernel, KernelError};

/// `forall false. (false -> q)`, built by generalizing a tautology over the
/// name `false`. The tautology rule accepts `false -> q` because it reads
/// `false` as the constant false, so the binder would be vacuous to the rule.
fn generalized_over_false() -> ProofTerm {
    let body = ProofTerm::Taut(Formula::Imp(
        Box::new(Formula::Const(false)),
        Box::new(Formula::Atom(Prop::atom("q"))),
    ));
    ProofTerm::TyLam("false".to_string(), Box::new(body))
}

#[test]
fn generalizing_over_false_is_rejected() {
    let kernel = Kernel::new();
    let result = kernel.check_proof(
        &generalized_over_false(),
        &Prop::forall("false", Prop::imp(Prop::atom("false"), Prop::atom("q"))),
    );
    assert!(
        matches!(result, Err(KernelError::ReservedSymbol(ref name)) if name == "false"),
        "expected `false` to be rejected as a binder, got {result:?}"
    );
}

#[test]
fn the_exploit_cannot_prove_an_arbitrary_proposition() {
    // Instantiating `forall false. (false -> q)` at `false -> false` gives
    // `(false -> false) -> q`; applying it to a proof of `false -> false`
    // yields `q`. With `q` a free letter, that must not be accepted.
    let kernel = Kernel::new();
    let true_proof = ProofTerm::Taut(Formula::Const(true));
    let true_prop = Prop::imp(Prop::atom("false"), Prop::atom("false"));
    let instance = ProofTerm::TyApp(Box::new(generalized_over_false()), true_prop);
    let term = ProofTerm::App(Box::new(instance), Box::new(true_proof));
    let result = kernel.check_proof(&term, &Prop::atom("q"));
    assert!(
        result.is_err(),
        "the kernel proved `q` from nothing: {result:?}"
    );
}

#[test]
fn generalizing_over_the_encoding_binder_is_rejected() {
    // `#r` is bound by the encodings of `and` and `or`. A user generalization
    // over it could capture an encoded formula's atom.
    let kernel = Kernel::new();
    let body = ProofTerm::Taut(Formula::Imp(
        Box::new(Formula::Atom(Prop::atom("#r"))),
        Box::new(Formula::Atom(Prop::atom("#r"))),
    ));
    let term = ProofTerm::TyLam("#r".to_string(), Box::new(body));
    let claimed = Prop::forall("#r", Prop::imp(Prop::atom("#r"), Prop::atom("#r")));
    let result = kernel.check_proof(&term, &claimed);
    assert!(
        matches!(result, Err(KernelError::ReservedSymbol(_))),
        "expected `#r` to be rejected as a binder, got {result:?}"
    );
}

#[test]
fn individual_binders_cannot_be_reserved_names() {
    let kernel = Kernel::new();
    let body = ProofTerm::Taut(Formula::Const(true));
    let term = ProofTerm::IndLam("false".to_string(), Sort::ind(), Box::new(body));
    let result = kernel.check_proof(
        &term,
        &Prop::forall_sorted(
            "false",
            Sort::ind(),
            Prop::imp(Prop::atom("false"), Prop::atom("false")),
        ),
    );
    assert!(
        matches!(result, Err(KernelError::ReservedSymbol(_))),
        "expected `false` to be rejected as an individual binder, got {result:?}"
    );
}

#[test]
fn taut_atoms_cannot_mention_the_encoding_binder() {
    // A formula atom `#r` would be captured by the `forall #r` that encodes
    // `and`, so the encoded proposition would not say what the formula says.
    let kernel = Kernel::new();
    let formula = Formula::And(vec![Formula::Atom(Prop::atom("#r"))]);
    let result = kernel.check_proof(&ProofTerm::Taut(formula.clone()), &formula.encode());
    assert!(
        matches!(result, Err(KernelError::ReservedSymbol(_))),
        "expected the atom `#r` to be rejected in a tautology, got {result:?}"
    );
}

#[test]
fn false_cannot_be_declared_as_a_function() {
    let mut kernel = Kernel::new();
    let result = kernel.declare_function("false", 0);
    assert!(
        matches!(result, Err(KernelError::ReservedSymbol(_))),
        "got {result:?}"
    );
}

#[test]
fn numerals_cannot_be_declared_as_constructors() {
    let mut kernel = Kernel::new();
    let result = kernel.declare_inductive("T", &[("0", vec![])]);
    assert!(
        matches!(result, Err(KernelError::ReservedSymbol(_))),
        "got {result:?}"
    );
}

#[test]
fn an_axiom_cannot_bind_false() {
    // The same exploit, with the binder introduced by an axiom instead of a
    // proof. Declaring the axiom must fail, so no theorem can use it.
    let mut kernel = Kernel::new();
    let axiom = Prop::forall("false", Prop::imp(Prop::atom("false"), Prop::atom("q")));
    let result = kernel.declare_axiom("bad", axiom, "test");
    assert!(
        matches!(result, Err(KernelError::ReservedSymbol(ref name)) if name == "false"),
        "expected the axiom to be rejected, got {result:?}"
    );
}
