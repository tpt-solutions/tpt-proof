//! Propositions and the proof term language.
//!
//! The logic is simply typed: propositions are built from atoms and implication
//! only (Curry-Howard: a proof of `p` is a term of type `p`). Universal
//! quantification, inductive types, and pattern matching from SPEC.md §4 are
//! not implemented yet; see `kernel/AUDIT.md`.

use std::fmt;

/// A proposition. Implication is the only connective for now.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Prop {
    /// A named, uninterpreted proposition such as `A`.
    Atom(String),
    /// Implication `A -> B`.
    Imp(Box<Prop>, Box<Prop>),
}

impl Prop {
    /// Builds an atomic proposition.
    pub fn atom(name: &str) -> Prop {
        Prop::Atom(name.to_string())
    }

    /// Builds the implication `a -> b`.
    pub fn imp(a: Prop, b: Prop) -> Prop {
        Prop::Imp(Box::new(a), Box::new(b))
    }
}

impl fmt::Display for Prop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Prop::Atom(name) => write!(f, "{name}"),
            Prop::Imp(a, b) => write!(f, "({a} -> {b})"),
        }
    }
}

/// A proof term. The variants follow SPEC.md §4, minus those not yet implemented.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofTerm {
    /// A variable bound by an enclosing [`ProofTerm::Lam`].
    Var(String),
    /// A previously checked theorem, by name.
    Const(String),
    /// A declared axiom, by name. Its use is recorded as a dependency.
    Axiom(String),
    /// Implication introduction: `λ name : prop. body`.
    Lam(String, Prop, Box<ProofTerm>),
    /// Implication elimination (modus ponens): `function argument`.
    App(Box<ProofTerm>, Box<ProofTerm>),
}
