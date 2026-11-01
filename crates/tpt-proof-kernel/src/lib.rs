//! The trusted proof kernel for tpt-proof.
//!
//! This crate is the only trusted component of the framework (SPEC.md §4, §7).
//! It has no external dependencies and forbids `unsafe` code. The only way to
//! obtain a [`Theorem`] is through [`Kernel::check_proof`], so every theorem
//! value has been checked by this crate.

#![forbid(unsafe_code)]

pub mod axioms;
mod checker;
pub mod terms;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub use axioms::Axiom;
pub use terms::{ProofTerm, Prop};

/// Errors the kernel reports. A rejected proof is never accepted in part.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelError {
    /// A `Var` refers to a name not bound in the local context.
    UnboundVariable(String),
    /// An `Axiom` refers to a name that was never declared.
    UnknownAxiom(String),
    /// A `Const` refers to a name that is not a checked theorem.
    UnknownTheorem(String),
    /// Application of a term whose type is not an implication.
    NotAFunction(Prop),
    /// A term has a different proposition than the one required.
    TypeMismatch {
        /// The proposition that was required.
        expected: Prop,
        /// The proposition the term actually proves.
        found: Prop,
    },
    /// A name is already used by an axiom or theorem.
    DuplicateName(String),
}

impl fmt::Display for KernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KernelError::UnboundVariable(name) => write!(f, "unbound variable `{name}`"),
            KernelError::UnknownAxiom(name) => write!(f, "unknown axiom `{name}`"),
            KernelError::UnknownTheorem(name) => write!(f, "unknown theorem `{name}`"),
            KernelError::NotAFunction(prop) => write!(f, "applied a non-function of type {prop}"),
            KernelError::TypeMismatch { expected, found } => {
                write!(f, "expected a proof of {expected}, found {found}")
            }
            KernelError::DuplicateName(name) => write!(f, "name `{name}` is already declared"),
        }
    }
}

impl std::error::Error for KernelError {}

/// Result type used throughout the kernel.
pub type Result<T> = std::result::Result<T, KernelError>;

/// A proposition proved by the kernel, together with the axioms it depends on.
///
/// The fields are private and the constructor is crate-private, so a `Theorem`
/// can only come from a successful check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Theorem {
    prop: Prop,
    axioms: BTreeSet<String>,
}

impl Theorem {
    pub(crate) fn new(prop: Prop, axioms: BTreeSet<String>) -> Self {
        Theorem { prop, axioms }
    }

    /// The proposition this theorem establishes.
    pub fn prop(&self) -> &Prop {
        &self.prop
    }

    /// Names of every axiom (including assumptions) this theorem depends on.
    pub fn axioms(&self) -> &BTreeSet<String> {
        &self.axioms
    }
}

/// The kernel environment: declared axioms and checked theorems.
#[derive(Debug, Default)]
pub struct Kernel {
    axioms: BTreeMap<String, Axiom>,
    theorems: BTreeMap<String, Theorem>,
    assumptions: usize,
}

impl Kernel {
    /// Creates an empty kernel with no axioms and no theorems.
    pub fn new() -> Self {
        Self::default()
    }

    /// Declares a trusted axiom. This expands the TCB, so every axiom must
    /// carry a justification, which is recorded with it.
    pub fn declare_axiom(&mut self, name: &str, prop: Prop, justification: &str) -> Result<()> {
        self.ensure_fresh(name)?;
        let axiom = Axiom {
            name: name.to_string(),
            prop,
            justification: justification.to_string(),
        };
        self.axioms.insert(name.to_string(), axiom);
        Ok(())
    }

    /// Introduces an assumption for an interactive proof. It is tracked like an
    /// axiom: every theorem that uses it lists it in [`Theorem::axioms`].
    pub fn assume(&mut self, prop: Prop) -> Result<Theorem> {
        self.assumptions += 1;
        let name = format!("assumption#{}", self.assumptions);
        let axiom = Axiom {
            name: name.clone(),
            prop: prop.clone(),
            justification: "assumed explicitly in an interactive proof".to_string(),
        };
        self.axioms.insert(name.clone(), axiom);
        Ok(Theorem::new(prop, BTreeSet::from([name])))
    }

    /// Checks `term` against `claimed`. Returns a [`Theorem`] only if the proof
    /// is valid.
    pub fn check_proof(&self, term: &ProofTerm, claimed: &Prop) -> Result<Theorem> {
        let mut ctx = Vec::new();
        let mut deps = BTreeSet::new();
        let found = checker::infer(self, &mut ctx, term, &mut deps)?;
        if found != *claimed {
            return Err(KernelError::TypeMismatch {
                expected: claimed.clone(),
                found,
            });
        }
        Ok(Theorem::new(claimed.clone(), deps))
    }

    /// Checks `term` against `claimed` and stores the result under `name`, so
    /// later proofs can refer to it with [`ProofTerm::Const`].
    pub fn declare_theorem(&mut self, name: &str, term: &ProofTerm, claimed: &Prop) -> Result<()> {
        self.ensure_fresh(name)?;
        let theorem = self.check_proof(term, claimed)?;
        self.theorems.insert(name.to_string(), theorem);
        Ok(())
    }

    /// Looks up a declared axiom.
    pub fn axiom(&self, name: &str) -> Option<&Axiom> {
        self.axioms.get(name)
    }

    /// Looks up a checked theorem.
    pub fn theorem(&self, name: &str) -> Option<&Theorem> {
        self.theorems.get(name)
    }

    fn ensure_fresh(&self, name: &str) -> Result<()> {
        if self.axioms.contains_key(name) || self.theorems.contains_key(name) {
            Err(KernelError::DuplicateName(name.to_string()))
        } else {
            Ok(())
        }
    }
}
