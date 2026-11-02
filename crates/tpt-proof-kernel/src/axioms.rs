//! Trusted axioms.
//!
//! Every axiom is declared with a proposition and a written justification.
//! The kernel tracks which theorems depend on which axioms (see
//! [`crate::Theorem::axioms`]). Adding an axiom to the kernel itself requires
//! a dedicated PR and an entry in `kernel/AUDIT.md`.
//!
//! The kernel ships with no built-in axioms: implication introduction and
//! elimination are primitive rules, not axioms.

use crate::terms::Prop;

/// A declared axiom.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Axiom {
    /// The name the axiom is referred to by.
    pub name: String,
    /// The proposition the axiom asserts.
    pub prop: Prop,
    /// Why the axiom is trusted.
    pub justification: String,
}
