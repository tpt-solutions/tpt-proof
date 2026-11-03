//! User-facing facade for tpt-proof.
//!
//! Import [`prelude`] to get the types for each layer in one place:
//!
//! ```
//! use tpt_proof::prelude::*;
//!
//! const SLOT: Index<8> = Index::new_const(3);
//! let handle = FileHandle::open(7).begin_write().end_write();
//! let _ = (SLOT, handle, Bytes(4096));
//! ```
//!
//! Contracts compile to debug-build checks:
//!
//! ```
//! use tpt_proof::prelude::*;
//!
//! #[requires(divisor != 0)]
//! #[ensures(|result| *result <= 10)]
//! fn quotient(value: u32, divisor: u32) -> u32 {
//!     value / divisor
//! }
//!
//! assert_eq!(quotient(10, 2), 5);
//! ```
//!
//! Layer 3: [`tactics`] builds proofs interactively. Each tactic produces a
//! proof term, and the kernel checks the whole term at [`tactics::Proof::qed`].
//! The `#[theorem]` attribute and the `by { ... }` macro DSL are not built yet.

#![forbid(unsafe_code)]
// Tactic errors carry whole propositions, so the error type is large. They are
// only produced for rejected steps, so boxing them is not worth the API cost.
#![allow(clippy::result_large_err)]

pub mod library;
pub mod report;
pub mod tactics;

/// Everything a typical user needs from each layer.
pub mod prelude {
    pub use crate::tactics::{Goal, Proof, ProofError, Suggestion, TacticError};
    pub use crate::{library, tactics};
    pub use tpt_proof_core::prelude::*;
    pub use tpt_proof_kernel::{Kernel, ProofTerm, Prop, Theorem};
    pub use tpt_proof_macros::{
        ensures, invariant, refined, requires, runtime_check, state_machine,
    };
}
