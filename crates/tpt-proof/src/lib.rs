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
//! Layer 3 (the proof DSL and tactics) is not built yet. It needs the proc-macro
//! crate and the tactic framework from SPEC.md §6.

#![forbid(unsafe_code)]

/// Everything a typical user needs from each layer.
pub mod prelude {
    pub use tpt_proof_core::prelude::*;
    pub use tpt_proof_kernel::{Kernel, ProofTerm, Prop, Theorem};
    pub use tpt_proof_runtime::runtime_check;
}
