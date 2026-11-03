//! Layer 2 of tpt-proof: contract-based verification (spec.txt §3).
//!
//! The pipeline here is: a verification condition ([`vc::Vc`]) is encoded to
//! SMT-LIB ([`smt::encode`]) and discharged by Z3 ([`smt::check`]).
//!
//! [`smt::verify`] goes further: it asks Z3 for a proof and has the kernel check
//! it, through [`reflect`]. Only that path reports [`Outcome::Verified`]. A
//! solver `unsat` answer that the kernel does not confirm is reported as
//! [`Outcome::Unchecked`] (spec.txt §2, principle 5).
//!
//! Not built yet: MIR-to-VC translation (spec.txt §5) and contract macros.

#![forbid(unsafe_code)]

pub mod cache;
pub mod reflect;
pub mod smt;
pub mod spec;
pub mod vc;
pub mod wp;

pub use smt::{check, encode, verify, SolverConfig};
pub use vc::{Expr, Sort, Vc};

/// The result of checking a verification condition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// The solver reported that the negated goal is unsatisfiable, and no proof
    /// was checked. The goal holds according to the solver, but this is not
    /// `Verified`. [`smt::check`] reports this.
    SolverUnsat,
    /// The solver reported `unsat` and the kernel accepted its proof, so the
    /// goal is proved. Only [`smt::verify`] reports this.
    Verified,
    /// The solver reported `unsat`, but the proof could not be checked. The
    /// field gives the reason. This is not `Verified`.
    Unchecked {
        /// Why the proof was not accepted.
        reason: String,
    },
    /// The solver found a counterexample. The field holds its model text.
    Failed {
        /// Solver model text, one `define-fun` per variable.
        counterexample: String,
    },
    /// The solver ran out of time.
    Timeout,
    /// The solver answered `unknown` for another reason.
    Unknown(String),
    /// The VC was malformed, or the solver could not run.
    Error(String),
}
