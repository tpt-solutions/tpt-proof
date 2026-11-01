//! Layer 2 of tpt-proof: contract-based verification (SPEC.md §3).
//!
//! The pipeline here is: a verification condition ([`vc::Vc`]) is encoded to
//! SMT-LIB ([`smt::encode`]) and discharged by Z3 ([`smt::check`]).
//!
//! Not built yet: MIR-to-VC translation (SPEC.md §5), contract macros, and
//! proof-producing reflection. Until reflection exists, a solver `unsat` answer
//! is reported as [`Outcome::SolverUnsat`], never as `Verified` (SPEC.md §2,
//! principle 5).

#![forbid(unsafe_code)]

pub mod smt;
pub mod vc;
pub mod wp;

pub use smt::{check, encode, SolverConfig};
pub use vc::{Expr, Sort, Vc};

/// The result of checking a verification condition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// The solver reported that the negated goal is unsatisfiable. The goal
    /// holds according to the solver, but no proof certificate has been checked
    /// by the kernel yet, so this is not `Verified`.
    SolverUnsat,
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
