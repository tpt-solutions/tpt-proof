//! Layer 1 of tpt-proof: type-level specifications (spec.txt §3).
//!
//! Layer 1 has zero runtime cost and zero proof burden. The invariants live in
//! the types, and the compiler enforces them.
//!
//! What is here:
//! - [`refined::Index`]: a value below a compile-time bound, checked by const evaluation.
//! - [`units`]: byte, block, and sector quantities that cannot be mixed up.
//! - [`state_machine`]: type-state for handles that move through states.
//! - [`Ghost`]: a zero-cost marker for specification-only data.
//!
//! The `#[refined]` and `#[state_machine]` attributes from spec.txt §3 live in
//! `tpt-proof-macros`, and they expand to the same shapes as the hand-written
//! types here.

#![forbid(unsafe_code)]

use std::marker::PhantomData;

pub mod refined;
pub mod state_machine;
pub mod units;

/// Zero-cost marker for ghost (specification-only) data.
///
/// A `Ghost<T>` takes no space at runtime. It lets a type carry a fact about
/// `T` without storing a `T`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Ghost<T>(PhantomData<T>);

impl<T> Ghost<T> {
    /// Creates the marker.
    pub const fn new() -> Self {
        Ghost(PhantomData)
    }
}

/// Re-exports for code that writes specifications.
pub mod prelude {
    pub use crate::refined::Index;
    pub use crate::state_machine::{Closed, FileHandle, Open, State, Writing};
    pub use crate::units::{Blocks, Bytes, Sectors};
    pub use crate::Ghost;
}
