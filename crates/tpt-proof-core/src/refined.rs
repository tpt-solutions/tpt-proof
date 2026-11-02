//! Refined values: a `usize` known to be below a bound `N`.
//!
//! `Index<N>` mirrors `#[refined(value < N)]` from spec.txt §3. When it is built
//! in a const context, a failed bound is a compile error. At runtime it is a
//! checked constructor. Either way there is no per-access cost after the
//! value is built.
//!
//! ```
//! use tpt_proof_core::refined::Index;
//!
//! const SLOT: Index<8> = Index::new_const(3);
//! assert_eq!(SLOT.get(), 3);
//! assert!(Index::<8>::new(8).is_none());
//! ```
//!
//! A bound violation in a const context does not compile:
//!
//! ```compile_fail
//! use tpt_proof_core::refined::Index;
//!
//! const BAD: Index<8> = Index::new_const(9);
//! ```

/// A `usize` strictly less than `N`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Index<const N: usize>(usize);

impl<const N: usize> Index<N> {
    /// Builds the index, or returns `None` when `value >= N`.
    pub const fn new(value: usize) -> Option<Self> {
        if value < N {
            Some(Index(value))
        } else {
            None
        }
    }

    /// Builds the index in a const context. Panics, and so fails to compile
    /// when used in a constant, if `value >= N`.
    pub const fn new_const(value: usize) -> Self {
        assert!(value < N, "index out of bounds");
        Index(value)
    }

    /// The underlying value. It is always less than `N`.
    pub const fn get(self) -> usize {
        self.0
    }

    /// The bound `N`: every value of this type is below it.
    pub const fn bound() -> usize {
        N
    }

    /// Re-checks the same value against a larger bound `M`. Panics, and so
    /// fails to compile in a constant, if `M < N`, because a value below `N`
    /// is not known to be below a smaller bound.
    ///
    /// ```
    /// use tpt_proof_core::refined::Index;
    ///
    /// const WIDE: Index<16> = Index::<4>::new_const(3).widen::<16>();
    /// assert_eq!(WIDE.get(), 3);
    /// assert_eq!(Index::<16>::bound(), 16);
    /// ```
    ///
    /// Widening to a smaller bound does not compile in a constant:
    ///
    /// ```compile_fail
    /// use tpt_proof_core::refined::Index;
    ///
    /// const NARROW: Index<4> = Index::<8>::new_const(3).widen::<4>();
    /// ```
    pub const fn widen<const M: usize>(self) -> Index<M> {
        assert!(N <= M, "widening to a smaller bound");
        Index(self.0)
    }
}
