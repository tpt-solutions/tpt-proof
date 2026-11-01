//! Unit correctness: bytes, blocks, and sectors are distinct types.
//!
//! Adding a block count to a byte count, or passing a sector number where a
//! block number is expected, is a compile error. Conversions have to name the
//! size they use.
//!
//! ```compile_fail
//! use tpt_proof_core::units::{Blocks, Bytes};
//!
//! let _ = Blocks(2) + Bytes(4096);
//! ```

use std::ops::Add;

/// A quantity of bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Bytes(pub u64);

/// A quantity of filesystem blocks. Its size in bytes depends on the filesystem.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Blocks(pub u64);

/// A quantity of device sectors.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Sectors(pub u64);

impl Blocks {
    /// Converts to bytes, given the block size in bytes. Returns `None` on overflow.
    pub const fn to_bytes(self, block_size: Bytes) -> Option<Bytes> {
        match self.0.checked_mul(block_size.0) {
            Some(bytes) => Some(Bytes(bytes)),
            None => None,
        }
    }
}

impl Bytes {
    /// Rounds up to whole blocks of the given size. Returns `None` if `block_size` is zero.
    pub const fn to_blocks_round_up(self, block_size: Bytes) -> Option<Blocks> {
        if block_size.0 == 0 {
            return None;
        }
        Some(Blocks(self.0.div_ceil(block_size.0)))
    }
}

impl Add for Bytes {
    type Output = Bytes;
    fn add(self, rhs: Bytes) -> Bytes {
        Bytes(self.0 + rhs.0)
    }
}

impl Add for Blocks {
    type Output = Blocks;
    fn add(self, rhs: Blocks) -> Blocks {
        Blocks(self.0 + rhs.0)
    }
}

impl Add for Sectors {
    type Output = Sectors;
    fn add(self, rhs: Sectors) -> Sectors {
        Sectors(self.0 + rhs.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_convert_to_bytes() {
        assert_eq!(Blocks(3).to_bytes(Bytes(4096)), Some(Bytes(12288)));
    }

    #[test]
    fn block_conversion_reports_overflow() {
        assert_eq!(Blocks(u64::MAX).to_bytes(Bytes(2)), None);
    }

    #[test]
    fn bytes_round_up_to_blocks() {
        assert_eq!(Bytes(4097).to_blocks_round_up(Bytes(4096)), Some(Blocks(2)));
        assert_eq!(Bytes(4096).to_blocks_round_up(Bytes(4096)), Some(Blocks(1)));
        assert_eq!(Bytes(0).to_blocks_round_up(Bytes(4096)), Some(Blocks(0)));
    }

    #[test]
    fn zero_block_size_is_rejected() {
        assert_eq!(Bytes(1).to_blocks_round_up(Bytes(0)), None);
    }

    #[test]
    fn same_unit_addition() {
        assert_eq!(Bytes(2) + Bytes(3), Bytes(5));
        assert_eq!(Sectors(1) + Sectors(1), Sectors(2));
    }
}
