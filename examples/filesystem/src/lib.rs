//! Layer 1 types for tpt-filesystem (TODO.md, phase 7).
//!
//! A [`BlockRef`] is a block number known to lie on the device it was made for.
//! Its only constructor checks the bound, so a read through a `BlockRef` cannot
//! go past the end of the device. The device itself is tpt-filesystem's
//! `BlockDevice`, used unchanged.

#![forbid(unsafe_code)]

use tpt_filesystem_core::block::BlockDevice;
use tpt_filesystem_core::Result;
use tpt_proof::prelude::*;

/// Bytes per filesystem block. Matches `SUPERBLOCK_SIZE` in tpt-filesystem.
pub const BLOCK_SIZE: Bytes = Bytes(4096);

/// A block number strictly below `total`, the number of blocks on the device.
#[refined(block < total)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BlockRef {
    block: usize,
    total: usize,
}

/// The number of whole blocks on `device`. A partial block at the end is not counted.
pub fn block_count(device: &impl BlockDevice) -> Blocks {
    Blocks(device.size_bytes() / BLOCK_SIZE.0)
}

/// The reference to block `block` on `device`, or `None` if it is past the end.
pub fn block_ref(device: &impl BlockDevice, block: usize) -> Option<BlockRef> {
    let total = usize::try_from(block_count(device).0).ok()?;
    BlockRef::new(block, total)
}

/// Reads the whole block that `block` refers to.
pub fn read_block(device: &mut impl BlockDevice, block: BlockRef) -> Result<Vec<u8>> {
    let mut buf = vec![0; BLOCK_SIZE.0 as usize];
    device.read_at(block.block() as u64 * BLOCK_SIZE.0, &mut buf)?;
    Ok(buf)
}

#[cfg(test)]
mod tests {
    use tpt_filesystem_core::block::MemDevice;

    use super::*;

    fn device(blocks: u64) -> MemDevice {
        MemDevice::new((blocks * BLOCK_SIZE.0) as usize)
    }

    #[test]
    fn block_count_is_whole_blocks() {
        let mut device = device(8);
        assert_eq!(block_count(&device), Blocks(8));
        // A partial block at the end is not counted.
        device = MemDevice::new(8 * 4096 + 100);
        assert_eq!(block_count(&device), Blocks(8));
    }

    #[test]
    fn a_reference_exists_only_for_blocks_on_the_device() {
        let device = device(8);
        assert_eq!(block_ref(&device, 7).map(|b| b.block()), Some(7));
        assert_eq!(block_ref(&device, 8), None);
    }

    #[test]
    fn reading_through_a_reference_returns_one_block() {
        let mut device = device(4);
        let block = block_ref(&device, 3).expect("in range");
        let bytes = read_block(&mut device, block).expect("reads");
        assert_eq!(bytes.len(), BLOCK_SIZE.0 as usize);
    }

    #[test]
    fn the_refined_bound_is_checked_at_construction() {
        assert!(BlockRef::new(3, 4).is_some());
        assert!(BlockRef::new(4, 4).is_none());
    }
}
