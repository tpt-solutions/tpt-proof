# Changelog

All notable changes to `tpt-proof-example-filesystem` are recorded here. The format
follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/). The example is
pre-alpha and not published, so the entries under Unreleased describe its current
state.

## Unreleased

### Added

- `BlockRef`, a `#[refined(block < total)]` block number whose only constructor
  checks the bound against the device.
- `BLOCK_SIZE`, `block_count` and `block_ref`, which take the device size from
  tpt-filesystem's `BlockDevice` and use tpt-proof's `Blocks` and `Bytes` units.
- `read_block`, which reads through a `BlockRef`, so it cannot be given a block past
  the end of the device.
- Tests for the block count, the bound, reading through a reference, and the
  refined constructor.
- The pinned dependency on tpt-filesystem at commit `cfbb1aa`.
