# examples/filesystem

Layer 1 types for [tpt-filesystem](https://github.com/tpt-solutions/tpt-filesystem), built on tpt-proof (TODO.md, phase 7).

- `BlockRef` is a `#[refined(block < total)]` block number. Its constructor checks the bound against the device, so a read through it cannot pass the end of the device.
- `block_count` and `block_ref` take the device size from tpt-filesystem's `BlockDevice` and use tpt-proof's `Blocks` and `Bytes` units.

This directory is a standalone Cargo workspace, not a member of tpt-proof's. It depends on tpt-filesystem at a pinned commit (`cfbb1aa`), and that repository's dependencies are outside tpt-proof's license audit. Run it with:

```bash
cargo test --manifest-path examples/filesystem/Cargo.toml
```

Layer 2 and Layer 3 proofs for the filesystem wait on MIR translation and the proof-producing reflection (TODO.md, phases 3 and 7).
