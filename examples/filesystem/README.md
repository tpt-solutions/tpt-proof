# tpt-proof-example-filesystem

A worked example of [tpt-proof](../../README.md) applied to a real storage
library, [tpt-filesystem](https://github.com/tpt-solutions/tpt-filesystem). It
shows how the Layer 1 types of tpt-proof make a class of bugs impossible to write,
and it marks where the Layer 2 and Layer 3 proofs will go.

This is the phase 7 target of [TODO.md](../../TODO.md): the goal is a filesystem
with mathematical guarantees, and this crate is the first step toward it.

> Status: pre-alpha, not published (`publish = false`). Only Layer 1 is in place.
> The contracts and proofs described at the end are not written yet.

## What it provides

| Item | Purpose |
|---|---|
| `BlockRef` | A block number known to lie on the device it was made for. It is a `#[refined(block < total)]` struct, so its only constructor checks the bound. |
| `BLOCK_SIZE` | Bytes per block (4096), as tpt-proof's `Bytes` unit. |
| `block_count(&device)` | The number of whole blocks on a device, as `Blocks`. |
| `block_ref(&device, n)` | A `BlockRef` for block `n`, or `None` if it is past the end. |
| `read_block(&mut device, block)` | Reads the whole block a `BlockRef` names. It cannot be given a block past the end, because a `BlockRef` cannot be built for one. |

The device itself is tpt-filesystem's `BlockDevice`, used unchanged.

## Why this matters

Reading block 9 of an 8-block device is an out-of-bounds read. In a plain
`usize` API, that is a runtime error or, worse, a silent read of the wrong data.
Here, the function that reads takes a `BlockRef`, and the only way to get one is
`block_ref`, which checks the bound against the device. The bad read is not a
runtime failure to handle. There is no value to pass.

```rust
use tpt_proof_example_filesystem::{block_ref, read_block};

let mut device = /* a BlockDevice with 8 blocks */;

let last = block_ref(&device, 7).expect("block 7 exists");
let bytes = read_block(&mut device, last)?;

assert!(block_ref(&device, 8).is_none());   // there is no BlockRef for block 8
```

## Running it

This directory is a standalone Cargo workspace, not a member of tpt-proof's. Its
dependencies are not part of tpt-proof's license audit, so it is kept out of the
root workspace. Run its tests with:

```sh
cargo test --manifest-path examples/filesystem/Cargo.toml
```

The dependency on tpt-filesystem is pinned to commit `cfbb1aa`, which tpt-filesystem
itself pins. Bump the pin deliberately, and check the license audit when you do.

## Tests

| Test | Checks |
|---|---|
| `block_count_is_whole_blocks` | a partial block at the end of the device is not counted |
| `a_reference_exists_only_for_blocks_on_the_device` | `block_ref` returns `None` past the end |
| `reading_through_a_reference_returns_one_block` | a read through a `BlockRef` returns one whole block |
| `the_refined_bound_is_checked_at_construction` | `BlockRef::new` checks the bound |

## Where it goes next

The rest of the filesystem guarantees need the later phases of tpt-proof:

- **Layer 2, contracts** on most functions: once MIR translation covers the
  filesystem's code (phase 3), its functions get `requires` and `ensures`
  clauses, checked by Z3.
- **Layer 3, proofs** of B-Tree balance, copy-on-write atomicity and transaction
  isolation (phase 7), using the interactive tactics and the kernel.

Until then, this crate shows the Layer 1 pattern that the rest will build on.

## Where it fits

```text
tpt-proof-example-filesystem ──▶ tpt-proof (facade) ──▶ tpt-proof-core, tpt-proof-kernel, …
                             ──▶ tpt-filesystem-core (pinned git dependency)
```

## Changelog

See [CHANGELOG.md](CHANGELOG.md).

## License

Licensed under either of Apache License, Version 2.0 or MIT license, at your
option. See the [root README](../../README.md#license).
