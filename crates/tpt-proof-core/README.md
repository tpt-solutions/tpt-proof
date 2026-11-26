# tpt-proof-core

Layer 1 of [tpt-proof](../../README.md): type-level specifications. Invariants
are encoded in the types, so the Rust compiler enforces them, and nothing has to
be proved.

Layer 1 has zero runtime cost and zero proof burden. An `Index<8>` holds a
`usize`, a `Bytes` holds a `u64`, and a `FileHandle<S>` holds a `u32` plus a
zero-sized state marker. The checks happen at compile time, or once when a value
is built.

> Status: pre-alpha. The types here are hand-written reference shapes. The
> `#[refined]` and `#[state_machine]` attributes in
> [`tpt-proof-macros`](../tpt-proof-macros/) are meant to generate the same shapes.

## What it provides

| Module | Item | Purpose |
|---|---|---|
| [`refined`](src/refined.rs) | `Index<const N: usize>` | A value strictly below the bound `N`. Built in a `const` context, a failed bound is a compile error. |
| [`units`](src/units.rs) | `Bytes`, `Blocks`, `Sectors` | Quantities that cannot be mixed up. Adding blocks to bytes does not compile. |
| [`state_machine`](src/state_machine.rs) | `FileHandle<S>` with `Open`, `Writing`, `Closed` | Type-state: a transition that is not allowed from the current state does not compile. |
| [`lib`](src/lib.rs) | `Ghost<T>` | A zero-sized marker for data that exists only in specifications. |
| [`prelude`](src/lib.rs) | everything above | One import for the common types. |

The `State` trait is sealed, so code outside the crate cannot add states that
the transitions were not written for.

## Usage

```rust
use tpt_proof_core::prelude::*;

// A slot in a table of 8 entries. `new_const` fails to compile if 9 is passed.
const SLOT: Index<8> = Index::new_const(3);

// Blocks and bytes are different types.
let block_size = Bytes(4096);
let blocks = Blocks(2);
// let total = block_size + blocks; // does not compile: no `Add<Blocks>` for `Bytes`

// A file handle must finish writing before it can close.
let handle = FileHandle::open(7).begin_write().end_write();
let closed = handle.close();
assert_eq!(closed.fd(), 7);

let _ = SLOT;
```

`Index::new(value)` is the checked runtime constructor and returns `Option`.
`Index::bound()` reads the bound, and `widen::<M>()` converts an index to a
larger bound `M`, which is checked at compile time.

Units convert only through named functions that state the block size:
`Blocks::to_bytes(block_size)` and `Bytes::to_blocks_round_up(block_size)`. Each
returns `Option`, so an overflow is reported rather than wrapped. `Bytes`,
`Blocks` and `Sectors` each add only to themselves.

The `#[refined(...)]` attribute in `tpt-proof-macros` expands to the same checked
constructor and getter. The hand-written `FileHandle` is the reference for the
`#[state_machine(...)]` attribute.

## Compile-time checks

Two kinds of test check that the bad code is rejected, using
[`trybuild`](https://crates.io/crates/trybuild):

- `tests/ui/index_out_of_bounds.rs`: an index outside its bound.
- `tests/ui/units_mixed.rs`: arithmetic across unit types.
- `tests/ui/write_after_close.rs`: a transition from the wrong state.

The `.stderr` files next to them hold the expected compiler messages. They change
when the compiler's wording changes, so regenerate them with `TRYBUILD=overwrite`
after checking that the new message is still clear.

## Where it fits

`tpt-proof-core` has no dependency on the other tpt-proof crates. The facade
[`tpt-proof`](../tpt-proof/) re-exports its prelude, so most users import it
through `tpt_proof::prelude::*`.

## Testing

```sh
cargo test -p tpt-proof-core
```

## Changelog

See [CHANGELOG.md](CHANGELOG.md).

## License

Licensed under either of Apache License, Version 2.0 or MIT license, at your
option. See the [root README](../../README.md#license).
