# Changelog

All notable changes to `tpt-proof-core` are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). The crate is pre-alpha
and not published, so the entries under Unreleased describe its current state.

## Unreleased

### Added

- `refined::Index<N>`: a value below the bound `N`, with a `const` constructor
  (`new_const`) that fails to compile for a bad value, a checked runtime
  constructor (`new`), `get`, and the bound query `bound()`.
- `Index::widen::<M>()`, a checked conversion to a larger bound.
- `units::Bytes`, `Blocks` and `Sectors`, each addable only to itself, with
  `Blocks::to_bytes` and `Bytes::to_blocks_round_up`, which take the block size
  and return `Option`.
- `state_machine::FileHandle<S>` with the sealed states `Open`, `Writing` and
  `Closed`, and transitions that do not compile from the wrong state.
- `Ghost<T>`, a zero-sized marker for specification-only data.
- `prelude`, which re-exports the types above.
- `trybuild` tests that check the compile errors for an index out of bounds,
  mixed units, and a write after close.
