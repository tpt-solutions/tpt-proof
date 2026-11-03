# tpt-proof

A layered, Rust-native formal verification framework for stateful, concurrent,
data-structure-heavy Rust code. See [spec.txt](spec.txt) for the design and
[TODO.md](TODO.md) for the task checklist.

> Status: pre-alpha. The proof kernel checks proofs, and the Z3-backed verifier
> works for a narrow subset of Rust. Much is still missing; see [TODO.md](TODO.md).
> Not for production use.

## Quickstart

You need [Z3](https://github.com/Z3Prover/z3/releases) on the PATH, and
[rustup](https://rustup.rs). The MIR driver is built with a pinned nightly, so
install that toolchain first:

```sh
rustup toolchain install nightly-2026-10-31 --component rustc-dev --component llvm-tools-preview
cargo build -p tpt-proof-cli                      # the tpt-proof command
(cd crates/tpt-proof-mir && cargo build)          # the driver, with the pinned nightly
export TPT_PROOF_MIR="$PWD/crates/tpt-proof-mir/target/debug/tpt-proof-mir"
./target/debug/tpt-proof verify crates/tpt-proof-mir/tests/fixtures/overflow_unsafe.rs
```

The output has one line per assertion. A `counterexample` line names inputs that
break the assertion, and the exit status is 0 only if every assertion is proved:

```text
add: assertion at bb0: counterexample: _2 = 255, _1 = 1
```

Options: `--timeout <ms>` sets the solver timeout per assertion, `--z3-path <path>`
picks the z3 executable, and `--json` prints one JSON object per result. Run
`tpt-proof --help` for the full list. Set `TPT_PROOF_VERIFY=1` to have the kernel
check each proof; without it, a proved assertion is only solver-checked.

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.

Copyright (c) 2026 TPT Solutions.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this work, as defined in the Apache-2.0 license, shall be dual
licensed as above, without any additional terms or conditions.
