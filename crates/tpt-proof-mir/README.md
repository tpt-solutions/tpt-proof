# tpt-proof-mir

The MIR translator and verification driver for [tpt-proof](../../README.md). It
reads a Rust file through the compiler's own analysis, turns each supported
function into verification conditions (VCs), and checks them with Z3.

This is the only tpt-proof crate that talks to the Rust compiler. It uses
`rustc_private` interfaces, which exist only on a nightly compiler, so the crate
is kept out of the stable workspace and pins its own toolchain.

> Status: pre-alpha, not published (`publish = false`). It verifies a subset of
> integer and boolean Rust. Anything outside the subset is reported by name, and
> never counted as verified.

## Build

The crate pins `nightly-2026-10-31` with the `rustc-dev` and `llvm-tools-preview`
components, in [`rust-toolchain.toml`](rust-toolchain.toml). Install the toolchain
first, then build from this directory:

```sh
rustup toolchain install nightly-2026-10-31 --component rustc-dev --component llvm-tools-preview
cd crates/tpt-proof-mir
cargo build
```

The binary is `target/debug/tpt-proof-mir`. Point the command-line tool at it with
`TPT_PROOF_MIR`, or leave it on the PATH. Run `tpt-proof doctor` to check.

This crate has its own `[workspace]` table, so it is not built by the root
`cargo build`.

## Use

The usual route is the command-line tool, which passes options to the driver as
environment variables:

```sh
tpt-proof verify crates/tpt-proof-mir/tests/fixtures/overflow_unsafe.rs
```

To run the driver directly:

```sh
TPT_PROOF_Z3=/usr/bin/z3 TPT_PROOF_TIMEOUT_MS=5000 \
  ./target/debug/tpt-proof-mir path/to/file.rs
```

### Output

The driver prints one line per assertion, and a line for each function that is
outside the supported subset:

```text
add: assertion at bb0: counterexample: _2 = 255, _1 = 1
```

With `TPT_PROOF_FORMAT=json`, it prints one JSON object per line:

```json
{"function": "add", "vc": "assertion at bb0", "status": "counterexample", "detail": "_2 = 255, _1 = 1"}
```

`vc` is `null` for a line about the function as a whole, such as an unsupported
construct.

The exit status is 0 only if every VC is proved and every function is in the
supported subset. Anything else exits with 1, so a failed or unverified function
never looks like a success.

### Environment

| Variable | Effect |
|---|---|
| `TPT_PROOF_Z3` | path to the `z3` executable. Default: `z3` on the PATH. |
| `TPT_PROOF_TIMEOUT_MS` | solver timeout per VC. Default: 10000. |
| `TPT_PROOF_FORMAT` | `json` for one JSON object per line. Default: text. |
| `TPT_PROOF_VERIFY` | `1` asks Z3 for a proof and has the kernel check it. The output then says `proved (kernel-checked)`. Default: solver-checked only. |
| `TPT_PROOF_CACHE` | directory for the VC result cache. Default: in memory. Proof mode bypasses the cache. |

Without `TPT_PROOF_VERIFY=1`, a proved VC means only that Z3 answered `unsat`. The
kernel-checked mode is the one that does not trust the solver.

## What the translator supports

The translator walks the optimized MIR of each function symbolically. Each path
carries a map from locals to expressions and the branch conditions taken so far.
Each `assert` in MIR becomes a VC under those conditions, with the ranges of the
integer parameters as assumptions.

Supported:

- integer and boolean parameters and locals, with straight-line code, `if`, and
  `return`;
- overflow checks on `+`, `-` and `*`, and division and remainder for signed and
  unsigned integers, with Rust's truncation rules, checked against concrete values;
- loops with an invariant written as `#[invariant(line, cond)]`, checked by the
  standard rule: the invariant holds on entry, the loop body preserves it, and the
  loop variables are replaced by fresh values before the body is analysed;
- `#[requires]` and `#[ensures]` contracts, read from the function's doc markers;
- direct calls, using the callee's contract as a summary, so a caller is checked
  against the callee's `requires` and inherits its `ensures`. A call to a function
  without contracts is reported, not assumed to be safe;
- shared references to scalars, which are modelled by their pointee, relying on
  rustc's borrow checker for soundness.

Reported as unsupported, not verified: generic calls, mutable references,
closures, and any other MIR construct not listed above. Mutable references are
designed in [`docs/design-ownership-phase2.md`](../../docs/design-ownership-phase2.md)
but not built.

The VC is only as strong as this translation. Each unsupported construct makes the
whole function unverified, which is the intended behaviour.

## Fixtures

`tests/fixtures/` holds one small Rust file per case. Some should prove, some
should fail with a counterexample, and some should be reported as unsupported.
Examples, with the expectation that `tests/driver.rs` checks:

| Fixture | Expected result |
|---|---|
| `overflow_unsafe.rs` | counterexample: the addition can overflow |
| `div_guarded.rs` / `div_unguarded.rs` | proved / counterexample for the zero divisor |
| `contract_ok.rs` / `contract_ensures_fails.rs` | proved / counterexample for the postcondition |
| `loop_verified.rs` / `loop_wrong_invariant.rs` | proved / counterexample |
| `loop_no_invariant.rs` | reported as unsupported, with its line |
| `mut_ref_unsupported.rs`, `cell_unsupported.rs` | reported as unsupported |

`tests/driver.rs` runs the built driver on each fixture and checks its output.

## Testing

```sh
cd crates/tpt-proof-mir
cargo test
```

The tests run the driver on the fixtures, so they need Z3 on the PATH (or
`TPT_PROOF_Z3`).

## Where it fits

```text
tpt-proof-cli ──(process, env vars)──▶ tpt-proof-mir ──▶ tpt-proof-contract ──▶ z3
                                                            │
                                                            └──▶ tpt-proof-kernel (proof mode)
```

## Changelog

See [CHANGELOG.md](CHANGELOG.md).

## License

Licensed under either of Apache License, Version 2.0 or MIT license, at your
option. See the [root README](../../README.md#license).
