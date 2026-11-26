# tpt-proof-cli

The `tpt-proof` command-line tool. It runs the static verifier on a Rust file,
prints a report on each library of proofs, exports proofs to Lean, and checks that
the tools verification needs are installed.

> Status: pre-alpha, not published. The binary is named `tpt-proof`; the package
> is `tpt-proof-cli`. Package-level verification (a whole Cargo package at once)
> and SARIF output are not built yet.

## Install

From the repository root:

```sh
cargo build -p tpt-proof-cli
export PATH="$PWD/target/debug:$PATH"   # or run ./target/debug/tpt-proof
```

Verification also needs the MIR driver, which is built with a pinned nightly
compiler, because it uses the compiler's internal interfaces. See the
[root README quickstart](../../README.md#quickstart). The CLI finds the driver
through `TPT_PROOF_MIR`, or on the PATH. It runs the driver under the toolchain
named by `TPT_PROOF_TOOLCHAIN`, which defaults to the pinned one.

Run `tpt-proof doctor` to check what is missing. It reports rustup, the pinned
toolchain, `z3`, the driver and `lean`, with the command that fixes each one.

## Commands

```text
tpt-proof verify <file.rs> [--timeout <ms>] [--z3-path <path>] [--json]
tpt-proof report <library>
tpt-proof export <library> [--out <file>]
tpt-proof doctor
tpt-proof --version | --help
```

### `verify`

Runs the MIR driver on one file and prints one verdict per assertion. The exit
status is 0 only if every assertion is proved and every function is inside the
supported subset. Anything else exits with a non-zero status, so an unverified
function never looks like a success.

```sh
tpt-proof verify crates/tpt-proof-mir/tests/fixtures/overflow_unsafe.rs
```

```text
add: assertion at bb0: counterexample: _2 = 255, _1 = 1
```

The line names the function, the assertion's location in the MIR, and a
counterexample: values for the inputs that break it. Read the counterexample to
find the input the function does not handle, then add a `requires` clause or fix
the code.

| Option | Effect |
|---|---|
| `--timeout <ms>` | solver timeout per assertion, in milliseconds. Default 10000. Sets `TPT_PROOF_TIMEOUT_MS`. |
| `--z3-path <path>` | the `z3` executable to run. Default: `z3` on the PATH. Sets `TPT_PROOF_Z3`. |
| `--json` | one JSON object per result, one per line: `{"function", "vc", "status", "detail"}`. Sets `TPT_PROOF_FORMAT=json`. |

Two environment variables change what the driver does, and the CLI does not set
them:

- `TPT_PROOF_VERIFY=1` asks Z3 for a proof and has the kernel check it. Results
  are then reported as `proved (kernel-checked)`. Without it, a proved assertion is
  only solver-checked. Proof mode is slower and bypasses the cache.
- `TPT_PROOF_CACHE=<directory>` stores solver results on disk, so unchanged
  assertions are not solved again.

### `report`

Prints the dependency report of a lemma library: each theorem, its statement, the
axioms it depends on, and each axiom's justification. Use it to see what a proof
rests on.

```sh
tpt-proof report lemmas.lib
```

### `export`

Writes a lemma library's lemmas as a Lean 4 file, which `lean` can check
independently of tpt-proof. Output goes to standard output unless `--out` is
given.

```sh
tpt-proof export lemmas.lib --out lemmas.lean
lean lemmas.lean
```

Some rules cannot be exported; see the
[export crate's limitations](../tpt-proof-export/README.md#limitations).

### `doctor`

Checks each tool and prints how to fix what is missing. It does not change
anything.

## Exit status

| Status | Meaning |
|---|---|
| 0 | success: every assertion proved, the command finished, or help or version was printed |
| 1 | a verdict was not proved, the driver failed, or a library could not be read or exported |
| 2 | bad command-line usage, or the pinned toolchain is missing for the driver |

## Library files

`report` and `export` read the text format written by
`tpt_proof::library::save`: one S-expression per line for each axiom, inductive
type, symbol and lemma. The CLI loads a library by replaying it through the
kernel, so a damaged or tampered file is rejected with the line that is wrong.

## Testing

```sh
cargo test -p tpt-proof-cli
```

## Where it fits

```text
tpt-proof-cli ──▶ tpt-proof (library, report)
              ──▶ tpt-proof-export (Lean)
              ──▶ tpt-proof-mir driver, as a separate process (verify)
```

## Changelog

See [CHANGELOG.md](CHANGELOG.md).

## License

Licensed under either of Apache License, Version 2.0 or MIT license, at your
option. See the [root README](../../README.md#license).
