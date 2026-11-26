# tpt-proof-runtime

Layer 4 of [tpt-proof](../../README.md): runtime verification. It turns a
specification into a check that runs in debug builds and disappears from release
builds, and it provides tools for testing contracts against real inputs.

Use it for code that the static verifier cannot reach: FFI, legacy code, and
third-party libraries. Where a function can be verified, prefer the static
checks; the runtime checks are the fallback, and they only test the inputs you
run.

> Status: pre-alpha, not published. The `#[runtime_check(...)]` attribute is
> provided by [`tpt-proof-macros`](../tpt-proof-macros/) and re-exported by the
> facade. This crate provides the `runtime_check!` macro and the helpers below.

## What it provides

| Item | Purpose |
|---|---|
| `runtime_check!(cond)` | A `debug_assert!` that names the condition in its failure message. Compiled out in release builds. |
| [`replay::run`](src/replay.rs) | Calls a function under chosen inputs and reports whether a contract failed. Used to confirm a counterexample from the static verifier on the real code. |
| [`property::check`](src/property.rs) | Runs a property over inputs from a `proptest` strategy, with shrinking. Behind the `proptest` feature. |

## Runtime checks

```rust
use tpt_proof_runtime::runtime_check;

fn scale(value: u32, factor: u32) -> u32 {
    runtime_check!(factor != 0);
    value / factor
}
```

In a debug build, a false condition panics with a message such as
`runtime check failed: factor != 0`. In a release build the check is removed, so
it costs nothing in the shipped binary.

The attribute form does the same for a whole function:

```rust
use tpt_proof::prelude::*;

#[runtime_check(factor != 0)]
fn scale(value: u32, factor: u32) -> u32 {
    value / factor
}
```

## Replaying a counterexample

The static verifier reports a counterexample as values for the function's inputs.
`replay::run` calls the real function with those values and reports what
happened:

```rust
use std::panic::AssertUnwindSafe;
use tpt_proof_runtime::replay::{run, Replay};

let outcome = run(AssertUnwindSafe(|| {
    let _ = scale(7, 0);
}));

match outcome {
    Replay::Confirmed(message) => println!("a contract failed: {message}"),
    Replay::Panicked(message) => println!("the function panicked: {message}"),
    Replay::Passed => println!("no failure with these inputs"),
}
```

- `Confirmed`: a contract failed. A panic counts as a contract failure when its
  message says `precondition failed`, `postcondition failed` or `runtime check
  failed`, which are the messages the contract checks use. The verifier's
  counterexample is real.
- `Panicked`: the function panicked for another reason, such as an index out of
  bounds. The counterexample still shows a real failure of the code.
- `Passed`: the function returned normally. In a release build this is always the
  result, because contracts are debug assertions.

`replay::run` catches panics, so many replays can run in one test. The default
panic hook still prints each panic message.

## Property tests with proptest

Enable the feature in your `Cargo.toml`:

```toml
[dependencies]
tpt-proof-runtime = { path = "../tpt-proof-runtime", features = ["proptest"] }
```

Then check a property over generated inputs:

```rust
use tpt_proof_runtime::property::check;

check(0u32..1000, |&n| n + 1 > n);
```

`check` runs the property with proptest's default configuration. A failing input
is shrunk to a smaller one before the failure is reported. The feature is off by
default, so the crate has no dependencies unless you ask for them.

## Testing

```sh
cargo test -p tpt-proof-runtime                    # runtime_check and replay
cargo test -p tpt-proof-runtime --features proptest
```

## Where it fits

```text
tpt-proof-runtime ──▶ (proptest, optional)
        ▲
tpt-proof (facade) ──┘
```

This crate depends on no other tpt-proof crate. The facade re-exports its
macros, and the static verifier's counterexamples are fed to `replay::run`.

## Changelog

See [CHANGELOG.md](CHANGELOG.md).

## License

Licensed under either of Apache License, Version 2.0 or MIT license, at your
option. See the [root README](../../README.md#license).
