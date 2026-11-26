# tpt-proof-macros

Attribute macros for [tpt-proof](../../README.md). They attach contracts to
functions and specifications to types. Each attribute does two things: it records
the specification where the static verifier can read it, and it compiles to a
check that runs only in debug builds.

Most users do not depend on this crate directly. Import the attributes through
the facade, `tpt_proof::prelude::*`.

> Status: pre-alpha, not published. This is a proc-macro crate, so it has no
> runtime code of its own.

## Attributes

| Attribute | Layer | Effect |
|---|---|---|
| `#[requires(cond)]` | 2 | Checks `cond` on entry. Repeat it for several conditions. |
| `#[ensures(\|result\| cond)]` | 2 | Checks `cond` on the return value. The binder names the result. |
| `#[runtime_check(cond)]` | 4 | Same as `requires`. This is the form in spec.txt §3. |
| `#[invariant(line, cond)]` | 2 | Declares the invariant of the loop that starts on source `line`. Verification only; there is no runtime check. |
| `#[refined(value < bound)]` | 1 | On a struct, adds a checked `new` and a getter. |
| `#[state_machine(A, B, ...)]` | 1 | On a struct, makes it generic over sealed state markers. |

### Contracts

```rust
use tpt_proof::prelude::*;

#[requires(divisor != 0)]
#[ensures(|result| *result <= 10)]
fn quotient(value: u32, divisor: u32) -> u32 {
    value / divisor
}
```

`requires` checks its condition with `debug_assert!`, so a call with a zero
divisor panics in a debug build with a message that names the condition. In a
release build the check is removed.

`ensures` evaluates the body inside a closure, so `return` and `?` work as usual.
Because of the closure, the function must declare its return type explicitly,
which is always true for a non-unit return.

Conditions can use `==>` for implication. It is rewritten to `!(a) || (b)` before
it is parsed.

### Loop invariants

```rust
#[invariant(5, i <= n && total == i)]   // 1
fn sum(n: u32) -> u32 {                  // 2
    let mut total = 0;                   // 3
    let mut i = 0;                       // 4
    while i < n {                        // 5: the loop the invariant describes
        total += 1;
        i += 1;
    }
    total
}
```

The first argument is the source line of the `while` loop, and the second is the
invariant. The invariant is a verification condition only. The verifier checks
that it holds on entry to the loop, and that each pass through the body preserves
it. The loop is matched to its invariant by that line number, so keep the
attribute's line number in step with the loop.

### Refined structs

```rust
#[refined(value < total_blocks)]
struct BlockIndex {
    value: usize,
    total_blocks: usize,
}

assert!(BlockIndex::new(3, 8).is_some());
assert!(BlockIndex::new(8, 8).is_none());
```

The bound is another field or an integer literal. The refined field must be
`Copy`, because the getter returns it by value. A struct literal in the defining
module can still skip `new`, so keep the struct in its own module when the bound
must hold everywhere.

### State machines

```rust
#[state_machine(Idle, Busy)]
struct Worker {
    id: u32,
}

impl Worker<Idle> {
    fn begin(self) -> Worker<Busy> {
        self.transition()
    }
}
```

The macro declares one marker type per listed state, makes the struct generic
over its state, and adds a `PhantomData` field. The state trait is sealed, so only
the listed states implement it. Transitions are written by hand. The struct must
not already have a `state` field, and it cannot have generics.

## How the attributes work with the verifier

Each contract attribute records a doc marker on the function, with the prefix
`tpt-proof-requires:`, `tpt-proof-ensures:` or `tpt-proof-invariant:`. The MIR
translator in [`tpt-proof-mir`](../tpt-proof-mir/) reads those markers. The
prefixes are constants in `src/lib.rs`, and the translator must use the same
strings.

The runtime check is switched off when `cfg(tpt_proof_verify)` is set. The
verification driver sets it, so the translator sees only the function's own code,
not the check code.

Crates that use these attributes declare the cfg, so the compiler does not warn
about it:

```toml
[lints.rust]
unexpected_cfgs = { level = "warn", check-cfg = ["cfg(tpt_proof_verify)"] }
```

## Testing

The attributes are tested through the facade, which has the compile-fail suite
for misuse (duplicate state names, pattern binders in `ensures`, a `refined` bound
that is not a field, and a transition from the wrong state):

```sh
cargo test -p tpt-proof
```

## Where it fits

```text
tpt-proof-macros ──▶ syn, quote, proc-macro2
        ▲
tpt-proof (facade) re-exports the attributes
```

## Changelog

See [CHANGELOG.md](CHANGELOG.md).

## License

Licensed under either of Apache License, Version 2.0 or MIT license, at your
option. See the [root README](../../README.md#license).
