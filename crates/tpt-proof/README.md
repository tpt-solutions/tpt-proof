# tpt-proof

The user-facing facade of [tpt-proof](../../README.md), a layered Rust-native
formal verification framework. This crate is the one most users depend on. It
re-exports the types of each layer in one prelude, provides the attributes for
contracts, and provides the interactive proof API (tactics), lemma libraries and
dependency reports.

> Status: pre-alpha, not published (`publish = false`). Not for production use.

## What it provides

| Layer | Where | What you get |
|---|---|---|
| 1. Type-level specs | [`tpt-proof-core`](../tpt-proof-core/) | `Index<N>`, units, type-state, `Ghost` |
| 2. Contracts | [`tpt-proof-macros`](../tpt-proof-macros/), [`tpt-proof-contract`](../tpt-proof-contract/) | `#[requires]`, `#[ensures]`, `#[invariant]`, `#[refined]`, `#[state_machine]` |
| 3. Interactive proofs | this crate, [`tactics`](src/tactics.rs) | `Proof`, tactics, lemma `library`, `report` |
| 4. Runtime checks | [`tpt-proof-runtime`](../tpt-proof-runtime/) | `runtime_check!`, counterexample replay, proptest |

The kernel that checks every interactive proof is
[`tpt-proof-kernel`](../tpt-proof-kernel/). This crate depends on it, but the
kernel is the only place where a theorem is accepted.

## Installation

This crate is not published yet. Depend on it by path inside the repository:

```toml
[dependencies]
tpt-proof = { path = "crates/tpt-proof" }
```

Contract attributes need one extra line in the crate that uses them, so the
compiler does not warn about the `tpt_proof_verify` configuration that the
verification driver sets:

```toml
[lints.rust]
unexpected_cfgs = { level = "warn", check-cfg = ["cfg(tpt_proof_verify)"] }
```

## Quick tour

Import the prelude to get the types for each layer:

```rust
use tpt_proof::prelude::*;

// Layer 1: a slot below 8, and a file handle that must finish writing before it closes.
const SLOT: Index<8> = Index::new_const(3);
let handle = FileHandle::open(7).begin_write().end_write();
let _ = (SLOT, handle, Bytes(4096));
```

Contracts compile to debug-build checks. In release builds they cost nothing:

```rust
use tpt_proof::prelude::*;

#[requires(divisor != 0)]
#[ensures(|result| *result <= 10)]
fn quotient(value: u32, divisor: u32) -> u32 {
    value / divisor
}

assert_eq!(quotient(10, 2), 5);
```

The same attributes are read by the static verifier, which checks each
contract with Z3. See [`tpt-proof-mir`](../tpt-proof-mir/) and the CLI's
`verify` command.

## Interactive proofs (tactics)

[`tactics::Proof`](src/tactics.rs) builds a proof goal by goal. Each tactic
produces part of a kernel proof term. `Proof::qed` assembles the full term and
asks the kernel to check it, so a wrong tactic cannot produce a theorem: at worst
it produces a term the kernel rejects.

The available tactics are:

| Tactic | What it does |
|---|---|
| `intro(name)` | introduce an implication's premise as a hypothesis |
| `intro_forall(name)` | introduce a propositional `forall` |
| `intro_individual(name)` | introduce an individual `forall` |
| `assumption()` | close the goal with a hypothesis that matches it |
| `apply_hyp`, `apply_axiom`, `apply_theorem` | use an implication to reduce the goal to its premise |
| `exact(term)` | close the goal with a given proof term |
| `tauto()` | close a propositional goal from its hypotheses by the tautology rule |
| `auto()` | `assumption`, then `tauto` |
| `case_split()` | case analysis on an inductive sort |
| `induct()` | structural induction on an inductive sort |
| `rewrite_hyp`, `rewrite_axiom`, `rewrite_theorem` | rewrite the goal with an equation |
| `qed()` | check the completed proof with the kernel and return a `Theorem` |

`Proof::suggestions()` lists the tactics that apply to the focused goal. It is
advice only, for interactive use.

### Example

This proves modus ponens for all propositions, then records it in the kernel:

```rust
use tpt_proof::prelude::*;
use tpt_proof::tactics::Proof;

let a = Prop::atom("A");
let b = Prop::atom("B");
let kernel = Kernel::new();

let goal = Prop::forall(
    "A",
    Prop::forall(
        "B",
        Prop::imp(
            Prop::imp(a.clone(), b.clone()),
            Prop::imp(a.clone(), b.clone()),
        ),
    ),
);
let mut proof = Proof::new(&kernel, goal);
proof.intro_forall("A").unwrap();
proof.intro_forall("B").unwrap();
proof.intro("f").unwrap();
proof.intro("a").unwrap();
proof.apply_hyp("f").unwrap();
proof.assumption().unwrap();
let theorem = proof.qed().unwrap();
println!("proved: {}", theorem.prop());
```

The full version, with a kernel declaration of the proof term, an axiom, the
dependency report and a Lean export, is in
[`examples/first_proof.rs`](examples/first_proof.rs). Run it with:

```sh
cargo run -p tpt-proof --example first_proof
cargo run -p tpt-proof --example induction    # addition by recursion, then induction
```

## Lemma libraries

[`library`](src/library.rs) saves a kernel environment and its lemmas as a text
file, one S-expression per declaration, and loads it back into a fresh kernel:

- `library::save(&kernel, &lemmas)` writes the text. It loads its own output
  before returning, so a file that `save` produced always loads.
- `library::load(text)` returns the kernel, and `load_with_lemmas(text)` also
  returns the lemmas.

Loading is untrusted. Every declaration is replayed through the kernel API, and
every lemma goes through `check_proof`, so a tampered file is rejected at the
line that is wrong.

## Dependency reports

[`report::dependency_report`](src/report.rs) lists every theorem in a kernel
with its statement, the axioms it depends on, and each axiom's justification.
Use it to see what a result rests on before you trust it.

## The prelude

`tpt_proof::prelude` re-exports `tpt_proof_core::prelude`, the kernel's `Kernel`,
`ProofTerm`, `Prop` and `Theorem`, the tactic types, and the attribute macros:
`requires`, `ensures`, `invariant`, `refined`, `runtime_check` and
`state_machine`.

## Testing

```sh
cargo test -p tpt-proof                      # unit, macro, derive, tactic and library tests
```

The `tests/ui.rs` suite uses `trybuild` to check that misuse of the attributes
fails to compile with the expected message, such as a duplicate state name, an
`ensures` with a pattern binder, or a `refined` bound that is not a field.

## Where it fits

```text
tpt-proof-core ────────┐
tpt-proof-kernel ──────┤
tpt-proof-runtime ─────┼──▶ tpt-proof ──▶ tpt-proof-cli
tpt-proof-macros ──────┘
```

## Changelog

See [CHANGELOG.md](CHANGELOG.md).

## License

Licensed under either of Apache License, Version 2.0 or MIT license, at your
option. See the [root README](../../README.md#license).
