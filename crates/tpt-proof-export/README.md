# tpt-proof-export

Exports [tpt-proof](../../README.md) kernel proofs to [Lean 4](https://lean-lang.org/)
for independent checking.

The kernel is trusted, but nobody should have to trust only the kernel. This
crate writes the kernel's environment (sorts, symbols, axioms) as Lean `axiom`s,
and each lemma's proof as a Lean `theorem`. Lean then checks every proof term
again, with its own checker. A proof that Lean accepts is a second, independent
check, relative to the exported axioms.

> Status: pre-alpha, not published. The export covers a subset of the kernel's
> rules. Anything outside the subset is reported as an error, never written
> silently.

## Usage

```rust
use tpt_proof_export::{export, Lemma};

let lean_source = export(&kernel, &[
    Lemma {
        name: "modus_ponens".to_string(),
        prop: claim,         // the proposition the lemma proves
        proof: proof_term,   // the kernel proof term for it
    },
])?;
std::fs::write("lemmas.lean", lean_source)?;
```

Run `lean lemmas.lean` to check the file. The facade's
[`first_proof` example](../tpt-proof/examples/first_proof.rs) writes such a file and
checks it, and the command-line tool does the same with
`tpt-proof export <library> --out <file>`.

Only the lemmas passed to `export` are written. A proof may refer to an earlier
lemma, by `ProofTerm::Const`, but not to a kernel theorem whose proof term is not
given.

## What is exported

| Kernel item | Lean |
|---|---|
| sorts and uninterpreted symbols | global declarations |
| axioms | `axiom` declarations, with their justification as a comment |
| implication, propositional and individual quantifiers | Lean `→`, `∀` |
| equality, `refl`, `symm`, `trans`, `congruence`, `Leibniz` | `Eq`, `Eq.subst` and the corresponding lemmas |
| free propositional variables | one global `Prop` constant each, so that a name means one proposition throughout |

## Limitations

The export refuses, with `ExportError::UnsupportedRule`, the rules it cannot
translate faithfully:

- **Case analysis and induction on an inductive sort** (`ProofTerm::Cases`,
  `ProofTerm::Induct`). The sort has no Lean `casesOn` or recursor in the export.
- **Tautologies** (`ProofTerm::Taut`). The kernel decides these with a truth
  table, which has no Lean counterpart here, and the built-in integers are not
  exported as numerals.

Inductive types are not exported as Lean `inductive` declarations. Their
constructors are uninterpreted symbols, and their induction principle is an
exported axiom. So Lean does not check that the sort is freely generated. That
property is the kernel's responsibility, and the export does not add to it.

## Errors

`export` returns `ExportError`:

| Variant | Meaning |
|---|---|
| `BadName(name)` | a name contains `»`, which cannot appear in a Lean quoted identifier |
| `UnknownTheorem(name)` | a proof refers to a theorem that is not an earlier lemma |
| `UnknownAxiom(name)` | a proof refers to an axiom the kernel does not declare |
| `UnsupportedRule(rule)` | a proof uses a rule listed under Limitations |

## Testing

```sh
cargo test -p tpt-proof-export
```

`tests/lean.rs` runs the output through `lean`. It skips with a message when
`lean` is not on the PATH. Install Lean 4 with [elan](https://github.com/leanprover/elan)
to run it.

## Where it fits

```text
tpt-proof-kernel ◀── tpt-proof-export ◀── tpt-proof-cli  (export subcommand)
                                       ◀── tpt-proof       (dev-dependency, examples)
```

## Changelog

See [CHANGELOG.md](CHANGELOG.md).

## License

Licensed under either of Apache License, Version 2.0 or MIT license, at your
option. See the [root README](../../README.md#license).
