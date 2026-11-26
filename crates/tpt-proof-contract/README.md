# tpt-proof-contract

Layer 2 of [tpt-proof](../../README.md): contract-based verification. It takes
verification conditions (VCs), which are logical formulas that a function's
contract reduces to, and decides them with the Z3 SMT solver.

This crate does the solving. It does not parse Rust. The MIR translator in
[`tpt-proof-mir`](../tpt-proof-mir/) turns a function into VCs, and this crate
checks them. Two things are kept apart:

- **Solver `unsat`** means Z3 says the negated goal has no model. That is a
  claim by an untrusted program.
- **Verified** means Z3 produced a proof and the [kernel](../tpt-proof-kernel/)
  checked it. Only this result is reported as `Outcome::Verified`.

> Status: pre-alpha. The pipeline works for the integer and boolean subset that
> the MIR translator supports. Proof reconstruction covers part of what Z3 emits;
> the rest is reported as `Unchecked`, never as verified.

## The pipeline

```text
Vc ──encode──▶ SMT-LIB script ──z3──▶ sat / unsat / unknown / timeout
                                          │
                 check (solver answer) ◀──┤
                                          │
                 verify (proof mode) ◀────┘  z3 -proof, then reflect::reconstruct
                                              into kernel proof terms, then check_proof
```

| Entry point | What it reports |
|---|---|
| `smt::check` | `SolverUnsat` when Z3 answers `unsat`; never `Verified`. |
| `smt::verify` | `Verified` only when the kernel accepts Z3's proof. `Unchecked` when the solver says `unsat` but the proof is not accepted. |

Both report `Failed` with the counterexample model when Z3 answers `sat`, and
`Timeout` or `Unknown` when it gives up.

## The types

- **`Vc`** (`vc`): a name for reports, the declared variables with their sorts
  (`Sort::Int` or `Sort::Bool`), assumptions, and a goal.
- **`Expr`** (`vc`): integer and boolean terms and formulas: literals, `Var`,
  `Add`, `Sub`, `Mul`, `Div`, `Rem`, `Ite`, `Lt`, `Le`, `Eq`, `Not`, `And`,
  `Or`, `Implies`. Division and remainder are only for non-negative operands;
  the translator adds Rust's truncation rules itself. Non-linear `Mul` is harder
  for the solver and may come back `unknown`.
- **`Outcome`** (crate root): `SolverUnsat`, `Verified`, `Unchecked { reason }`,
  `Failed { counterexample }`, `Timeout`, `Unknown(reason)`.
- **`SolverConfig`** (`smt`): the path to `z3` and a per-query timeout in
  milliseconds. `SolverConfig::from_lookup` reads `TPT_PROOF_Z3` and
  `TPT_PROOF_TIMEOUT_MS`, with defaults for unset names.

## Example

```rust
use tpt_proof_contract::{check, Expr, Outcome, Sort, SolverConfig, Vc};

// Goal: if 0 <= x, then 0 <= x + 1.
let x = || Box::new(Expr::Var("x".into()));
let vc = Vc {
    name: "increment keeps x non-negative".into(),
    vars: vec![("x".into(), Sort::Int)],
    assumptions: vec![Expr::Le(Box::new(Expr::Int(0)), x())],
    goal: Expr::Le(
        Box::new(Expr::Int(0)),
        Box::new(Expr::Add(x(), Box::new(Expr::Int(1)))),
    ),
};

let config = SolverConfig::from_lookup(|name| std::env::var(name).ok())
    .expect("the solver settings are valid");
match check(&vc, &config) {
    Outcome::SolverUnsat => println!("proved by the solver (not kernel-checked)"),
    other => println!("not proved: {other:?}"),
}
```

Use `smt::verify` instead of `check` to ask for a kernel-checked result. It runs
Z3 in proof mode, which is slower and does not use the cache.

## Function-level conditions

`wp::generate` takes a small imperative `Function` (`Stmt::{Assign, Assert,
Assume, If, While}`, with `requires`, `ensures` and integer `ranges`) and returns
one `Vc` per postcondition. It uses weakest preconditions. A loop needs an
invariant, which must hold on entry and be preserved by the body. Range entries
model fixed-width integers: an assignment that leaves the range is an obligation.

The MIR translator does its own walk over real MIR, but the same rules apply.

## Contract expressions

`spec::parse` reads the text of a `requires` or `ensures` clause into an `Expr`.
The language is Rust-like: integer and boolean literals, comparisons, `&&`, `||`,
`!`, unary and binary `+` and `-`, parentheses, and names that are parameters.
A leading `*` on a name is accepted and ignored, so `*result` reads the same as
the closure form used by the macros.

## Proof reconstruction

`reflect::reconstruct` reads the proof object that Z3 prints and builds kernel
proof terms for it. The kernel then checks the whole term against the claim. A
step that is not translated makes the whole result `Unchecked`.

Covered: asserted hypotheses, propositional steps, rewrites that are tautologies
or axiom instances, `symm`, `trans`, `refl`, monotonicity over connectives and
integer comparisons, congruence, commutativity, and named terms.

Not covered yet: `th-lemma` steps (Farkas certificates for linear arithmetic),
Z3's arithmetic normalization (for example `x - y` to `x + (-1) * y`), and `ite`,
`div` and `mod`. The research behind reconstruction is in
[`docs/spike-proof-reconstruction.md`](../../docs/spike-proof-reconstruction.md).

## Caching

`cache::VcCache` stores solver results keyed by the encoded SMT-LIB script and
the timeout, hashed with FNV-1a. The hash is stable across runs and toolchains.
Only deterministic results are stored: `unsat` and counterexamples. Timeouts and
`unknown` answers are never cached, because a later run may answer differently.

`VcCache::in_directory` stores results on disk, and `VcCache::in_memory` keeps
them for one process. The verification driver uses the directory named by
`TPT_PROOF_CACHE`. Proof mode bypasses the cache.

## Solver settings

| Variable | Meaning | Default |
|---|---|---|
| `TPT_PROOF_Z3` | path to the `z3` executable | `z3` on the PATH |
| `TPT_PROOF_TIMEOUT_MS` | per-query timeout | 10000 |

The solver is untrusted, and a wrong answer from it is caught by the kernel in
proof mode. The solver process is killed after its timeout plus five seconds, so
a hung `z3` cannot block verification.

## Testing

```sh
cargo test -p tpt-proof-contract                  # encoding, WP, reflection, parser
cargo run -p tpt-proof-contract --example z3_timing   # Z3 timings for contract VCs
```

Tests that need `z3` skip with a message when it is not installed. Install Z3
from [its releases](https://github.com/Z3Prover/z3/releases) and put it on the
PATH, or set `TPT_PROOF_Z3`.

## Where it fits

```text
tpt-proof-kernel ◀── tpt-proof-contract ◀── tpt-proof-mir (driver)
                                       ◀── tpt-proof-cli (through the driver)
```

## Changelog

See [CHANGELOG.md](CHANGELOG.md).

## License

Licensed under either of Apache License, Version 2.0 or MIT license, at your
option. See the [root README](../../README.md#license).
