# tpt-proof-kernel

The trusted proof kernel for [tpt-proof](../../README.md). It checks proofs of
propositions over sorted individuals and reports which axioms each checked
theorem depends on.

This crate is the trusted computing base (TCB) of the framework. Nothing else in
tpt-proof can produce a `Theorem`: the solver, the tactics, the Z3 proof
reconstruction and the Lean export are all untrusted, and each of them hands its
result to this crate to be checked. If the kernel accepts a term, the term proves
the claimed proposition, given the axioms it lists.

> Status: pre-alpha. The kernel checks simple and medium-sized proofs, and its
> soundness has been reviewed only by its author. `kernel/AUDIT.md` records the
> scope and the review status; the hand audit has not been done.

## Guarantees

- **No external dependencies.** The crate depends on the standard library only,
  and its `dev-dependencies` are empty too. Property tests use a small fixed-seed
  generator, not `proptest`. CI fails if a dependency is added.
- **No `unsafe` code.** The crate has `#![forbid(unsafe_code)]`.
- **Opaque theorems.** The only way to get a [`Theorem`] is
  `Kernel::check_proof`, so a `Theorem` value is evidence that the kernel checked
  its proof term.
- **Explicit axioms.** Every axiom is declared with a proposition and a written
  justification. Each theorem records the axioms it uses, and
  `Theorem::axioms()` returns them.
- **Small size.** CI enforces a line-count limit on the kernel (spec.txt §2).

The kernel is classical. The tautology rule decides formulas by truth table, so
`not not a -> a` is provable without an excluded-middle axiom. Read
[`docs/kernel-logic.md`](../../docs/kernel-logic.md) for the logic, and
[`kernel/AUDIT.md`](../../kernel/AUDIT.md) for what has been reviewed.

## The logic

Propositions ([`Prop`]) are:

| Form | Meaning |
|---|---|
| `Prop::atom("A")` | a propositional letter |
| `Prop::imp(a, b)` | implication |
| `Prop::forall("A", p)` | quantification over propositions |
| `Prop::forall_sorted("x", sort, p)` | quantification over individuals of a sort |
| `Prop::Eq(t, s)` | equality of two terms of one sort |
| `Prop::Pred(name, args)` | a predicate symbol applied to terms |

Individuals are sorted. The built-in sort `Int` has `+`, `-`, `*`, `neg`, `<=`
and `<`, and numerals such as `"42"`. Other sorts and their function symbols are
declared with `declare_sort`, `declare_function_sorted` and `declare_inductive`.

Formulas with `and`, `or`, `not`, `iff`, `true` and `false` are encoded into
propositions in [`formula`]. A formula is closed by the tautology rule, which
checks it under every valuation of its letters.

A proof is a [`ProofTerm`]: a term whose type is the proposition it proves
(Curry-Howard). The rules are:

- **Propositional:** `Var`, `Lam`, `App`, `Axiom`, `Const` (a previously declared
  theorem), `Atom`.
- **Taut:** `Taut(Formula)`, the tautology rule, for at most 16 letters. Ground
  atoms are evaluated with the built-in integers (see `arith`), so a true
  arithmetic fact such as `2 < 3` needs no letter of its own.
- **Second-order:** `TyLam`, `TyApp`, the quantifier over propositions.
- **First-order:** `IndLam`, `IndApp`, the quantifier over individuals, with the
  generalization side condition checked.
- **Equality:** `Refl`, `Sym`, `Trans`, `Cong` (congruence) and `Leibniz`
  (substitution of equals).
- **Inductive types:** `Cases` (case analysis) and `Induct` (structural
  induction), one premise per constructor.

## Example

This is the smallest useful kernel session: declare an axiom, then check a proof
that uses it. The facade crate's [`first_proof` example](../tpt-proof/examples/first_proof.rs)
does the same through tactics and writes the Lean export.

```rust
use tpt_proof_kernel::terms::{Sort, Term};
use tpt_proof_kernel::{Kernel, Prop, ProofTerm};

let mut kernel = Kernel::new();

// Axiom: adding zero changes no integer.
let x = Term::var("x");
let add_zero = Prop::forall_sorted(
    "x",
    Sort::named("Int"),
    Prop::Eq(Term::Fun("+".into(), vec![x.clone(), Term::constant("0")]), x),
);
kernel
    .declare_axiom("add_zero", add_zero, "adding zero changes no integer")
    .unwrap();

// Theorem: 2 + 0 = 2, by instantiating the axiom at 2.
let claim = Prop::Eq(
    Term::Fun("+".into(), vec![Term::constant("2"), Term::constant("0")]),
    Term::constant("2"),
);
let proof = ProofTerm::IndApp(
    Box::new(ProofTerm::Axiom("add_zero".into())),
    Term::constant("2"),
);
let theorem = kernel.check_proof(&proof, &claim).unwrap();
assert!(theorem.axioms().contains("add_zero"));
```

To keep a proof, use `declare_theorem(name, &term, &claim)`. A later proof can
refer to it with `ProofTerm::Const(name)`.

## Definitions and recursion

- `define_function` adds a non-recursive definition as one conservative equation
  over a fresh symbol. The equation is recorded as an axiom named `<symbol>_def`.
- `define_by_recursion` and `define_by_recursion_with_params` define a function by
  structural recursion on an inductive sort: one defining equation per
  constructor, with recursive calls only on recursive arguments. The first
  argument is the structural one in the `with_params` form.
- General termination checking is not implemented. Only structural recursion is
  accepted.

## Errors

Every operation that can fail returns `Result<_, KernelError>`. The variants say
what was wrong with the proof, for example an unbound variable, an individual
used outside the `forall` that binds it, a reserved name used as a binder, or a
proposition that does not match the claim. Reserved names (`false`, `#r`, the
built-in integers and their operators) cannot be bound, declared or used as
constructors; see the changelog for the soundness fix that added this check.

## Testing and benchmarks

```sh
cargo test -p tpt-proof-kernel           # unit, property and negative tests
cargo bench -p tpt-proof-kernel          # timing of chains of modus ponens and nested proofs
```

The test suite includes negative tests: bogus proofs must be rejected, and
`reserved_names.rs` covers the soundness fix for reserved names. The property
tests (`property.rs`, `taut_property.rs`) use fixed seeds, so every run is
reproducible.

Tests that need `lean` skip with a message when it is not on the PATH. The
helper that detects tools is `tests-support/tools.rs`.

## Where the kernel fits

```text
tpt-proof-kernel   (no dependencies)
  ├── tpt-proof-contract   Z3 proof reconstruction calls check_proof
  ├── tpt-proof-export     exports kernel theorems and proof terms to Lean 4
  └── tpt-proof            the facade: tactics and lemma libraries
```

## Changelog

See [CHANGELOG.md](CHANGELOG.md).

## License

Licensed under either of Apache License, Version 2.0 or MIT license, at your
option. See the [root README](../../README.md#license).
