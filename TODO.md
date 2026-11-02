# tpt-proof TODO

Legend: `[ ]` todo · `[x]` done. Milestones are in **bold**. Source of truth for design: `spec.txt`.

## Decisions made

- [x] License: dual **MIT OR Apache-2.0**, copyright TPT Solutions (spec section 11 said MIT-only; update it)
- [x] Crate naming: `tpt-proof-*` (spec's `axiom-*` is renamed)
- [x] MIR access: pinned **nightly** (`rustc_private` / `stable_mir`)
- [x] Z3 integration: **shell out to the `z3` binary**, parse its proof output (no C++ linking, outside the TCB)

## Former open questions (resolved: recommendations adopted)

- [x] Kernel logic: **simply-typed lambda calculus with higher-order logic (HOL-style, LCF)**; no dependent types. Typed `Lam`/`Forall` in `ProofTerm` are consistent with this. Write up the rules in Phase 1 before coding.
- [x] Kernel has **zero external dependencies** (std only, even `dev-dependencies` kept out of the kernel crate; property tests live in a separate test crate). CI enforces it.
- [x] Z3 proof reconstruction: Z3 only *finds* certificates and its verdict is never trusted. Start with a narrow fragment (QF_LIA and QF_UF) and check certificates (e.g. Farkas coefficients) with kernel-checked rules. Anything not reconstructible is reported as `Failed`, never accepted. Research spike at the start of Phase 3 confirms feasibility.
- [x] Toolchain: pin one specific nightly date in `rust-toolchain.toml` at Phase 0 and bump deliberately. The kernel and non-MIR crates must also build on **stable** (MSRV = latest stable minus 2 releases; decide the exact number at Phase 0).
- [x] Integers: model `usize`/`u64` etc. as **bounded naturals with explicit modular ops**. Plain `+`/`-`/`*` generate overflow VCs (prove no overflow); `wrapping_*`/`checked_*` map to their own operations.
- [x] Rust-semantics axioms: **minimal, safe-subset only**. Each axiom lives in `axioms.rs` with a doc comment (statement, justification, reference to Rust reference/Miri/RustBelt). Adding one requires a dedicated PR and is recorded in `AUDIT.md`.

## Still needs you (can't be decided by me)

- [x] GitHub repo: `tpt-solutions/tpt-proof`
- [ ] Reserve crate names on crates.io (`tpt-proof`, `tpt-proof-kernel`, ...)
- [x] Second reviewer for kernel and axiom changes: requirement removed by maintainer decision. No CODEOWNERS file planned.

## Phase 0: Repo foundation

- [x] `git init`, `.gitignore`, default branch
- [x] `LICENSE-MIT`, `LICENSE-APACHE` (Apache text verified against apache.org)
- [x] `README.md` with license and contribution blurb
- [x] Copy `spec.txt` to a renamed copy and back again; update section 10 (crate names) and section 11 (licensing)
- [x] Cargo workspace root `Cargo.toml` with `license = "MIT OR Apache-2.0"`, `authors`/`repository`
- [x] `rust-toolchain.toml` pinning nightly + components (`rustc-dev`, `llvm-tools`) (stable for now; the nightly pin lands with `tpt-proof-mir` in Phase 3)
- [x] `rustfmt.toml`, `clippy` config, `deny.toml` (cargo-deny: licenses must be MIT/Apache-2.0 compatible)
- [x] CI (GitHub Actions): build, test, fmt, clippy, cargo-deny, kernel line-count check (<5,000 LOC)
- [x] `CONTRIBUTING.md` (issues only; no outside pull requests), `CODE_OF_CONDUCT.md`. `SECURITY.md` removed at maintainer request.
- [x] Per-crate `Cargo.toml` stubs for the crates listed below
- [x] `docs/` skeleton (mdBook or similar)

### Crate skeleton (`crates/`)

- [x] `tpt-proof-kernel` (the trusted kernel; also at `kernel/` with `AUDIT.md`)
- [x] `tpt-proof-core` (Layer 1: refined types, state machines, units)
- [x] `tpt-proof-contract` (Layer 2: contracts, VCs, SMT)
- [x] `tpt-proof` (Layer 3: proof DSL, tactics; the user-facing facade and prelude)
- [x] `tpt-proof-runtime` (Layer 4)
- [x] `tpt-proof-mir` (MIR analysis, translation)
- [x] `tpt-proof-cli`
- [ ] `stdlib/{collections,sync,io}`, `proofs/kernel_soundness` (directories and READMEs scaffolded; contents pending in phases 6-8). `examples/filesystem` now has code (phase 7).
- [ ] Proc-macro crate(s) for `#[refined]`, `#[requires]`, `#[theorem]`, etc. (proc macros must live in their own crate) (tpt-proof-macros: requires, ensures, runtime_check, refined, and state_machine done, with doc markers for the translator and a `tpt_proof_verify` cfg split; theorem pending)

## Phase 1: Kernel foundation

- [x] Formal write-up of the logic (syntax, typing rules, inference rules) before coding
- [x] `Type`, `Proposition`, `ProofTerm` AST (`terms.rs`)
- [x] Opaque `Theorem` type, constructible only by the kernel
- [x] Contexts, variable binding, capture-avoiding substitution
- [x] Proof checker (`checker.rs`): Var, Lam, App, Forall, Axiom, Const, TyLam, TyApp, Leibniz, and Cases (case analysis on an inductive sort, `ProofTerm::Cases`). Constructors need no proof-term form: they are term symbols, used through `Term::Fun`.
- [x] Inductive type declarations, multiple sorts, and induction axioms (positivity holds by construction: first-order arguments only; recursors pending)
- [x] Recursive function definitions: structural recursion with extra parameters via `define_by_recursion_with_params` (general termination checking pending)
- [x] Equality: refl, symm, trans, congruence, and Leibniz substitution (`ProofTerm::Leibniz`, exported to Lean as `Eq.subst`; ground terms over uninterpreted symbols)
- [x] Individual quantification (`forall x. A`), individual variables, and predicate symbols, with the generalization side condition (added beyond the original plan; see docs/design-inductive-types.md)
- [ ] Trusted axioms (`axioms.rs`): logical, equality, bounded arithmetic
- [ ] Rust-semantics axioms (safe subset only), each documented and justified
- [x] Axiom-dependency tracking per theorem
- [ ] Kernel API: `declare_axiom`, `declare_inductive`, `define_function`, `check_proof`, `assume` (declare_axiom, declare_theorem, check_proof, assume, declare_inductive, and define_function done; define_function is non-recursive and conservative, recursion goes through `define_by_recursion`)
- [x] Unit tests, property-based tests, and negative tests (bogus proofs must be rejected)
- [x] Enforce <5,000 LOC and zero deps in CI
- [x] `AUDIT.md` (scope, reviewers, status)
- [x] **Milestone: kernel checks simple proofs**
- [ ] Hand audit; publish the audit report

## Phase 2: Layer 1, type-level specs

- [x] `#[refined(...)]` attribute (e.g. `value < total_blocks`, or a literal bound): a checked `new` returning `Option` and a getter, in `tpt-proof-macros`
- [x] Compile-time checks via const eval plus simple bound queries (const-checked constructor, `Index::bound()`, and const-checked `widen` to a larger bound)
- [x] `#[state_machine(...)]` attribute: declares the states, a sealed state trait, and `transition`; the hand-written FileHandle stays as the reference
- [x] Unit-correctness types (blocks / bytes / sectors)
- [x] Ghost state and phantom type helpers
- [x] `tpt_proof::prelude`
- [ ] trybuild compile-fail tests, docs, examples (compile_fail doctests and trybuild tests for tpt-proof-core done; trybuild for the facade's derive attributes done; trybuild for the facade's contract attributes added, with a case for `ensures` misuse; trybuild for the contract crate and examples pending)
- [x] **Milestone: write and check type-level specs** (hand-written; derive macros pending)

## Phase 3: Layer 2, contracts

- [ ] Contract macros: `#[requires]`, `#[ensures]`, `#[invariant]`, `#[assert]`, `==>` operator (requires, ensures, invariant, and `==>` done; `==>` is rewritten to `!(a) || (b)` before parsing; `#[assert]` pending: a statement-level check needs a statement macro, since attributes on statements are limited on stable)
- [x] Research spike: Z3 proof-reconstruction strategy (docs/spike-proof-reconstruction.md: Z3 emits proof objects; arithmetic steps are the hard part; no checker yet)
- [ ] MIR extraction (`tpt-proof-mir`): desugar, monomorphize, resolve ownership (done for integer and bool functions with straight-line code, `if`, and asserts: MIR asserts become VCs checked by Z3, and each unsupported construct is reported. Contracts `requires` and `ensures` are read from doc markers and checked; loops with line-anchored `#[invariant(line, cond)]` are checked with the entry, havoc, and preservation rule; generic calls and mutable references are pending; shared references to scalars are supported (a reference is modelled by its pointee, sound by rustc's borrow check); signed division and remainder use Rust truncation, checked against concrete values; direct calls use callee contracts as summaries, which are assumed on the callee's own verification; unsigned division and remainder, and multiplication with overflow checks, are supported)
- [x] Verifiable subset enforcement: unsupported constructs are reported by name, never verified (integer and bool subset only; see the MIR crate)
- [ ] Ownership/borrow model (linear resources, loans): phase 1 (shared references to scalars) done; phase 2 (mutable references) designed in docs/design-ownership-phase2.md, awaiting review
- [ ] VC generation (`vc.rs`): weakest precondition, loops via invariants, overflow/bounds checks (WP, loop havoc, and range (overflow) obligations done; array bounds pending; source language is a model, not MIR)
- [x] SMT-LIB encoding and `z3` subprocess driver (timeouts, resource limits) (verified against z3 5.3.3: the 3 ignored solver tests pass with `cargo test -- --ignored`)
- [ ] Proof-producing reflection: convert Z3 output to kernel proof terms; fail if not checkable
- [x] Counterexample extraction and reporting (model parsed into name-value pairs and printed by the driver)
- [ ] Result states: Verified / Unverified / Failed / Timeout, never silent fallback (Outcome done; Verified is unreachable until proof reflection exists)
- [x] Caching and incremental verification (VC result cache keyed by encoded script and timeout; TPT_PROOF_CACHE selects a directory; unsat and counterexample results only)
- [ ] `tpt-proof-cli` (`cargo tpt-proof verify`), diagnostics UX (`tpt-proof verify <file>` runs the MIR driver; the driver needs the nightly runtime environment, so it works under cargo, not as a bare binary yet)
- [ ] **Milestone: verify simple function contracts**

## Phase 4: Layer 3, interactive proofs

- [ ] DSL macros: `#[theorem]`, `#[lemma]`, `arbitrary()`, `assume()`, `show()`, `by {}` (not started: needs the proc-macro crate; tactics are the Rust API for now)
- [ ] Tactic framework (untrusted): `case_split`, `apply`, `induct`, `simplify`, ... (intro, intro_forall, apply_*, assumption, exact, case_split, and rewrite (`rewrite_hyp`, `rewrite_axiom`, `rewrite_theorem`: directed rewriting by an equation, built on Leibniz substitution) done. `simplify` is read as a strategy that applies a rule set of rewrites, and is not built; `induct` is pending, because it needs predicate abstraction over the goal, which the kernel's induction axioms do not yet support)
- [x] Each tactic step emits a proof term that the kernel checks
- [x] Interactive mode: goal display and suggested next steps (`Proof::suggestions` lists the tactics that apply to the focused goal: intro, intro_forall, assumption, apply_hyp/axiom/theorem; advice only)
- [x] Dependency/axiom reports (`tpt_proof::report::dependency_report`: each theorem, its axioms, and their justifications)
- [x] Lemma library: `tpt_proof::library::{save, load}` write a kernel environment and its lemmas as S-expressions, and load them into a fresh kernel. Loading is untrusted: every declaration is replayed through the kernel API and every lemma goes through `check_proof`. `save` loads its own output before returning it. Theorems not passed to `save` are not saved, and definitions by recursion are saved as their generated axioms.
- [x] **Milestone: write and check interactive proofs** (via the tactics API)

## Phase 5: Layer 4, runtime verification

- [x] `#[runtime_check]` and spec-to-assertion compilation (debug builds only, zero release cost) (runtime_check! macro done; attribute form needs a proc-macro crate) (attribute form done via tpt-proof-macros; spec.txt example semantics)
- [x] proptest integration: `tpt_proof_runtime::property::check` behind the `proptest` feature (quickcheck not added)
- [x] Counterexample replay: `tpt_proof_runtime::replay::run` calls a function under solver-chosen inputs and reports `Confirmed` (a contract failed), `Panicked` or `Passed`. Replay in release builds reports `Passed`, because contracts are debug assertions.
- [ ] **Milestone: debug verification failures at runtime**

## Phase 6: Standard library

- [ ] Verified B-Tree
- [ ] Verified HashMap
- [ ] Verified Vec extensions
- [ ] Verified concurrency primitives (Mutex model; atomics later)
- [ ] I/O abstractions
- [ ] **Milestone: verified standard library**

## Phase 7: Filesystem integration

- [x] Wire up `examples/filesystem` against `tpt-filesystem`: a standalone crate pinned to tpt-filesystem commit `cfbb1aa`, kept out of the root workspace so its dependencies stay out of the license audit
- [x] Layer 1 types: `BlockRef` (`#[refined(block < total)]`) for block indices, and `Blocks`/`Bytes` for sizes, in `examples/filesystem`
- [ ] Layer 2 contracts on most functions
- [ ] Layer 3 proofs: B-Tree balance, CoW atomicity, transaction isolation
- [ ] **Milestone: filesystem has genuine mathematical guarantees**

## Phase 8: Self-verification

- [ ] Verify parts of the translation layer with tpt-proof
- [x] Export proofs to Lean 4 for independent checking: `tpt-proof-export` writes the kernel's environment and each lemma's proof term as Lean; `lean` accepts the five test lemmas (`cargo test -p tpt-proof-export -- --ignored`, needs `lean` on PATH). Coq not started. Inductive types are exported as uninterpreted symbols plus their induction axioms, not as Lean `inductive`s.
- [ ] `proofs/kernel_soundness`
- [ ] **Milestone: framework self-verified to the extent possible**

## Later: extended Rust subset

- [ ] Phase 2 subset: closures, monomorphized generics, simple `unsafe` with proof obligations, mutexes/atomics
- [ ] Phase 3 subset: full safe Rust, complex `unsafe`, lock-free structures
- [ ] Concurrency logic (concurrent separation logic or session types)

## Ongoing

- [ ] Fuzzing and differential testing against Kani/Creusot
- [ ] Benchmarks (target: seconds for most verification) (kernel and contract-level Z3 timings in docs/benchmarks.md; translator-fixture and end-to-end timings pending)
- [ ] User docs, tutorials, error-message quality
- [ ] Success-criteria review (spec section 14)
