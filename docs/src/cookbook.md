# Cookbook

Short recipes for common tasks. Each one is a test in `crates/tpt-proof/tests/docs_examples.rs`, so the code here compiles and runs as written.

## Write a propositional goal as text

Use `prop!` for a literal, or `tpt_proof::prop::parse` for text read at runtime. Connectives are `->` (right-associative) and `forall p. ...` over propositional variables. `false` is the constant false.

```rust
use tpt_proof::prelude::*;
use tpt_proof::prop;

let kernel = Kernel::new();
let mut proof = Proof::new(&kernel, prop!("A -> B -> A"));
proof.intro("a").unwrap();
proof.intro("b").unwrap();
proof.auto().unwrap();      // assumption closes it
let theorem = proof.qed().unwrap();
```

A malformed literal panics at the call site with the parse error. Use `parse` when the input comes from outside the program, and handle its `Err`.

## Close a goal by tautology

`tauto` works on any goal and its hypotheses built from implications, `false` and atoms. It hands the whole statement to the kernel's tautology rule, which decides it by a truth table over at most 16 letters.

```rust
// (A -> B) -> (B -> C) -> A -> C
let mut proof = Proof::new(&kernel, prop!("(A -> B) -> (B -> C) -> A -> C"));
for name in ["f", "g", "a"] {
    proof.intro(name).unwrap();
}
proof.tauto().unwrap();
proof.qed().unwrap();
```

`auto` is the same plus `assumption` first, so use it when you are not sure whether the goal is already a hypothesis. Neither tactic introduces binders: call `intro` first.

## Introduce a universal quantifier

From `forall p. B`, `intro_forall` leaves `B` with `p` in scope. From `forall x:S. B` over individuals of a sort, use `intro_individual`.

```rust
let mut proof = Proof::new(&kernel, prop!("forall p. p -> p"));
proof.intro_forall("p").unwrap();
proof.intro("h").unwrap();
proof.assumption().unwrap();
proof.qed().unwrap();
```

## Use an axiom, and record the result

Declare an axiom with a justification, so the dependency report can say why it is trusted. Then prove something with it and record the theorem, so later proofs can refer to it by name.

```rust
let mut kernel = Kernel::new();
kernel
    .declare_axiom("ax_a", prop!("A"), "A is taken as given in this example")
    .unwrap();

let mut proof = Proof::new(&kernel, prop!("A"));
proof.exact(ProofTerm::Axiom("ax_a".to_string())).unwrap();
proof.qed().unwrap();
kernel
    .declare_theorem("a_holds", &ProofTerm::Axiom("ax_a".into()), &prop!("A"))
    .unwrap();
```

`exact` closes the goal with a proof term you already have. `apply_axiom` and `apply_theorem` instead take an implication `A -> B` from the environment and leave `A` as the new goal.

## Save and load a lemma library

A library is text: the declarations, and each lemma with its proof term. Loading is untrusted. Every declaration is replayed through the kernel and every lemma is checked again, so a damaged file fails to load rather than adding a false theorem.

```rust
use tpt_proof::library::{self, Lemma};

let mut kernel = Kernel::new();
let proof_term = ProofTerm::Axiom("ax_a".into());
// ... declare the axiom and check the proof as above ...
let lemmas = vec![Lemma {
    name: "a_holds".into(),
    prop: prop!("A"),
    proof: proof_term,
}];
let text = library::save(&kernel, &lemmas).unwrap();   // loads its own output before returning
let (reloaded, reloaded_lemmas) = library::load_with_lemmas(&text).unwrap();
```

Only theorems passed to `save` are written. `library::load` returns just the kernel when you do not need the lemmas.

## Read the dependency report

For every theorem, the report lists the axioms it depends on and their justifications. This is the first thing to read when reviewing a library.

```rust
use tpt_proof::report::dependency_report;

print!("{}", dependency_report(&kernel));
```

## Export lemmas to Lean

`tpt_proof_export::export` writes the kernel's environment and each lemma's proof term as Lean, so that `lean` can check them without trusting this kernel. Inductive types are exported as uninterpreted symbols with their induction axioms, not as Lean `inductive` declarations, and induction proofs are not exported yet.

```rust
use tpt_proof_export::{export, Lemma as ExportLemma};

let lean = export(&kernel, &[ExportLemma {
    name: "a_holds".into(),
    prop: prop!("A"),
    proof: ProofTerm::Axiom("ax_a".into()),
}]).unwrap();
```

From the command line, `tpt-proof export <library> [--out <file>]` does the same for a saved library. Check the result with `lean`, which `tpt-proof doctor` reports on.

## Check a solver result against the kernel

`tpt-proof verify` trusts the solver's `unsat` answer by default. Set `TPT_PROOF_VERIFY=1` and the MIR driver asks the solver for a proof and has the kernel check it. A result the kernel does not accept is reported as `Unchecked`, not as verified. The cost is speed: the proof path does not use the VC cache. See [What is trusted](trusted.md).
