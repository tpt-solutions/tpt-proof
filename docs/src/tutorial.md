# Tutorial

This tutorial has two parts. The first verifies a Rust function against a contract with the solver. The second writes a proof that the kernel checks. They use different tools, and the second part is the stronger guarantee: it does not depend on the solver being right.

Before you start, follow the quickstart in the repository README so that `tpt-proof verify` runs.

## Part 1: a contract, a counterexample, and a fix

Write a function with a contract. The `#[requires]` and `#[ensures]` attributes are read by the verifier, and they compile to debug-build checks in ordinary builds.

```rust
#[requires(divisor != 0)]
#[ensures(|result| *result <= value)]
fn quotient(value: u32, divisor: u32) -> u32 {
    value / divisor
}
```

Run the verifier on the file. It reports one line per assertion that the MIR translation produces:

```sh
tpt-proof verify src/lib.rs
```

Now change the function so that the precondition is missing, or the postcondition is wrong. For example, drop `divisor != 0`. The verifier cannot prove that division is safe and prints a counterexample:

```text
quotient: assertion at bb0: counterexample: divisor = 0, value = 0
```

Read the counterexample as a concrete input that breaks the assertion. Either add the missing `requires` (the caller must then rule the input out), or change the body so that the input is handled. Run the verifier again until every line says the assertion is proved. The exit status is 0 only when all assertions are proved.

Two things the verifier does not do yet are worth knowing before you rely on it. It supports a subset of Rust: integer and boolean functions with straight-line code, `if`, asserts and loops with invariants. Anything else is reported by name, and never silently accepted. And its solver verdict is trusted by default. Set `TPT_PROOF_VERIFY=1` to have the kernel check the solver's proof for each `unsat` result; see [What is trusted](trusted.md).

## Part 2: a proof the kernel checks

Interactive proofs are written against a `Kernel`. You state a target proposition, apply tactics to build a proof term, and call `qed`. The kernel checks the complete term there, so a wrong tactic cannot produce a theorem.

```rust
use tpt_proof::prelude::*;

fn main() {
    let a = Prop::atom("A");
    let b = Prop::atom("B");
    let kernel = Kernel::new();

    // (A -> B) -> A -> (B -> A)
    let target = Prop::imp(
        Prop::imp(a.clone(), b.clone()),
        Prop::imp(a.clone(), Prop::imp(b.clone(), a.clone())),
    );

    let mut proof = Proof::new(&kernel, target.clone());
    proof.intro("f").unwrap();   // f : A -> B
    proof.intro("x").unwrap();   // x : A
    proof.intro("y").unwrap();   // y : B
    proof.auto().unwrap();       // closes the goal by tautology
    let theorem = proof.qed().expect("the kernel accepts the proof");
    println!("proved: {}", theorem.prop());
}
```

The goal is written in the propositional text syntax, so the same target can be written as a string:

```rust
use tpt_proof::prop;

let target = prop!("(A -> B) -> A -> B -> A");
```

Three points to take from this:

- `intro` opens an implication. It adds the hypothesis to the context and leaves the conclusion as the goal.
- `auto` tries `assumption` and then `tauto`. Both work on propositional goals only. `tauto` hands the goal to the kernel's tautology rule, which decides it by a truth table over at most 16 letters.
- If the goal is not a theorem, `auto` still succeeds, because `tauto` applies the rule without deciding it. The kernel rejects the proof at `qed`. Always call `qed` and check its result.

To look at what is left, use `proof.goals()` and `proof.suggestions()`. The suggestions are advice only: each one is a tactic that would apply to the first open goal.

## Next steps

- [Cookbook](cookbook.md) has short recipes for common tasks: quantified goals, induction, saving lemma libraries, reading the dependency report, and exporting to Lean.
- [What is trusted](trusted.md) lists exactly which parts of the system you must believe.
- `crates/tpt-proof/examples/first_proof.rs` and `induction.rs` are complete programs you can run with `cargo run -p tpt-proof --example first_proof`.
