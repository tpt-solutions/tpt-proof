# Kernel Logic Write-up

This is the formal description of the kernel's logic, written before the checker was implemented (TODO.md, Phase 1). The implementation is in [crates/tpt-proof-kernel](../crates/tpt-proof-kernel). If the two disagree, the kernel is wrong until this document is fixed.

## Syntax

Propositions (types):

```
A, B ::= p          atomic proposition (p a name)
       | A -> B     implication
```

Proof terms:

```
t ::= x              variable
    | c              theorem constant
    | ax             axiom
    | \x:A. t        implication introduction
    | t1 t2          implication elimination
```

## Judgments

- `Γ ⊢ t : A` means term `t` proves proposition `A` under local context `Γ`.
- `Γ` is a list of `x : A` bindings. Later bindings shadow earlier ones.
- `Σ` is the global environment of axioms `ax : A` and checked theorems `c : A`.
- Each judgment also computes a dependency set `D`, the names of axioms used.

## Rules

```
  (x : A) ∈ Γ                         (ax : A) ∈ Σ
  ------------------ VAR              ------------------ AXIOM
  Γ ⊢ x : A ; ∅                       Γ ⊢ ax : A ; {ax}


  (c : A ; D) ∈ Σ                     Γ, x:A ⊢ t : B ; D
  ----------------------- CONST      ---------------------------- IMP-INTRO
  Γ ⊢ c : A ; D                       Γ ⊢ \x:A. t : A -> B ; D


  Γ ⊢ t1 : A -> B ; D1     Γ ⊢ t2 : A ; D2
  ------------------------------------------- IMP-ELIM
  Γ ⊢ t1 t2 : B ; D1 ∪ D2
```

## Checking a claim

`check(t, A)` succeeds if and only if `∅ ⊢ t : A ; D` for some `D`. The result is a `Theorem` for `A` with dependency set `D`. The claimed proposition must match the inferred one exactly, with no coercion.

## Assumptions

`assume(A)` adds a fresh axiom `assumption#n : A` to `Σ` and returns a theorem for `A` with dependency `{assumption#n}`. Assumptions cannot be hidden: any theorem that uses one lists it.

## Soundness argument (informal)

1. Every `Theorem` value is produced by `check`, the only constructor, which applies the rules above.
2. The rules are the standard natural-deduction rules for implication, restricted to the simply-typed fragment. Each rule preserves truth when its premises hold.
3. Axioms and assumptions are the only non-derived facts. Their names appear in every dependent theorem, so a theorem depending on `D` is valid whenever the axioms in `D` are.

Formal proof of (2) and (3) is the Phase 8 target (`proofs/kernel_soundness`).

## Not yet in the logic

- Universal quantification and its rules
- Inductive types, constructors, and pattern matching
- Recursive definitions with termination checking
- Equality and its axioms

Each needs its own rules here before it is implemented.
