# Kernel Logic Write-up

This is the formal description of the kernel's logic, written before the checker was implemented (TODO.md, Phase 1). The implementation is in [crates/tpt-proof-kernel](../crates/tpt-proof-kernel). If the two disagree, the kernel is wrong until this document is fixed.

## Syntax

Propositions (types):

```
A, B ::= p          atomic proposition or propositional variable
       | A -> B     implication
       | forall p. A   universal quantification over a propositional variable
```

Proof terms:

```
t ::= x              variable
    | c              theorem constant
    | ax             axiom
    | \x:A. t        implication introduction
    | t1 t2          implication elimination
    | /\p. t         universal introduction (Λp)
    | t [A]          universal elimination (instantiation at A)
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


  Γ ⊢ t : B ; D     p ∉ FV(Γ)     ∀ax ∈ D. p ∉ FV(prop(ax))
  ----------------------------------------------------------- ALL-INTRO
  Γ ⊢ /\p. t : forall p. B ; D


  Γ ⊢ t : forall p. B ; D
  ------------------------------- ALL-ELIM
  Γ ⊢ t [A] : B[p := A] ; D
```

The side condition on ALL-INTRO is what keeps quantification sound. The proof may use only hypotheses and axioms that do not mention `p`, so the proof works for every choice of `p`. Without it, the axiom `A` would give `forall A. A`. The substitution `B[p := A]` renames bound variables when needed to avoid capturing free variables in `A`. Propositions are compared up to renaming of bound variables.

## Checking a claim

`check(t, A)` succeeds if and only if `∅ ⊢ t : A ; D` for some `D`. The result is a `Theorem` for `A` with dependency set `D`. The claimed proposition must match the inferred one exactly, with no coercion.

## Assumptions

`assume(A)` adds a fresh axiom `assumption#n : A` to `Σ` and returns a theorem for `A` with dependency `{assumption#n}`. Assumptions cannot be hidden: any theorem that uses one lists it.

## Soundness argument (informal)

1. Every `Theorem` value is produced by `check`, the only constructor, which applies the rules above.
2. The rules are the standard natural-deduction rules for implication, restricted to the simply-typed fragment. Each rule preserves truth when its premises hold.
3. Axioms and assumptions are the only non-derived facts. Their names appear in every dependent theorem, so a theorem depending on `D` is valid whenever the axioms in `D` are.

Formal proof of (2) and (3) is the Phase 8 target (`proofs/kernel_soundness`).

## Equality

Terms are applications of uninterpreted function symbols: `f(t1, ..., tn)`. A constant is a symbol of arity zero. Every symbol used in a term or proof must be declared with its arity. Equality between two ground terms is a proposition, `t = s`.

```
t ::= f(t1, ..., tn)          (f declared with arity n)
A ::= ... | t = s

t = t                      REFL       proof: Refl(t)
t = s  ⊢  s = t            SYM        proof: Sym(p)
t = s,  s = u  ⊢  t = u    TRANS      proof: Trans(p, q)
t1 = s1, ..., tn = sn  ⊢  f(t1..tn) = f(s1..sn)   CONG   proof: Cong(f, [p1..pn])
```

TRANS requires the two middle terms to be identical. CONG requires every argument proof to prove an equality, and checks the arity of `f`. An equality mentions no propositional variable, so ALL-INTRO's side condition is unaffected by it.

Equality over the uninterpreted symbols is sound: every rule holds in any model where the symbols denote functions. This only reasons about ground terms. There are no individual variables yet, so nothing is quantified over individuals.

## Not yet in the logic

- Quantification over individuals (terms of a domain such as `usize`)
- Leibniz substitution (`p(t)` and `t = s` give `p(s)`), which needs predicate abstraction
- Inductive types, constructors, and pattern matching
- Recursive definitions with termination checking

Each needs its own rules here before it is implemented.
