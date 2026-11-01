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

Equality over the uninterpreted symbols is sound: every rule holds in any model where the symbols denote functions.

## Individuals and predicates

Individuals are sorted. Every term has a sort, and the default sort is `Ind`. Terms may contain individual variables `x:S`. Predicate symbols `P` with argument sorts `S1..Sn` make propositions `P(t1, ..., tn)`. Universal quantification over individuals of sort `S` is `forall x:S. A`. Equality is only between terms of one sort.

```
t ::= x | f(t1, ..., tn)
A ::= ... | P(t1, ..., tn) | forall x. A

      Γ ⊢ t : A ; D      x ∈ scope(Γ)?
  ----------------------------------------- IND-INTRO
  Γ ⊢ /\x. t : forall x. A ; D            when x is not free in Γ or in any axiom in D


  Γ ⊢ t : forall x. A ; D      s is a term in scope
  ------------------------------------------------ IND-ELIM
  Γ ⊢ t [s] : A[x := s] ; D
```

IND-INTRO has the same side condition as ALL-INTRO: a hypothesis in `Γ` or an axiom in `D` that mentions `x` makes the proof depend on one individual. Substitution `A[x := s]` renames bound individual variables when `s` contains a free variable of the same name, so instantiation does not capture.

Every individual variable must be bound by an enclosing `forall`. Axioms, theorems, and assumptions must be closed: a claim that mentions an unbound individual, or an undeclared predicate or function, is rejected.

Soundness is the standard many-sorted first-order argument for non-empty sorts. The kernel has no `exists`.

## Inductive types and induction

`declare_inductive(T, constructors)` declares a sort `T`. Each constructor `C(a1..an)` is a function symbol from its argument sorts to `T`. An argument of sort `T` is recursive.

Positivity holds automatically: constructor arguments are first-order values of declared sorts, so there are no function-typed arguments that could be non-positive.

Induction is an axiom the kernel generates for a declared predicate `P : T -> Prop`:

```
for each constructor C(a1..an):   forall a1..an. (P(ai) for each recursive ai) -> P(C(a1..an))
implies                           forall x:T. P(x)
```

**Trust assumption.** This axiom is sound only if `T` is generated freely by its constructors: every value of sort `T` is built from them. The kernel cannot prove that for an uninterpreted sort, so it is part of the trusted base. Every theorem that uses an induction axiom lists it in its dependencies, so the assumption is visible in each proof.

Not yet built: recursors and definitional equations on constructors, so functions over `T` cannot be defined in the kernel.

## Not yet in the logic

- Recursors and definitional equations for inductive types
- Leibniz substitution (`P(t)` and `t = s` give `P(s)`), which needs predicate variables
- Recursive definitions with termination checking

Each needs its own rules here before it is implemented.
