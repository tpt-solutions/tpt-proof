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
2. The rules are the standard natural-deduction rules for implication and quantification, with the equality, individual, and inductive rules above. Each rule preserves truth when its premises hold. The tautology rule is the one trusted primitive beyond these, and it makes the logic classical (see the section on it).
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

Structural recursion: `define_by_recursion(f, T, R, cases)` defines `f : T -> R` with one case per constructor. Inside a case, recursive calls must be written `f(a_j)` on a recursive argument `a_j`, and nothing else may call `f`. The kernel checks the cases and generates one defining equation per constructor, `forall a. f(C(a)) = body`, as an axiom named `f_C`.

This is a conservative extension. Each equation fixes `f` on one constructor, and every recursive call is on a structurally smaller argument, so it adds no contradiction. A model is the term algebra of the constructors, which satisfies every equation, so the extension is consistent without the induction assumption. A rejected definition is rolled back and leaves no symbol behind.

## Leibniz substitution, case analysis, and induction

These are primitive rules of the checker, not axioms.

- **Leibniz** (`Leibniz`): from `t = s` and a motive `P[x := t]` that matches exactly, derive `P[x := s]`. It uses only the equality rules above.
- **Cases** and **Induct** (`Cases`, `Induct`): on a declared inductive sort `T`, one premise per constructor `C(a1..an)`. `Cases` gives no hypotheses for recursive arguments. `Induct` gives a hypothesis `P(aj)` for each recursive `aj`. The conclusion is `forall x:T. P(x)`, and the side condition of IND-INTRO applies. Both are sound only under the trust assumption above, that `T` is generated freely by its constructors.

## The tautology rule and classical logic

`Taut(F)` proves a formula `F` built from atoms, `false`, and `true` with `not`, `and`, `or`, `iff`, and `->`. The kernel first encodes `F` as a proposition: `not a` is `a -> false`, `and` and `or` are second-order encodings over a bound variable `#r`, and `iff` is two implications. It then accepts `F` only when a truth table over the letters of `F` makes it true. A letter is a non-ground atom. A ground atom is evaluated with the built-in integers, and the atom `false` is the constant false.

The rule makes the logic classical: `not not a -> a` is accepted with no excluded-middle axiom. It is trusted, together with the encodings and the integer evaluation. A formula may have at most 16 letters. Its atoms are checked with no individual variables in scope, so `Taut` cannot be used under an individual binder (`IndLam`, or a `Cases` or `Induct` premise that refers to the bound variable); instantiate the binder first, then apply the rule. This is a limit on what is accepted, not a gap in soundness.

The truth table must not be fooled by binders. The atom `false` and the name `#r` are reserved, so a proof cannot generalize over them (`TyLam`, `IndLam`), and a `Taut` atom cannot mention `#r`. Without these checks, `forall false. (false -> q)` could be instantiated at a true proposition and yield `q`. Numerals and the other built-in names are also reserved, and cannot be declared as symbols or constructors.

## Built-in integers

The sort `Int`, the numerals, `+`, `-`, `*`, `neg`, `<=`, and `<` are declared by the kernel with their usual meaning, and no axioms about them are declared. `axioms::declare_standard` adds a fixed list of integer axioms, and a caller opts in to them. The axioms are listed in `kernel/AUDIT.md`.

## Not yet in the logic

- Termination checking beyond structural recursion
- Bounded (modular) integer arithmetic
- Rust-semantics axioms

Each needs its own rules here before it is implemented.
