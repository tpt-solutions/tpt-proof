# Design: Ownership and References in the MIR Translator

Status: **phase 1 implemented** (shared references to scalars, approved). Phase 2 (mutable references) is still a proposal. It follows spec.txt §5 ("Handling Ownership and Borrowing").

## What the translator supports now

Integer and bool locals and parameters, and shared references (`&T`, `&&T`) to them, with no `UnsafeCell`. Reads through a shared reference, and shared borrows of scalar places, are translated. Mutable references, other projections, and non-scalar values are reported as unsupported.

## What the design has to answer

1. What a reference means in the VC language.
2. How moves and copies of scalars are modelled.
3. How much of Rust's ownership and borrowing the verifier must itself check, and how much it can take from rustc.
4. What `ensures` can say about a reference result.

## Trust decision: borrow checking stays with rustc

rustc's borrow checker already rejects every program where a reference outlives its referent or where a mutable and a shared borrow overlap. The translator runs only on code that compiled. It should rely on that, not re-prove lifetimes. This keeps the translator smaller, and it means the trusted base for ownership is the Rust compiler, which spec.txt §7 already trusts.

The translator must not rely on anything rustc does not guarantee, such as the absence of interior mutability. It rejects types with `UnsafeCell` (directly or through a field) so that the "no change while shared" argument holds.

## Phase 1: shared references to scalars

Supported:
- Parameters and locals of type `&T` and `&&T`, where `T` is an integer or bool, with no `UnsafeCell`.
- `Deref` projections on such references, read as the pointee value.
- `&x` borrows of scalar locals, and reborrows.
- Moves and copies of scalars and references. A move of a scalar is a copy.

Model. A shared reference is represented by its pointee value. A parameter `r: &u8` becomes a variable `_1` of sort Int with the range of `u8`, read through `*r` as `_1`. A `&x` borrow, where `x` is a local that is not mutated while the borrow is live, has the value of `x` at the borrow point. rustc's borrow checker guarantees the first condition, so the translator can take the value at the borrow without tracking aliasing.

What this gives: `fn f(x: &u8) -> u8 { *x + 1 }` is checked with the same overflow VC as `fn f(x: u8) -> u8 { x + 1 }`, and `ensures` can talk about `*result`.

## Phase 2: mutable references (not proposed in detail yet)

`&mut T` lets the callee change the pointee, so the value model above fails. The likely model is a place-based state: each mutable reference is tied to the local it borrows, and a write through it updates that local's state. Calls with `&mut` arguments must havoc the pointee and assume the callee's `ensures`. This needs its own design and its own tests, and I would not start it until phase 1 is in use.

## Out of scope

- `UnsafeCell`, `Cell`, `RefCell`, and any other interior mutability.
- Raw pointers and `unsafe` blocks.
- Types with `Drop` glue, unless they are scalars.
- Lifetimes as proof obligations. rustc checks them; see the trust decision above.
- Heap-allocated values (`Box`, `Vec`). These need a separate memory model.

## Test plan

- A `&u8` parameter with `*x + 1` gets the same overflow counterexample as the owned version.
- `ensures` on `*result` for a reference result, with the caller's proof depending on the callee's `ensures` as for calls.
- A type with `UnsafeCell` is reported as unsupported, not verified.
- A `&mut` parameter is reported as unsupported in phase 1.

## Decision needed

Approve phase 1 as described, and confirm the trust decision that rustc's borrow checker is part of the trusted base for this translator.
