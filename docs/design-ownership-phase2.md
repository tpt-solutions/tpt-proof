# Design: Mutable References (Ownership Phase 2)

Status: **proposal for review.** Phase 1 (shared references to scalars) is implemented. This phase extends `docs/design-ownership.md`. No translator code is written for it yet; it is implemented after review.

## Why phase 1 does not extend directly

Phase 1 models a reference by its pointee value. That holds because a shared borrow cannot change its pointee while it is live (rustc's borrow checker guarantees this). A mutable reference can change the pointee, so a single value per reference is wrong: after `*r = 1`, the borrowed local must read as `1`.

## Model: places with state

The translator keeps a state map from each MIR local to its value, as now. A mutable reference is represented by the **place it borrows**, not by a value. A `&mut x` borrow records that `r` refers to local `x`.

- Reading `*r` reads the current value of `x`.
- Writing `*r = v` updates `x`'s value in the state.
- A reborrow `&mut *r` refers to the same place as `r`.
- A borrow of a field or a tuple component is out of scope for this phase.

The borrowed local is the only place a write can reach. rustc's borrow checker guarantees that while `r` is live, no other access to `x` happens, so the state map stays consistent: there is no aliasing to track.

## Calls with mutable arguments

A call that takes `&mut x` may change `x`. The model for such a call:

1. Check the callee's `requires` with the argument values, as for shared arguments (a VC at the call site).
2. Replace the value of every place passed as `&mut` with a fresh constant, within the range of its type. This is the havoc.
3. Assume the callee's `ensures` about the fresh values, with `*param` bound to the new value of the place.

Step 3 depends on the callee's contract describing the pointee after the call. A callee whose `ensures` do not mention a `&mut` parameter leaves its pointee unknown, which is sound but weak. The same modular trust applies as for calls in phase 1 of the translator: the callee must be verified separately.

## Write through a reference in a loop

A loop that writes through `&mut x` assigns `x`. The loop rule already havocs every local the loop assigns. Writes through a mutable reference must be counted as assignments to the borrowed local. The invariant is then written over the current value of `x`, as it is for a local.

## Trust

- rustc's borrow checker is trusted for exclusivity and lifetimes, as in phase 1.
- A `&mut` argument's pointee is havoced at every call, so no assumption is made about it beyond the callee's contract.
- Callee contracts are trusted only when the callee is verified separately, as for calls.

## Out of scope

- Borrows of fields, array elements, and tuple components. These need place paths in the state map.
- Raw pointers and `unsafe` blocks.
- Interior mutability (`Cell`, `RefCell`, `UnsafeCell`), which phase 1 already rejects.
- Heap values (`Box`, `Vec`).

## Test plan

- `fn set(x: &mut u8) { *x = 1 }` with `ensures *x == 1`: the write is visible in the postcondition, and the VC is proved.
- A caller that passes `&mut y`, then reads `y`: the read sees the callee's `ensures` through the havoced value.
- A callee with no `ensures` about its `&mut` parameter: the caller's postcondition on that value is refuted (sound, and weak).
- A loop that writes through `&mut x`, with an invariant over `x`: preservation and entry VCs, as for locals.
- A field borrow (`&mut s.a`): reported as unsupported.

## Decision needed

Approve the place-based model and the havoc-at-call rule, so implementation can start.
