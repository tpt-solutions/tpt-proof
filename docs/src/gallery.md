# Verified-Rust gallery

Each example is a file in `examples/gallery/`. The output below is what `tpt-proof verify` printed for it when this page was written, so you can compare your own run against it. The exit status is 0 only when every assertion is proved.

Run an example with:

```sh
tpt-proof verify examples/gallery/clamp.rs
```

Add `TPT_PROOF_VERIFY=1` to have the kernel check each proof, as described in [What is trusted](trusted.md). The output then says `kernel-checked` for a proof the kernel accepted, and `solver unsat, not kernel-checked` otherwise.

## 1. A postcondition that holds: `clamp`

[`clamp.rs`](../../examples/gallery/clamp.rs) restricts a value to a range. Its contract says the result lies in `[lo, hi]`, provided `lo <= hi`.

```text
clamp: ensures |result| *result >= lo && *result <= hi: proved (kernel-checked)
clamp: ensures |result| *result >= lo && *result <= hi: proved (kernel-checked)
clamp: ensures |result| *result >= lo && *result <= hi: proved (kernel-checked)
```

There is one line per return path, and each is proved. Without `TPT_PROOF_VERIFY=1` the same lines say `proved (solver unsat, not kernel-checked)`.

## 2. Reading a counterexample: `clamp_missing_precondition`

[`clamp_missing_precondition.rs`](../../examples/gallery/clamp_missing_precondition.rs) is the same function without the `lo <= hi` precondition.

```text
clamp: ensures |result| *result >= lo && *result <= hi: proved (solver unsat, not kernel-checked)
clamp: ensures |result| *result >= lo && *result <= hi: counterexample: _2 = 1, _1 = 1, _3 = 0
clamp: ensures |result| *result >= lo && *result <= hi: counterexample: _2 = 1, _1 = 0, _3 = 0
```

A counterexample names inputs that break the assertion. The names are the MIR locals of the function, so `_1` is `value`, `_2` is `lo` and `_3` is `hi`. Here `lo = 1` and `hi = 0`, so the range is empty and the result cannot satisfy both bounds. The fix is the precondition from example 1: `#[doc = "tpt-proof-requires: lo <= hi"]`.

## 3. A precondition that rules out the failure: `safe_div`

[`safe_div.rs`](../../examples/gallery/safe_div.rs) divides by `y`, and its contract requires `y != 0`. [`safe_div_unguarded.rs`](../../examples/gallery/safe_div_unguarded.rs) is the same division with no precondition.

```text
quotient: assertion at bb0: counterexample: _1 = 0, _2 = 0
```

The division by zero is the assertion at `bb0`, and the counterexample is `y = 0` (`_2`). With the precondition, `safe_div` is proved:

```text
quotient: assertion at bb0: proved (solver unsat, not kernel-checked)
quotient: ensures |result| *result <= x: proved (solver unsat, not kernel-checked)
```

In proof mode the division assertion is kernel-checked, but the postcondition is not yet: it contains `div`, which the proof translator does not handle, so it is reported as unchecked:

```text
quotient: ensures |result| *result <= x: unchecked (solver unsat, proof not accepted): unsupported in proofs: term `Div(Var("_1"), Var("_2"))`
```

This is a known gap, not a failed proof. The solver's verdict is correct; the kernel has not yet been given the arithmetic it needs for division.

## 4. A loop with an invariant: `count_up`

[`count_up.rs`](../../examples/gallery/count_up.rs) counts `i` up to `n` and returns `total`, which equals `n`. The loop needs an invariant, `i <= n && total == i`, which the marker gives with the line number of the `while`.

```text
count_up: loop at line 8: invariant holds on entry: proved (solver unsat, not kernel-checked)
count_up: ensures |result| *result == n: proved (solver unsat, not kernel-checked)
count_up: assertion at bb2: proved (solver unsat, not kernel-checked)
count_up: assertion at bb3: proved (solver unsat, not kernel-checked)
count_up: loop at line 8: invariant is preserved: proved (solver unsat, not kernel-checked)
```

The verifier checks three things: the invariant holds when the loop is entered, it is preserved by an iteration, and it implies the postcondition when the loop exits.

The line number matters. `loop at line 8` is the line of the `while`, and an invariant that names another line is reported as having no invariant. Check the number when you add or move code above a loop.

## 5. A wrong invariant: `count_up_wrong_invariant`

[`count_up_wrong_invariant.rs`](../../examples/gallery/count_up_wrong_invariant.rs) uses `i < n` as the invariant. That is false when the loop is entered with `n = 0`, so the first check fails and the verifier shows that input:

```text
count_up: loop at line 8: invariant holds on entry: counterexample: _1 = 0
count_up: loop at line 8: invariant is preserved: counterexample: _1 = 1, __h1 = 0, __h4 = 0, __h2 = 0, __h3 = false
```

The second line is a counterexample to preservation. The names starting with `__h` appear to be the loop's havoced values, a state at an arbitrary iteration. Read the line as "some state where the invariant holds and the body breaks it".

Proof mode also shows the open gap in this example:

```text
count_up: assertion at bb2: unchecked (solver unsat, proof not accepted): unsupported in proofs: an indexed rule such as `th-lemma`
```

The solver proves the assertion. The kernel has no check yet for Z3's `assign-bounds` lemma, so the answer is reported as unchecked, not verified. See [the reflection notes](../../docs/spike-proof-reconstruction.md).

## 6. Reading an array: `array_get`

[`array_get.rs`](../../examples/gallery/array_get.rs) reads `a[i]` for an array of four bytes. The read is guarded by a bounds check that rustc emits, so the verifier turns it into an assertion: `i < 4`.

```text
get: assertion at bb0: proved (solver unsat, not kernel-checked)
```

Without the precondition, [`array_get_unchecked.rs`](../../examples/gallery/array_get_unchecked.rs) gives a counterexample with the index that is out of bounds:

```text
get: assertion at bb0: counterexample: _2 = 4, _1 = all 0
```

`_1` is the array, shown as `all 0`: every element is zero. A model that changes some elements prints them after `except`, as `all 0 except {1: 7}`.

## 7. Writing an array: `array_set`

[`array_set.rs`](../../examples/gallery/array_set.rs) writes an element and reads it back, and its postcondition says the read returns the value written:

```text
set_then_get: assertion at bb0: proved (solver unsat, not kernel-checked)
set_then_get: assertion at bb1: proved (solver unsat, not kernel-checked)
set_then_get: ensures |result| *result == v: proved (solver unsat, not kernel-checked)
```

The write is translated as an array that equals the old one except at the index. The solver's theory of arrays does the rest.

## 8. A search over an array: `binary_search`

[`binary_search.rs`](../../examples/gallery/binary_search.rs) is a binary search over a four-element array. Its contract talks about indices only, because a specification cannot yet mention array contents. The invariant `lo <= hi && hi <= 4` keeps every read `a[mid]` in bounds, and it makes the result at most 4.

```text
search: loop at line 9: invariant holds on entry: proved (solver unsat, not kernel-checked)
search: ensures |result| *result <= 4: proved (solver unsat, not kernel-checked)
search: assertion at bb2: proved (solver unsat, not kernel-checked)
...
search: loop at line 9: invariant is preserved: proved (solver unsat, not kernel-checked)
```

The output is longer than the other examples because each read and each arithmetic check has its own line. Every line is proved, and the exit status is 0.

In proof mode the kernel cannot yet check this example. The reads need the array theory, and the midpoint needs division, so most lines say `unchecked`. The solver's answer is still the answer the verifier gives in default mode.

## 9. A ring buffer write: `ring_write`

[`ring_write.rs`](../../examples/gallery/ring_write.rs) writes into a four-slot buffer at `head % 4`. The index is in bounds for every head, so both assertions are proved:

```text
write: assertion at bb0: proved (solver unsat, not kernel-checked)
write: assertion at bb1: proved (solver unsat, not kernel-checked)
```

In proof mode the first assertion is kernel-checked, and the second is reported as unchecked, because the kernel does not translate `mod` yet.

## Not yet in the gallery

- A function whose postcondition describes the contents of an array, such as "the result is an element of `a`". The specification language has no array syntax yet, and the kernel cannot check the array theory.
- A function that calls another contracted function on a path the caller must prove. The `call_verified.rs` and `call_violated.rs` fixtures in `crates/tpt-proof-mir/tests/fixtures` show that case.
