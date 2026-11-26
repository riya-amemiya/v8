# Lean 4 model and safety proofs for `Array.prototype.reverse`

This directory models `TryFastPackedArrayReverse` and `FastArrayReverse` in
`src/builtins/array-reverse.tq`, the fast path of `ArrayPrototypeReverse`, and
proves that it never reads or writes outside the backing store, never writes
into a copy-on-write backing store, and leaves a well-formed array with holes
past its length whose elements are the reversed elements. The accesses and the
copy-on-write handling come from `InPlace`, which this library imports.

## Files

| File | Contents |
| --- | --- |
| `ArrayReverse/Model.lean` | The swap loop, the kind dispatch and the specification |
| `ArrayReverse/Safety.lean` | Absence of undefined behavior and aborts, agreement with the specification, well-formedness |
| `ArrayReverse/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-reverse.tq`

| Lean | Torque |
| --- | --- |
| `revLoop` | the `while (lower < upper)` loop of `FastArrayReverse`, with `LoadElement` and `StoreElement` through bounds-checked slices |
| `fastReverse` | `FastArrayReverse` from `lower = 0` and `upper = length - 1` |
| `tryFast` | `TryFastPackedArrayReverse` |
| `a.fast = false` | `Cast<FastJSArray>(receiver) otherwise Slow` |
| `ensureWritableChecked` before `fastReverse` | `array::EnsureWriteableFastElements(array)` for the Smi and object kinds |
| `fastReverse a` for the double kinds | `FastArrayReverse<FixedDoubleArray, float64_or_undefined_or_hole>`, without `EnsureWriteableFastElements` |
| `Result.slow` | `Slow` and `GenericArrayReverse` |
| `specReverse` | the specification, which moves the element at `len - lower - 1` to `lower` and keeps holes as holes |

`JSArr.fast` stands for the `FastJSArray` cast, which already checks
`IsPrototypeInitialArrayPrototype` and `IsNoElementsProtectorCellInvalid`, so
the repeated checks before the holey kinds always pass.

## Theorems

`tryFast_ne_ub`. For every well-formed array, the fast path has no undefined
behavior.

`tryFast_ne_abort`. For every well-formed array whose backing store length is
at most `c.maxLen`, when `c.maxLen ≤ c.smiMax`, the fast path does not abort.

`tryFast_done`. For every well-formed array with holes past its length, when
the fast path returns `a'`, `a'` has the kind and the length of `a`, is not
copy-on-write, is well formed, satisfies `JSArr.SlackHoles`, and its elements
are `specReverse a.elems`.

`tryFast_handles`. Under the hypotheses of `tryFast_ne_abort`, every fast array
is handled by the fast path.

The double kinds skip `EnsureWriteableFastElements`, which is safe because a
well-formed array with a double kind is never copy-on-write.
`Examples.lean` checks that `fastReverse` aborts on an array whose length
exceeds its empty backing store, which `JSArr.WF` rules out, and that it is
undefined behavior on a copy-on-write backing store, which
`EnsureWriteableFastElements` removes.

## Assumptions

The array satisfies `JSArr.WF`, and `tryFast_done` also requires
`JSArr.SlackHoles`. `tryFast_ne_abort` and `tryFast_handles` require a backing
store length of at most `c.maxLen` and `c.maxLen ≤ c.smiMax`, which keep the
`Cast<Smi>(array.length)` and the copy in `EnsureWriteableFastElements` from
failing.

## Not modeled

`ToObject`, `GenericArrayReverse` and the float64 representation of doubles
are outside the model.
