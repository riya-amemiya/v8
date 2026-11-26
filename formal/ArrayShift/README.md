# Lean 4 model and safety proofs for `Array.prototype.shift`

This directory models `TryFastArrayShift` in `src/builtins/array-shift.tq`, the
fast path of `ArrayPrototypeShift`, and proves that it never reads or writes
outside the backing store, never writes into a copy-on-write backing store, and
leaves a well-formed array with holes past its new length that holds the
remaining elements, returning the first element with a hole read as
`undefined`. The accesses, the map checks and the copy-on-write handling come
from `InPlace`, which this library imports.

## Files

| File | Contents |
| --- | --- |
| `ArrayShift/Model.lean` | The element shift, the fast path and the specification |
| `ArrayShift/Safety.lean` | Absence of undefined behavior and aborts, agreement with the specification, well-formedness |
| `ArrayShift/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-shift.tq`

| Lean | Torque |
| --- | --- |
| `tryFast` | `TryFastArrayShift` |
| `a.fast = false` | `Cast<FastJSArray>(receiver) otherwise Slow` |
| `m.pushable = false` | `witness.EnsureArrayPushable() otherwise Slow` |
| `ensureWritableChecked` | `EnsureWriteableFastElements` inside `EnsureArrayPushable` of the witness |
| `b.length = 0` | `array.length == 0`, for which the fast path returns `Undefined` |
| `2 * (b.length - 1) + kMinAddedElementsCapacity < b.store.length` | the right-trim check, which goes to `Runtime` |
| `kMaxCopyElements < b.length - 1` | `if (newLength > kMaxCopyElements) goto Runtime` |
| `shiftElements` | `LoadElementOrUndefined(0)`, `MoveElements(0, 1, ...)` and `StoreHole(newLength)` of the witness |
| `castElements` | the `Cast<FixedDoubleArray>` with `otherwise unreachable` in those witness methods |
| `Result.slow` | both `Slow`, which runs `GenericArrayShift`, and `Runtime`, which tail calls the C++ `ArrayShift` |
| `specShift` | the remaining elements and the first element |

## Theorems

`tryFast_ne_ub`. For every well-formed array and every map, the fast path has
no undefined behavior.

`tryFast_ne_abort`. For every well-formed array whose backing store length is
at most `c.maxLen`, when `c.maxLen ≤ c.smiMax`, the fast path does not abort.

`tryFast_done`. For every well-formed array with holes past its length, when
the fast path returns `a'` and `r`, `a'` is not copy-on-write, has the kind of
`a` and length `a.length - 1`, is well formed and satisfies
`JSArr.SlackHoles`, and `(a'.elems, r) = specShift a.elems`.

`tryFast_handles`. Under the hypotheses of `tryFast_ne_abort`, for a fast array
with a pushable map, at most `kMaxCopyElements + 1` elements and a backing
store of at most `2 * (a.length - 1) + kMinAddedElementsCapacity` slots, the
fast path returns.

`tryFast_done` includes the hole that `StoreHole(newLength)` writes, so the
shift keeps the invariant `JSArr.SlackHoles` that the fast paths reading past
the length, such as `lastIndexOf`, rely on. `Examples.lean` checks that
`shiftElements` aborts on a double array whose length exceeds its empty backing
store, which `JSArr.WF` rules out, and the bailouts for a read-only length, a
length above `kMaxCopyElements + 1` and a backing store that would be trimmed.

## Assumptions

The array satisfies `JSArr.WF`, and `tryFast_done` also requires
`JSArr.SlackHoles`. `tryFast_ne_abort` and `tryFast_handles` require a backing
store length of at most `c.maxLen` and `c.maxLen ≤ c.smiMax`. Both hold in V8:
`c.maxLen` stands for `kMaxFixedArrayCapacity` in
`src/objects/fixed-array-base.h`, 128 Mi slots, which bounds every backing
store, and `c.smiMax` for the Smi maximum, `2^30 - 1` with the 31-bit Smis of
`include/v8-internal.h`.

## Not modeled

`ToObject`, `GenericArrayShift`, the C++ `ArrayShift` and the float64
representation of doubles are outside the model. `MapInfo` stands for the map
bits `EnsureArrayPushable` reads.
