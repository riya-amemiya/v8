# Lean 4 model and safety proofs for `Array.prototype.lastIndexOf`

This directory models `ArrayPrototypeLastIndexOf` in
`src/builtins/array-lastindexof.tq`, its index computation and its fast path
`TryFastArrayLastIndexOf`, and proves that the fast path never fails a bounds
check and returns what the generic loop `GenericArrayLastIndexOf` returns on the
same array.

## Files

| File | Contents |
| --- | --- |
| `ArrayLastIndexOf/Model.lean` | The index computation, the fast scans and the specification loop |
| `ArrayLastIndexOf/Safety.lean` | Absence of aborts and agreement with the specification |
| `ArrayLastIndexOf/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-lastindexof.tq`

| Lean | Torque |
| --- | --- |
| `fromIndex` | `GetFromIndex` |
| `specFrom` | steps 4 to 7 of the specification |
| `lastIndexOf` | `ArrayPrototypeLastIndexOf` after `GetLengthProperty` |
| `fastLastIndexOf` | `TryFastArrayLastIndexOf`, `FastArrayLastIndexOfFixedArray` and `FastArrayLastIndexOfDoubles` |
| `clampFrom` | `ClampLastIndexOfFrom`, the fix for Bug 898785 |
| `scanStore` | the loops `LastIndexOfNumberInFixedArray`, `LastIndexOfAnyInFixedArray`, `LastIndexOfDoubleValue` and `LastIndexOfUndefinedInDoubles`, which read through bounds-checked Torque slices |
| `Cmp.seq` | `StrictEqual`, and the comparisons the fast loops use in its place |
| `Cmp.isNaN` | the `Float64IsNaN` early returns |
| `specScan`, `specLastIndexOf` | steps 8 and 9 of the specification, as `GenericArrayLastIndexOf` performs them |
| `Result.generic` | the jump to `GenericArrayLastIndexOf` |
| `Result.fatal` | a failed Torque slice bounds check |

`lastIndexOf` takes the array `a` as it is after `ToInteger(fromIndex)` and the
length `len` read before it as independent inputs, so the theorems cover any
change user code makes to the array in between.

## Theorems

`lastIndexOf_ne_fatal`. For every well-formed array, the fast path never reads
outside the backing store.

`lastIndexOf_spec`. For every well-formed array with holes past its length and
every comparison satisfying `Cmp.OK`, the result of the fast path equals the
result of the specification loop on the same array, which treats indices at or
past the current length and holes as absent.

The two theorems need different facts. `lastIndexOf_ne_fatal` relies on
`ClampLastIndexOfFrom`, which clamps the start to the backing store length:
user code in `ToInteger` can shrink the array and trim its backing store below
the old length, and `Examples.lean` checks that scanning from the unclamped
index fails the bounds check. `lastIndexOf_spec` relies on the holes past the
length: after clamping to the backing store rather than to the length, the scan
reads the slots between the current length and the backing store length, and
`Examples.lean` checks that a stale value there would make the fast path return
an index the specification does not.

## Assumptions

The array satisfies `JSArr.WF` and `JSArr.SlackHoles`. V8 states the second
invariant in `ValidateContents` in `src/objects/elements.cc`, whose slow DCHECKs
require that values past the length are holes even for packed kinds. The writers
that lower a length keep it: `SetLengthImpl` calls `FillWithHoles`, the CSA
`ArrayPrototypePop` stores the hole, `RemoveElement` in `elements.cc` fills the
vacated slot, `JSCallReducer::ReduceArrayPrototypePop`,
`JSCallReducer::ReduceArrayPrototypeShift` and
`MaglevGraphBuilder::TryReduceArrayPrototypePop` store the hole, and the growth
paths initialize new slots with holes through `CopyFixedArrayElements` and
`ConvertElementsWithCapacity`. The Torque shift and splice are covered by their
own libraries.

`Cmp.OK` states the properties of `StrictEqual` the fast loops use: a NaN
search value matches nothing, only a number matches a number, and only
`undefined` matches `undefined`. These justify returning early for NaN, for a
search value that is neither a number nor `undefined` in a double array, and
comparing doubles numerically.

## Not modeled

`ToObject`, `GetLengthProperty`, `ToInteger` and the float64 representation are
outside the model, which represents the integer arguments as `Int` with
infinities.
