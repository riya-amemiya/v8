# Lean 4 model and safety proofs for `Array.prototype.map`

This directory models `FastArrayMap` and the `Vector` struct in
`src/builtins/array-map.tq`, the fast path of `ArrayMap`, and proves that it
never fails a bounds check and never has undefined behavior, that the array it
returns is well formed and holds the results of the specification, and that a
bailout hands `ArrayMapLoopContinuation` a well-formed output array and an
index that agree with the specification loop. The loop over the input is the
witness loop of `ArrayWitness`, which this library imports, on a
`FastJSArrayForReadWitness`.

## Files

| File | Contents |
| --- | --- |
| `ArrayMap/Model.lean` | The result vector, its kind choice, the loop body, the fast path and the specification loop |
| `ArrayMap/Safety.lean` | The vector invariant, the simulation and the three theorems |
| `ArrayMap/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-map.tq`

| Lean | Torque |
| --- | --- |
| `Vec` | `Vector`, with `onlySmis`, `onlyNumbers`, `onlyNumbersAndUndefined` and `skippedElements` |
| `newVector` | `NewVector`, which allocates `AllocateFixedArrayWithHoles(len)` |
| `noteResult`, `storeResult` | `StoreResult`, whose store into `fixedArray.objects[index]` is bounds checked |
| `body` | one iteration of `FastArrayMap`: `ReportSkippedElement` on a hole, otherwise the call of `callbackfn` and `StoreResult` |
| `baseKind`, `resultKind` | the kind choice in `CreateJSArray`, made holey by `FastHoleyElementsKind` when an element was skipped or `validLength` is below the length |
| `doubleOk` | the `UnsafeCast<(Number \| Undefined \| TheHole)>` in the double copy of `CreateJSArray` |
| `createJSArray` | `CreateJSArray`, which copies the first `validLength` values into `AllocateFixedDoubleArrayWithHoles(length)` for a double kind and installs `fixedArray` otherwise |
| `finish` | `vector.CreateJSArray(len)` after the loop |
| `fastMap` | `ArrayMap` from the species check to the return of `FastArrayMap` |
| `speciesOk`, `a.forRead`, `smiMax` | `IsArraySpeciesProtectorCellInvalid`, `Cast<FastJSArrayForRead>(receiver)` and `Cast<Smi>(len)`, each going to `SlowSpeciesCreate` |
| `Result.species` | `SlowSpeciesCreate`, after which `ArraySpeciesCreate` and `ArrayMapLoopContinuation` run from 0 |
| `Result.bailout` | `PrepareBailout(k)`, `Bailout(vector.CreateJSArray(k), k)` and the call of `ArrayMapLoopContinuation` |
| `specBody`, `specMap` | the specification, which sets index `k` of an array of `len` holes for every present element |

## Theorems

`fastMap_safe`. For every well-formed array and every callback satisfying
`CallbackOk a.kind`, the fast path never ends in `fatal` or `ub`, for both
settings of `V8_ENABLE_UNDEFINED_DOUBLE` and every result of the species check.

`fastMap_done`. Under the same hypotheses, when the fast path returns `r`, `r`
is well formed, its elements are `specMap cb a` and its length is `a.length`.

`fastMap_bailout`. Under the same hypotheses, when the fast path bails out with
output `out`, indices `ks` and array `arr`, there are `k ≤ a.length` and a list
`o` with `ks = List.range' k (a.length - k)`, the specification loop reaches
`ks`, `o` and `arr` from the start, `out` is well formed with elements `o` and
length `a.length`, `arr` is well formed, and the specification loop run on `ks`
from `o` and `arr` gives `specMap cb a`.

Well-formedness of the result is the safety property of the kind choice: the
flags of `Vector` must describe every stored value, or `CreateJSArray` would
install a backing store whose contents its kind does not allow, or copy a
non-number through the `UnsafeCast` into a double array. `Examples.lean` checks
that `createJSArray` is undefined behavior for a vector whose flags claim only
numbers while it holds another value, the choice of `HOLEY_DOUBLE_ELEMENTS` or
`PACKED_ELEMENTS` for `undefined` results with and without undefined doubles,
and the holey output of a bailout.

## Assumptions

The array satisfies `JSArr.WF`, and the callback satisfies `CallbackOk a.kind`
from `ArrayWitness`: it leaves a well-formed array whose kind is unchanged
whenever it reports the map unchanged.

## Not modeled

`ToObject`, `GetLengthProperty`, the callable check, `thisArg`, exceptions from
the callback, `ArraySpeciesCreate`, the allocation of HeapNumbers and the deopt
continuations are outside the model.
