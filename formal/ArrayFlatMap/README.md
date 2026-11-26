# Lean 4 model and safety proofs for `Array.prototype.flatMap`

`ArrayPrototypeFlatMap` in `src/builtins/array-flat.tq` calls
`FlattenIntoArrayWithMapFn` with depth 1, which runs `FlattenIntoArrayFast`
and falls back to `FlattenIntoArraySlow` on a bailout. This directory models
the fast loop over the source and the depth 0 flattening of each mapped array,
and proves that the loop never fails a bounds check or a backing store cast,
that the values it appends to the target are the values the specification
appends, and that a bailout hands `FlattenIntoArraySlow` a source index and a
target index that agree with the specification loop. The outer loop is the
witness loop of `ArrayWitness`, which this library imports.

## Files

| File | Contents |
| --- | --- |
| `ArrayFlatMap/Model.lean` | Mapped values, the inner flattening, the loop body, the fast path and the specification loop |
| `ArrayFlatMap/Safety.lean` | The inner flattening lemma, the simulation and the three theorems |
| `ArrayFlatMap/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-flat.tq`

| Lean | Torque |
| --- | --- |
| `Mapped.value` | a mapped element that is not flattened, stored by `FastCreateDataProperty(target, targetIndex, element)` |
| `Mapped.array` | a mapped element that passes `Cast<JSArray>(element)` |
| `Mapped.proxy` | a `JSProxy` for which `runtime::ArrayIsArray` is true, with the values its flattening appends |
| `Callback` | the call of `mapfn` with `element`, `smiSourceIndex` and `source` |
| `innerLoad`, `innerLoop`, `innerFlatten` | `FlattenIntoArrayWithoutMapFn` with depth 0 on a mapped `JSArray`: the fast loop with `LoadElementNoHole` when the element is a fast array, and the slow loop otherwise |
| `body` | one iteration of `FlattenIntoArrayFast` after `LoadElementNoHole` |
| `fastFlatMap` | `FlattenIntoArrayFast` with `hasMapper` true and depth 1 |
| `a.fast = false`, `smiMax < a.length` | `Cast<FastJSArray>(source)` and `Cast<Smi>(sourceLength)`, each going to `Bailout(targetIndex, smiSourceIndex)` |
| `List Val` accumulator | the values stored into the target, whose length is `targetIndex` |
| `Result.bailout` | `Bailout(targetIndex, smiSourceIndex)` and the call of `FlattenIntoArraySlow` |
| `specAppended`, `specBody`, `specFlatMap` | the values the specification appends, skipping holes in the source and in each mapped array |

## Theorems

`fastFlatMap_safe`. For every well-formed array and every callback satisfying
`CallbackOk a.kind` and `CallbackFits`, the fast path never ends in `fatal` or
`ub`.

`fastFlatMap_done`. Under the same hypotheses, when the fast path returns the
appended values `r`, `r = specFlatMap cb a`.

`fastFlatMap_bailout`. Under the same hypotheses, when the fast path bails out
with indices `ks`, appended values `out` and array `arr`, there is
`k ≤ a.length` with `ks = List.range' k (a.length - k)`, the specification
loop reaches `ks`, `out` and `arr` from the start, and the specification loop
run on `ks` from `out` and `arr` gives `specFlatMap cb a`.

`innerFlatten_eq`. For every well-formed mapped array, the depth 0 flattening
returns its present elements in order. `Examples.lean` checks that the inner
loop fails its bounds check on an array whose length exceeds its backing store,
which is why `CallbackFits` requires every mapped array to be well formed.

## Assumptions

The source array satisfies `JSArr.WF`, and the callback satisfies
`CallbackOk a.kind` from `ArrayWitness`, so it leaves a well-formed source whose
kind is unchanged whenever it reports the map unchanged. `CallbackFits` requires
that every array the callback returns satisfies `JSArr.WF`.

## Not modeled

`ArraySpeciesCreate`, the target array and `FastCreateDataProperty` are
represented by the list of appended values. The `kMaxSafeInteger` check,
`PerformStackCheck`, the flattening of proxies, `GetLengthProperty` on mapped
values, exceptions from the callback, and `ArrayPrototypeFlat` are outside the
model. The `ArrayFlat` library covers `TryFastFlat`.
