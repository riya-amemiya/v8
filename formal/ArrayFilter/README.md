# Lean 4 model and safety proofs for `Array.prototype.filter`

This directory models `FastArrayFilter` and `FastFilterSpeciesCreate` in
`src/builtins/array-filter.tq`, the fast path of `ArrayFilter`, together with
the push of selected values into the output array through
`FastJSArrayWitness.Push` and `BuildAppendJSArray`. It proves that the fast
path never fails a bounds check and never has undefined behavior, that the
output holds exactly the values the specification selects, and that a bailout
hands `ArrayFilterLoopContinuation` an index, an output array and a `to` count
that agree with the specification loop. The loop over the input is the witness
loop of `ArrayWitness`, which this library imports.

## Files

| File | Contents |
| --- | --- |
| `ArrayFilter/Model.lean` | The append, the store with its slow fallback, the loop body, the fast path and the specification loop |
| `ArrayFilter/Safety.lean` | The output invariant, the simulation and the three theorems |
| `ArrayFilter/Examples.lean` | Executable `#guard` checks |

## Correspondence with the V8 sources

| Lean | V8 |
| --- | --- |
| `FilterConfig.smiMax` | `Cast<Smi>(len) otherwise goto Bailout(k, to)` in `ArrayFilter` |
| `FilterConfig.undefinedDouble` | `V8_ENABLE_UNDEFINED_DOUBLE` |
| `FilterConfig.growLimit` | `FixedArrayBase::GetMaxLengthForNewSpaceAllocation`, above which `GrowElementsCapacity` bails out |
| `pushKind` | the kind `FastJSArrayWitness.Push` passes to `BuildAppendJSArray` |
| `accepts` | the checks of `TryStoreArrayElement` in `src/codegen/code-stub-assembler.cc` |
| `newCapacity` | `CalculateNewElementsCapacity` |
| `capacityFor` | `PossiblyGrowElementsCapacity`, whose new slots are holes |
| `append` | `BuildAppendJSArray(kind, array, value)`, with `ub` for a push kind of the wrong representation, a copy-on-write backing store, or an unchecked store of `undefined` through `StoreFixedDoubleArrayUndefined` |
| `Out` | the output array, the count `to`, and whether the output map is still the one `fastOutputW` was created with |
| `SlowStore`, `slowStore` | `FastCreateDataProperty(fastOutputW.stable, to, value)` under the `SlowStore` label |
| `store` | `fastOutputW.Recheck()`, the check `fastOutputW.Get().length != to` and `fastOutputW.Push(value)`, each falling back to `SlowStore` |
| `body` | one iteration of `FastArrayFilter` after `LoadElementNoHole` |
| `newOutput` | `FastFilterSpeciesCreate`, which allocates an empty array with the map of the receiver's kind |
| `fastFilter` | `ArrayFilter` from `FastFilterSpeciesCreate` to the end of `FastArrayFilter` |
| `speciesOk`, `a.fast` | `IsArraySpeciesProtectorCellInvalid` and `Cast<FastJSArray>(receiver)` in `FastFilterSpeciesCreate` |
| `pushable` | `fastOutputW.EnsureArrayPushable()` |
| `Result.species` | the `SlowSpeciesCreate` label, after which `ArraySpeciesCreate` and `ArrayFilterLoopContinuation` run from 0 |
| `Result.bailout` | `Bailout(k, to)` and the call of `ArrayFilterLoopContinuation` |
| `specBody`, `specFilter` | the values the specification selects |

## Theorems

`fastFilter_safe`. For every well-formed array, every callback satisfying
`CallbackOk a.kind` and every slow store satisfying `SlowOk a.kind`, the fast
path never ends in `fatal` or `ub`, whatever `speciesOk` and `pushable` are.

`fastFilter_done`. Under the same hypotheses, when the fast path returns `r`,
`r` is well formed, not copy-on-write, its length is the number of selected
values and its elements are exactly `specFilter cb a`.

`fastFilter_bailout`. Under the same hypotheses, when the fast path bails out
with indices `ks`, output `o` and array `arr`, there are `k ≤ a.length` and a
list `sel` with `ks = List.range' k (a.length - k)`, the specification loop
reaches `ks`, `sel` and `arr` from the start, `o` satisfies `OutInv a.kind o sel`
with `o.to = sel.length`, and the specification loop run on `ks` from `sel` and
`arr` gives `specFilter cb a`.

`OutInv K o sel` is the invariant behind both: the output is well formed and
not copy-on-write, its length and `to` are `sel.length`, its elements are
`sel`, and its kind is `K` while its map is unchanged. The last part keeps the
push kind in the representation of the output backing store, which
`pushKind_isDouble` relates to the kind, and capacity growth leaves room for the
store, so the `fatal` and `ub` branches of `append` are unreachable.
`Examples.lean` checks that `append` is undefined behavior with a double push
kind on a Smi array and on a copy-on-write backing store, and that a bailout
after an invalidated protector carries the stored value and `to`.

## Assumptions

The input array satisfies `JSArr.WF`, and the callback satisfies
`CallbackOk a.kind` from `ArrayWitness`. `SlowOk a.kind slow` states what is
assumed of `FastCreateDataProperty` when it appends at the length of a
well-formed output: the result is well formed, not copy-on-write, one element
longer with the value appended, and of kind `a.kind` whenever it reports the
map unchanged.

## Not modeled

`ToObject`, `GetLengthProperty`, the callable check, `thisArg`, exceptions from
the callback, `ArraySpeciesCreate` and the deopt continuations are outside the
model, and `FastCreateDataProperty` is represented by `SlowOk`.
