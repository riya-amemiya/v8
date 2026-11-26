# Lean 4 model and safety proofs for `Array.prototype.with`

This directory models `ArrayPrototypeWith` in `src/builtins/array-with.tq` from
`ConvertRelativeIndex` on, its fast path `TryFastPackedArrayWith`, and the
non-appending store of `FastCreateDataProperty` into the copy. It proves that
the fast path never has undefined behavior and never aborts, and that it
returns a well-formed array of length `len` holding the source elements with
the value at the index. The result type and `ExtractFastJSArray` come from
`ArrayCopyCommon`, which this library imports.

## Files

| File | Contents |
| --- | --- |
| `ArrayWith/Model.lean` | The index conversion, the store into the copy, the fast path and the specification |
| `ArrayWith/Safety.lean` | Absence of undefined behavior and aborts, agreement with the specification, well-formedness |
| `ArrayWith/Examples.lean` | Executable `#guard` checks |

## Correspondence with the V8 sources

| Lean | V8 |
| --- | --- |
| `convertRelativeIndex` | `ConvertRelativeIndex(relativeIndex, len)`, whose failure throws a RangeError |
| `fastPath` | `ArrayPrototypeWith` after `ToInteger_Inline(index)` |
| `tryFast` | `TryFastPackedArrayWith` |
| `a.fast = false`, `isFastPacked a.kind = false` | `Cast<FastJSArray>(receiver) otherwise Slow` and `IsFastPackedElementsKind` |
| `r.max < len` | `Cast<Smi>(len) otherwise Slow` |
| `a.length < len` | `if (lenSmi > array.length) goto Slow` |
| `extractFast lim a 0 len` | `ExtractFastJSArray(context, array, 0, lenSmi)` |
| `fastCreate` | the non-appending branch of `FastCreateDataProperty` in `src/builtins/base.tq` |
| `Torque.ensureWritable` | `EnsureWriteableFastElements` |
| `storeInto` | the bounds-checked element stores of that branch |
| `storeUndefined` | `StoreFixedDoubleArrayUndefined`, which checks its index only with `CSA_DCHECK` |
| `c.store = []` for a double kind | `Cast<FixedDoubleArray>(array.elements) otherwise unreachable` on `empty_fixed_array` |
| `runtimeCreate`, `runtimeKind` | the `Slow` label of `FastCreateDataProperty` and the runtime `CreateDataProperty`, represented as a store that moves the copy to `GetMoreGeneralElementsKind` of its kind and `Object::OptimalElementsKind` of the value, made holey for a holey kind |
| `ud` | `V8_ENABLE_UNDEFINED_DOUBLE` |
| `Result.slow` | `Slow` and `GenericArrayWith` |
| `specWith` | the loop of `GenericArrayWith`, which reads `GetProperty(receiver, k)` for every other index |

`fastPath` takes the length `len` read before `ToInteger_Inline(index)` and the
array as it is after it as independent inputs, so the theorems cover any change
user code makes to the array in between.

## Theorems

`fastPath_ne_ub` and `fastPath_ne_abort`. For every well-formed array whose
backing store length is at most `lim.maxLen`, every length and every index,
the fast path has no undefined behavior and does not abort.

`fastPath_done`. Under the same hypotheses, when the fast path returns `res`
for source `src`, there is `idx` with `convertRelativeIndex index len = some idx`
and `idx < len`, `src = a`, and `res` is well formed, satisfies
`JSArr.SlackHoles`, is not copy-on-write, has length `len`, and its elements are
`specWith a.elems len idx v`.

`tryFast_ne_ub`, `tryFast_ne_abort`, `tryFast_done` and `tryFast_cases` state
the same for `tryFast` with an index `idx < len`.

The proofs rest on the copy having exactly `len` slots, so the index is inside
the backing store and a double backing store is not `empty_fixed_array`.
`Examples.lean` checks that `fastCreate` aborts on a double array whose backing
store is empty, and that storing `undefined` past the backing store of a
`HOLEY_DOUBLE_ELEMENTS` array is undefined behavior, and the kinds the runtime
store chooses for a double and for `undefined`.

## Assumptions

The array satisfies `JSArr.WF`, and its backing store length is at most
`lim.maxLen`, the `FixedArray::kMaxLength` limit of `AllocateFixedArray`.

## Not modeled

`ToObject`, `GetLengthProperty`, `ToInteger_Inline`, `GenericArrayWith` and
the runtime `CreateDataProperty` beyond `runtimeCreate` are outside the model.
