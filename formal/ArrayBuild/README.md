# Shared model of element stores and array copies

`ArrayBuild` models the element store and array copy routines that several
Array builtins share, and proves their safety once. `ArrayOf`, `ArrayFrom` and
`ArrayConcat` build on it.

## Files

| File | Contents |
| --- | --- |
| `ArrayBuild/Store.lean` | `FastCreateDataProperty` with its append and overwrite branches |
| `ArrayBuild/StoreSafety.lean` | Absence of undefined behavior and aborts, the resulting elements and length, well-formedness |
| `ArrayBuild/Loop.lean` | The loop of `CreateDataPropertyOrThrow` calls that `Array.of` and `Array.from` run, with the runtime fallback |
| `ArrayBuild/Clone.lean` | `CloneFastJSArray` with and without hole conversion |
| `ArrayBuild/CloneSafety.lean` | Absence of undefined behavior, the copied elements, well-formedness |

## Correspondence with the V8 sources

| Lean | V8 |
| --- | --- |
| `fastCreateDataProperty` | `FastCreateDataProperty` in `src/builtins/base.tq` |
| `overwrite` | its non-appending branch, which stores Smis into Smi kinds, numbers and `undefined` into double kinds and anything into object kinds |
| `appendElem`, `appendKind`, `valueFits` | its appending branch, `BuildAppendJSArray` with the kind argument `FastCreateDataProperty` passes, and `TryStoreArrayElement` |
| `growIfNeeded`, `newCapacity` | `PossiblyGrowElementsCapacity`, `CalculateNewElementsCapacity` and `GrowElementsCapacity`, which bails out at the new-space size limit and whose `CopyFixedArrayElements` fills the new slots with holes |
| `storeChecked` | Torque slice stores and `StoreFixedArrayElement` or `StoreFixedDoubleArrayElement` with `CheckBounds::kAlways`, whose `FixedArrayBoundsCheck` is a `CSA_CHECK` because `fixed_array_bounds_checks` is a read-only `true` flag |
| `storeUnchecked` | `StoreFixedDoubleArrayUndefined`, which checks its index only with `CSA_DCHECK` |
| `Torque.ensureWritable` | `EnsureWriteableFastElements` in `src/builtins/array.tq` |
| `StoreResult.slow` | the jump to the runtime function `CreateDataProperty` |
| `RuntimeOK`, `CreatesData` | the behavior assumed of the runtime `CreateDataProperty` on an array |
| `createLoop` | the `FastCreateDataProperty` loops in `ArrayOf` and `ArrayFrom` |
| `cloneFastJSArray false` | `CloneFastJSArray` in `src/codegen/code-stub-assembler.cc` with `HoleConversionMode::kDontConvert`, as the `CloneFastJSArray` builtin calls it |
| `cloneFastJSArray true` | the same function with `HoleConversionMode::kConvertToUndefined`, as `CloneFastJSArrayFillingHoles` calls it |
| `cloneKind` | the elements kind choice of `CloneFastJSArray`, which uses `PACKED_ELEMENTS` when holes were converted and for every nonextensible kind |
| `CloneResult.ub` | `ExtractFixedArray` reading past the source backing store, since its `CopyElements`, `CopyFixedArrayElements` and raw double loads check their ranges only with `CSA_DCHECK` |
| `Result.fatal` of the users | a failed `CSA_CHECK` or Torque slice bounds check |
| `Result.ub` of the users | a write into a copy-on-write backing store or an unchecked access outside a backing store |

## Theorems

`fastCreateDataProperty_safe`. For every well-formed array, index and value,
`FastCreateDataProperty` never writes outside a backing store, never writes into
a copy-on-write backing store and never fails a bounds check.

`fastCreateDataProperty_spec`. It either stores the value, leaving a
well-formed array whose elements are the old elements with the value set at the
index, or appended when the index equals the length, with the same elements
kind and holes past the new length, or hands an array with unchanged contents to
the runtime. An appended Smi keeps a packed Smi array packed, because
`BuildAppendJSArray` writes exactly at the length.

`createLoop_spec`. A loop of these calls at indices `0, 1, ...`, falling back to
any runtime function satisfying `RuntimeOK`, ends with exactly the written
values as the first elements and leaves every element after them unchanged.

`clone_ne_ub` and `clone_spec`. `CloneFastJSArray` of a well-formed array never
reads past the backing store, and the copy is a well-formed, fast array with
the same length and the same elements, with holes turned into `undefined` in the
converting mode. A copy-on-write source shares its backing store, which stays
copy-on-write.

## Assumptions

`clone_spec` requires that the non-converting mode receives an array with a
fast elements kind. A holey nonextensible array would otherwise become a
`PACKED_ELEMENTS` copy that still contains holes. Every caller of the
non-converting mode checks a fast kind: `ArrayPrototypeConcat` and
`ArrayPrototypeSlice` through the `FastJSArrayForConcat` and
`FastJSArrayForCopy` casts, `IterableToListMayPreserveHoles` through
`IsFastJSArrayWithNoCustomIteration`, and the slice reductions in
`JSCallReducer` and `MaglevGraphBuilder` through `SupportsFastArrayIteration`,
which requires `IsFastElementsKind`. The remaining callers copy array literal
boilerplates.

`RuntimeOK` assumes that the runtime `CreateDataProperty` sets the element as
the specification does and leaves a well-formed array with holes past its
length. The model does not fix which elements kind the runtime chooses.

## Not modeled

Write barriers, the allocation of HeapNumbers during conversions and the
garbage collection it may trigger, allocation sites, and the float64
representation of doubles are not modeled.
