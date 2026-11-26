# Lean 4 model and safety proofs for the copying helpers of `toReversed`, `with`, `toSpliced` and `slice`

`ArrayCopyCommon` models the copying helpers and the result type that the
builtins returning a new array share, and proves the lemmas they need about
them once. `ArrayToReversed`, `ArrayWith`, `ArrayToSpliced` and `ArraySlice`
build on it. `ArraySlice` also imports `ArrayBuild` for `CloneFastJSArray`.

## Files

| File | Contents |
| --- | --- |
| `ArrayCopyCommon/Basic.lean` | Limits, the result type, hole conversion, index clamping, element copies and stores, `ExtractFastJSArray` and `CloneFastJSArray` |
| `ArrayCopyCommon/Lemmas.lean` | Lemmas on copies, the reference slice and well-formedness of new arrays |

## Correspondence with the V8 sources

| Lean | V8 |
| --- | --- |
| `Limits.maxLen` | `FixedArray::kMaxLength`, above which `AllocateFixedArray` calls `Runtime::kFatalProcessOutOfMemoryInvalidArrayLength` |
| `Limits.maxFast` | `kMaxFastArrayLength` |
| `Result.done` | a result array, with the source array as the fast path left it |
| `Result.slow` | the jump to the generic implementation of a builtin |
| `Result.throws` | a JavaScript exception |
| `Result.ub` | undefined behavior, such as an access outside a backing store that is checked only with `CSA_DCHECK` |
| `Result.abort` | a failed bounds check, `unreachable` or an out-of-memory abort |
| `holeToUndef`, `getOrUndef` | reading a hole as `undefined`, as `LoadElementOrUndefined` and `ReplaceTheHoleWithUndefined` in `src/builtins/array.tq` do |
| `isFastPacked` | `IsFastPackedElementsKind` |
| `newArray` | a new fast array whose backing store has exactly its length |
| `relIndex` | `relativeStart < 0 ? Max((len + relativeStart), 0) : Min(relativeStart, len)` and the same clamping of the end |
| `copyElements` | `CopyElements` in `src/codegen/code-stub-assembler.cc`, whose ranges are checked only with `CSA_DCHECK` |
| `storeChecked` | an element store through a bounds-checked Torque slice |
| `extractFast` | `ExtractFastJSArray` in `src/codegen/code-stub-assembler.cc`, which copies with `ExtractFixedArray` and keeps the source kind |
| `cloneFast` | `CloneFastJSArray`, which shares a copy-on-write backing store instead of copying it |
| `specSlice` | the elements `k` to `k + n - 1` of a list, with holes and indices past its end absent |

`ExtractFastJSArray` and `CloneFastJSArray` assume a fast array, so a
non-fast argument gives `ub`.

## Theorems

`extractFast_eq`. For a fast array whose length is at most its backing store
length, and `k + n ≤ a.length` and `n ≤ lim.maxLen`, `extractFast` returns a
new array of the source kind whose elements are `specSlice a.elems k n`.

`cloneFast_eq`. For a well-formed fast array with `a.length ≤ lim.maxLen`,
`cloneFast` returns an array that shares the copy-on-write backing store when
the source is non-empty and copy-on-write, and otherwise a new array whose
elements are `a.elems`.

`newArray_wf`, `newArray_slack` and `newArray_elems`. A new array of a fast
kind whose values the kind allows is well formed, satisfies `JSArr.SlackHoles`
because its backing store has no slots past its length, and has the given
elements. `kindOk_specSlice` shows that the values of a slice
of a well-formed array are allowed by its kind.

The remaining lemmas, `copyElements_eq`, `storeChecked_eq`,
`take_drop_eq_specSlice`, `specSlice_store` and the others, give the result of
in-bounds copies and stores and relate the backing store to the elements below
the length.

## Assumptions

The lemmas take only the explicit bounds above and, for `cloneFast_eq` and
`kindOk_specSlice`, `JSArr.WF`.

## Not modeled

The allocation of the result arrays, write barriers and the float64
representation of doubles are outside the model. `ArraySlice` uses the
`CloneFastJSArray` model of `ArrayBuild`, not `cloneFast`.
