# Lean 4 model and safety proofs for `Array.prototype.toSpliced`

This directory models `ArrayPrototypeToSpliced` in
`src/builtins/array-to-spliced.tq` from the computation of `actualStart` on,
its fast path `TryFastArrayToSpliced` with `CopyFastPackedArrayForToSpliced`,
and the insertion helpers it shares with `src/builtins/array-splice.tq`. It
proves that the fast path never has undefined behavior and never aborts, and
that it returns a well-formed packed array holding the elements before the
start, the inserted items and the elements after the deleted range. The result
type and the copy helpers come from `ArrayCopyCommon`, which this library
imports.

## Files

| File | Contents |
| --- | --- |
| `ArrayToSpliced/Model.lean` | The argument forms, the copy, the kind transition, the insertion, the fast path and the specification |
| `ArrayToSpliced/Safety.lean` | Absence of undefined behavior and aborts, agreement with the specification, well-formedness |
| `ArrayToSpliced/Examples.lean` | Executable `#guard` checks |

## Correspondence with the V8 sources

| Lean | V8 |
| --- | --- |
| `Args` | the cases `arguments.length == 0`, `arguments.length == 1` and two or more arguments |
| `actualStart`, `actualDeleteCount`, `newLen` | steps 3 to 11 in `ArrayPrototypeToSpliced` |
| `fastPath` | `ArrayPrototypeToSpliced` from the `kMaxSafeInteger` check on |
| `newLen len args = 0` | `if (newLen == 0) return ArrayCreate(0)` |
| `lim.maxFast < newLen len args` | `if (newLen > kMaxFastArrayLength) goto Slow` |
| `tryFast` | `TryFastArrayToSpliced` |
| `r.max < nl ∨ r.max < st ∨ r.max < dc`, `r.max < len` | the `Cast<Smi>` of `newLenNumber`, `actualStartNumber`, `actualDeleteCountNumber` and `originalLenNumber` |
| `a.fast = false` | `Cast<FastJSArray>(o) otherwise Slow` |
| `a.length < len` | `if (originalLen > array.length) goto Slow` |
| `isFastPacked a.kind = false` | `if (!IsFastPackedElementsKind(elementsKind)) goto Slow` |
| `copyForToSpliced` | `CopyFastPackedArrayForToSpliced`, with `AllocateFixedArray(kind, newLen)` and two `CopyElements`, whose ranges are checked only with `CSA_DCHECK` |
| `fillZero` | `FillFixedArrayWithSmiZero` and `FillFixedDoubleArrayWithZero` for the slots of the inserted items |
| `insertKind`, `isSmiKind`, `isHeapNumber`, `allowDouble`, `allowNonNumber` | `TransitionElementsKindForInsertionIfNeeded` in `array-splice.tq`, with `IsFastSmiElementsKind`, `IsHeapNumber`, `AllowDoubleElements` and `AllowNonNumberElements` |
| `transitionCopy` | `TransitionElementsKindWithKind`, which aborts when the conversion of a backing store above `lim.maxLen` fails |
| `insertLoop` | `InsertArgumentsIntoFastPackedArray`, whose `UnsafeCast<ElementType>` of a non-number into a `FixedDoubleArray` is undefined behavior |
| `Result.slow` | `Slow` and `GenericArrayToSpliced` |
| `Result.throws` | `ThrowTypeError(MessageTemplate::kInvalidArrayLength)` |
| `specSpliced` | the loops of `GenericArrayToSpliced`, which read `GetProperty(o, i)` and `GetProperty(o, r)` |

`fastPath` takes the length `len` read before the argument coercions and the
array as it is after them as independent inputs.

## Theorems

`fastPath_ne_ub` and `fastPath_ne_abort`. For every well-formed array, every
length and every argument form, when `lim.maxFast ≤ lim.maxLen`, the fast path
has no undefined behavior and does not abort.

`fastPath_done`. Under the same hypotheses, when the fast path returns `res`
for source `src`, `src = a`, `res` is well formed, satisfies
`JSArr.SlackHoles`, is not copy-on-write, has a packed kind and length
`newLen len args`, and its elements are `specSpliced a.elems len` applied to
the actual start, the actual delete count and the items.

`fastPath_cases` and `tryFast_cases`. The fast path throws, goes to the slow
path, returns the empty array for a new length of 0, or returns an array of
kind `insertKind a.kind` with the specified elements and contents its kind
allows.

`Examples.lean` checks that `insertLoop` is undefined behavior when it stores a
non-number into a double copy, which is why the kind transition runs before
the insertion, and that `copyForToSpliced` is undefined behavior when the
source is shorter than the length it is told to copy, which is why the fast
path checks `originalLen > array.length`.

## Assumptions

The array satisfies `JSArr.WF`, and `lim.maxFast ≤ lim.maxLen`. `js-array.h`
states the second fact as `static_assert(kMaxFastArrayLength <= kMaxFixedArrayCapacity)`,
and `FixedArray::kMaxLength` is `kMaxFixedArrayCapacity`.

## Not modeled

`ToObject`, `GetLengthProperty`, `ToInteger_Inline`, `GenericArrayToSpliced`,
`LoadJSArrayElementsMap`, `NewJSArray` and the float64 representation of
doubles are outside the model.
