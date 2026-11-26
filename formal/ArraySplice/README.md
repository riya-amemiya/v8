# Lean 4 model and safety proofs for `Array.prototype.splice`

This directory models `ArrayPrototypeSplice` in `src/builtins/array-splice.tq`
from the computation of `actualStart` on and its fast path `FastArraySplice`
with `FastSplice`, and proves that the fast path never has undefined behavior
and that, when it returns, the array holds the elements before the start, the
inserted items and the elements after the deleted range, with holes past its
length, and the returned array holds the deleted elements. The accesses, the
map checks, the copy-on-write handling and the kind transition come from
`InPlace`, which this library imports.

## Files

| File | Contents |
| --- | --- |
| `ArraySplice/Model.lean` | The argument forms, the kind transition, the extraction of the deleted elements, the element shuffle, the insertion, the fast path and the specification |
| `ArraySplice/Safety.lean` | Absence of undefined behavior, agreement with the specification, well-formedness |
| `ArraySplice/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-splice.tq`

| Lean | Torque |
| --- | --- |
| `Args` | the cases `arguments.length == 0`, `arguments.length == 1` and two or more arguments |
| `actualStart`, `actualDeleteCount` | steps 4 to 7 of `ArrayPrototypeSplice` |
| `fastPath` | `ArrayPrototypeSplice` from the `kMaxSafeInteger` check to the call of `FastArraySplice` |
| `tryFast` | `FastArraySplice` |
| `c.smiMax < len ∨ c.smiMax < start ∨ c.smiMax < adc` | the `Cast<Smi>` of `originalLengthNumber`, `actualStartNumber` and `actualDeleteCountNumber` |
| `c.smiMax < len + xs.length - adc` | the Smi addition `originalLength + lengthDelta` overflowing, which `SmiAdd` from `SMI_ARITHMETIC_BINOP` in `src/codegen/code-stub-assembler.h` does not check |
| `a.forCopy = false` | `Cast<JSArray>`, `IsPrototypeInitialArrayPrototype`, `IsNoElementsProtectorCellInvalid`, `IsArraySpeciesProtectorCellInvalid` and `IsFastElementsKind`, the conditions of the `FastJSArrayForCopy` cast |
| `m.pushable = false` | `EnsureArrayPushable(map) otherwise Bailout` |
| `insertionKind`, `isSmiKind`, `isHeapNumber`, `allowDouble`, `allowNonNumber`, `transitionForInsertion` | `TransitionElementsKindForInsertionIfNeeded`, with `IsFastSmiElementsKind`, `IsHeapNumber`, `AllowDoubleElements`, `AllowNonNumberElements` and `TransitionElementsKindWithKind` |
| `c.smiMax < b.length`, `len ≠ b.length` | `Cast<Smi>(a.length) otherwise Bailout` and `if (originalLength != length) goto Bailout` |
| `extract` | `ExtractFastJSArray(context, a, actualStart, actualDeleteCount)` |
| `len + xs.length - adc = 0` | `if (newLength == 0)`, which sets `a.elements = kEmptyFixedArray` and `a.length = 0` |
| `fastSplice` | `FastSplice`, starting with `EnsureWriteableFastElements` |
| `shuffle` | the moves of `FastSplice`: `DoMoveElements` and `StoreHoles` to shrink, `DoMoveElements` when the backing store is large enough, and `Extract` with `CalculateNewElementsCapacity` and `DoCopyElements` to grow |
| `newCapacity` | `CalculateNewElementsCapacity` |
| `extractGrow` | both `Extract` macros, including the `EmptyFixedArray` case that allocates `AllocateFixedDoubleArrayWithHoles` |
| `storeHoles` | `StoreHoles`, through `StoreArrayHole` |
| `insertLoop` | `InsertArgumentsIntoFastPackedArray`, whose `UnsafeCast<ElementType>` of a non-number into a `FixedDoubleArray` is undefined behavior |
| `Result.slow` | `Bailout` and `SlowSplice` |
| `Result.throws` | `ThrowTypeError(MessageTemplate::kInvalidArrayLength)` |
| `specSplice` | the new elements and the deleted elements |

## Theorems

`fastPath_spec`. For every well-formed array with holes past its length whose
backing store has at most `c.maxLen` slots, every length and every argument
form, when `c.maxLen ≤ c.smiMax` and
`newCapacity (c.maxLen + args.items.length) ≤ c.smiMax`, the fast path has no
undefined behavior, aborts only when the grown backing store would need more
than `c.maxLen` slots, and when it returns `a'` and `d`, `a'` is well formed,
satisfies `JSArr.SlackHoles`, has the new length and the elements of
`specSplice` at the actual start and delete count, and `d` is well formed with
the deleted elements. That abort is the `FatalProcessOutOfMemoryInvalidArrayLength`
call of `AllocateFixedArray` in `src/codegen/code-stub-assembler.cc`, which
V8 performs for any backing store above `FixedArray::kMaxLength`. Whenever the
grown backing store fits, no bounds check, `unreachable` or other abort occurs.

`tryFast_spec` states the same for explicit start and delete count satisfying
`Bounds`, and `actual_range` shows
`actualStart len args.startArg + actualDeleteCount len args ≤ len`, the
`range` field of `Bounds` for the arguments `fastPath` passes.

`Examples.lean` checks
that `insertLoop` is undefined behavior when it stores a non-number into a
double backing store, which is why the kind transition runs before the
insertion, that `memmove` past the backing store is undefined behavior, and
that a copy-on-write array is copied before it is modified.

## Assumptions

The array satisfies `JSArr.WF` and `JSArr.SlackHoles`. `c.maxLen` stands for
`kMaxFixedArrayCapacity` in `src/objects/fixed-array-base.h`, 128 Mi slots,
which bounds every backing store, and `c.smiMax` for the Smi maximum,
`2^30 - 1` with pointer compression. `newCapacity (c.maxLen + k) ≤ c.smiMax`
then holds for every argument count `k` up to 581610143, far more than
the stack allows, so `CalculateNewElementsCapacity` of the new length is a Smi.

## Not modeled

`ToObject`, `GetLengthProperty`, `ToInteger_Inline`, `SlowSplice`, write
barriers and the float64 representation of doubles are outside the model. `MapInfo` stands for the map bits
`EnsureArrayPushable` reads.
