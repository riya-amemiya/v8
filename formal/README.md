# Lean 4 models and safety proofs for V8 builtins

This directory is one Lake project. `Torque` models the heap objects and the
Torque and CodeStubAssembler macros that several builtins share. `ArrayBuild`,
`ArrayWitness`, `ArrayCopyCommon` and `InPlace` model the element stores, the
witness-based iteration loop, the copying helpers and the in-place mutation
helpers that several Array builtins share. Every other library models one
builtin, or one group of builtins that share a Torque file, on top of them and
proves its safety properties. The proofs use only the Lean 4 core library.

## Checking the proofs

The toolchain is pinned in `lean-toolchain` (Lean 4.36.0).

```bash
cd formal
lake build
```

A successful build means every theorem is proved. `#print axioms` on the main
theorems reports only `propext`, `Quot.sound` and `Classical.choice`.

## Shared library

| File | Contents | V8 counterpart |
| --- | --- | --- |
| `Torque/Value.lean` | `Val`, `Val.isSmi`, `Val.isNumber` | `Smi`, `HeapNumber`, `JSArray`, `JSProxy` and other `JSAny` values |
| `Torque/ElementsKind.lean` | `Kind`, `Kind.isFast`, `Kind.isDouble`, `kindOk`, `Kind.isHoley`, `Kind.toHoley`, `Kind.isMoreGeneral`, `Kind.moreGeneral`, `Kind.transitionTarget`, `optimalKind` | `ElementsKind`, the contents each kind allows, `GetHoleyElementsKind`, `IsMoreGeneralElementsKindTransition`, `GetMoreGeneralElementsKind`, the holey adjustment of `JSObject::TransitionElementsKind`, and `Object::OptimalElementsKind` |
| `Torque/JSArray.lean` | `JSArr`, `JSArr.elems`, `JSArr.WF`, `JSArr.SlackHoles`, `Heap`, `HeapWF`, `Config` | `JSArray`, its backing store, the holes past its length, the `FastJSArrayForRead`, `FastJSArray` and `FastJSArrayForCopy` casts, and copy-on-write backing stores |
| `Torque/FixedArray.lean` | `blit`, `moveElements`, `ensureWritable`, `growTo` | `TorqueCopyElements`, `TorqueMoveElements`, `EnsureWriteableFastElements`, and a backing store grown with holes |
| `Torque/Smi.lean` | `SmiRepr`, `SmiRepr.add`, `SmiRepr.above`, `SmiRepr.greaterThan` | Smi tagging, `SmiAdd`, `SmiAbove` and `SmiGreaterThan` in `src/codegen/code-stub-assembler.h` |
| `Torque/Machine.lean` | `Step`, `Outcome`, `run`, `Reach` | the loop structure of a builtin, its bailouts and its exits |

`SmiRepr.compressed` is the 31-bit Smi layout of pointer compression and
`SmiRepr.full` the 32-bit Smi layout of 64-bit words. `SmiRepr.above_add_iff`
shows that `SmiAbove(a + b, l)` computed on tagged words equals `a + b > l` for
all non-negative Smis, in both layouts.

## Shared assumptions

`HeapWF` states the heap invariants the proofs rely on. Every fast array has
`length` at most its backing store length, which `JSArray::JSArrayVerify` checks
for fast elements unless the backing store is `empty_fixed_array`. Packed kinds
hold no holes, Smi kinds hold only Smis, `PACKED_DOUBLE_ELEMENTS` holds only
numbers and `HOLEY_DOUBLE_ELEMENTS` may additionally hold `undefined`. An array
passing the `FastJSArrayForRead` cast does not have dictionary elements,
`FastJSArray` implies `FastJSArrayForRead`, and `FastJSArrayForCopy` implies
`FastJSArray`. The model represents a nonextensible kind by the
`PACKED_ELEMENTS` or `HOLEY_ELEMENTS` kind with the same reads, with
`JSArr.fast` false. A
copy-on-write backing store never has a double elements kind, as
`EnsureWriteableFastElements` in `src/builtins/array.tq` states.

`JSArray::JSArrayVerify` relaxes the length premise when the backing store is
`empty_fixed_array`. None of the code read for this premise leaves a fast array
with a length above its backing store length. The creation paths read are
`Factory::NewJSArray`, `Factory::NewJSArrayStorage`, `v8::Array::New`, the
callers of the CSA `AllocateJSArray` overloads in `src/builtins`, `src/codegen`
and `src/interpreter`, `JSCreateLowering::ReduceNewArray` in TurboFan, and
`BuildAndAllocateJSArray` with `AllocateElementsArray` in Maglev. The length
writers read are `SetLengthImpl` in `src/objects/elements.cc`,
`JSObject::AddDataElement`, both `BuildAppendJSArray` overloads,
`ArrayPrototypePop`, the growing branch of `EmitElementStore`,
`ArrayConcatVisitor::ToArray`, `StringToList`, `FastSplice`, and in Maglev
`TryReduceArrayPrototypePush`, `TryReduceArrayPrototypePop` and the growing
keyed store of `TryBuildElementStoreOnJSArrayOrJSObject`, whose
`UpdateJSArrayLength` Turbolev lowers to the Turboshaft operation of the same
name. Each of them allocates or grows the backing store before it raises the
length, or only lowers the length. `BuildAppendJSArray` in
`src/codegen/code-stub-assembler.cc` names another bug or in-sandbox memory
corruption as the way a length above the backing store length arises.

`UpdateJSArrayLength` has one producer, the growing keyed store, where
`MaybeGrowFastElements` runs first and either leaves a backing store longer than
the index, through `TryGrowElementsCapacity` or `Runtime_GrowArrayElements`, or
deoptimizes. Turboshaft gives `MaybeGrowFastElementsOp` the `CanCallAnything`
effects, and no Turboshaft reducer other than its lowering rewrites it. The
Maglev graph optimizer replaces `UpdateJSArrayLength` by its length input only
when it shows `index < length`. One of its arguments is a `LessEqualConstraint`,
which `maglev-range-analysis.h` records only on the true branch of a strict
`<`, so the fact it carries is strict although the name says less or equal. The
removal of an unsigned `CheckInt32Condition` in the same optimizer relies on the
same strictness.

These two places are the only readers of `LessEqualConstraint`. The range
analysis records it only for a `BranchIfInt32Compare` with `kLessThan`, on the
true successor, which split-edge form gives a single predecessor. The constraint
stays in that block, because `Join` copies ranges but not constraints, a query
looks only at the current block, and a block spliced in after the analysis
answers no. Both readers also require the ranges of both operands to lie in
`Uint32`, which turns the signed `<` into the unsigned one, so they are only as
sound as those ranges.

`RangeProcessor` has one overload that the dispatch never reaches. Every other
`Process` overload takes the node and a `ProcessingState`, which is what
`GraphProcessor` passes through `DispatchNodeBase`, but the overload for
`TruncateCheckedNumberOrOddballToInt32` takes the node alone. The template
overload therefore handles that node and records the full `Int32` range, and
`GetStaticRangeFor` gives it `Int32` as well, because it is not a conversion
node. The unreachable overload intersects the input range with `Int32`, which
is wrong for `ToInt32`, since inputs from `2^31` to `2^32 - 1` truncate to
negative values. An input range with a non-negative minimum and a maximum above
`INT32_MAX`, which a tagged value from `Uint32ToNumber` can have, would come out
non-negative, and the removal of an unsigned `CheckInt32Condition` would then
drop the bounds check of a negative index after `i < a.length`. Adding the
missing parameter to that overload would turn this on.

The other truncating nodes get sound ranges. `TruncateUint32ToInt32`,
`TruncateFloat64ToInt32` and `TruncateHoleyFloat64ToInt32` are not conversion
nodes and get the full `Int32` range, the wrapping arithmetic nodes widen to
`Int32` on overflow through `UnionUpdateTruncatingInt32`, and
`Range::ShiftLeft` returns `All` whenever the shift can overflow. The range
analysis and the graph optimizer that reads it run only in the Turbolev frontend
pipeline, which `--turbolev` or `--turbolev-future` enables and which is off by
default. `--maglev-assert` turns on `--maglev-range-verification`, which inserts
`AssertRangeInt32` after each Int32 node whose range is neither all nor empty,
so a wrong range for a truncation would abort at run time under that flag.

When the premise fails, both fast paths access memory outside a backing store
in a release build. `TryFastFlat` copies a `PACKED_SMI_ELEMENTS` or
`PACKED_DOUBLE_ELEMENTS` subarray with `TorqueCopyElements`, and `CopyElements`
checks the source range only with `CSA_DCHECK`, so the copy reads past the
source backing store. Its element-by-element reads go through Torque slices,
whose `AtIndex` stops the process on an out-of-bounds index instead.
`TryFastArrayCopyWithin` hands its indices to `MoveElements`, which also checks
them only with `CSA_DCHECK`, so the move reads and writes outside the backing
store. The `Examples.lean` of both builtins check these cases on a fast array
with length 3 and an empty backing store.

## Builtins

| Library | Builtin | Source |
| --- | --- | --- |
| `ArrayFlat` | `Array.prototype.flat` | `TryFastFlat` in `src/builtins/array-flat.tq` |
| `ArrayCopyWithin` | `Array.prototype.copyWithin` | `src/builtins/array-copywithin.tq` |
| `ArrayFill` | `Array.prototype.fill` | `TryFastArrayFill` in `src/builtins/builtins-array.cc` and the elements accessors it calls |
| `ArrayBuild` | shared by `concat`, `Array.of` and `Array.from` | `FastCreateDataProperty` in `src/builtins/base.tq` and `CloneFastJSArray` in `src/codegen/code-stub-assembler.cc` |
| `ArrayAt` | `Array.prototype.at` | `src/builtins/array-at.tq` |
| `ArrayConcat` | `Array.prototype.concat` | `src/builtins/array-concat.tq` |
| `ArrayLastIndexOf` | `Array.prototype.lastIndexOf` | `src/builtins/array-lastindexof.tq` |
| `ArrayOf` | `Array.of` | `src/builtins/array-of.tq` |
| `ArrayFrom` | `Array.from` | `src/builtins/array-from.tq` and the array and string branches of `FastIterableToList` |
| `ArrayIsArray` | `Array.isArray` | `src/builtins/array-isarray.tq` |
| `ArrayFromCollections` | the Map and Set branches of `Array.from` | `FastIterableToList` in `src/builtins/builtins-iterator-gen.cc`, `MapIteratorToList` and `SetOrSetIteratorToList` in `src/builtins/builtins-collections-gen.cc` |
| `ArrayWitness` | shared by the iteration builtins below | `FastJSArrayWitness` in `src/objects/js-array.tq` |
| `ArrayEvery` | `Array.prototype.every` | `src/builtins/array-every.tq` |
| `ArraySome` | `Array.prototype.some` | `src/builtins/array-some.tq` |
| `ArrayForEach` | `Array.prototype.forEach` | `src/builtins/array-foreach.tq` |
| `ArrayFind` | `Array.prototype.find` | `src/builtins/array-find.tq` |
| `ArrayFindIndex` | `Array.prototype.findIndex` | `src/builtins/array-findindex.tq` |
| `ArrayFindLast` | `Array.prototype.findLast` | `src/builtins/array-findlast.tq` |
| `ArrayFindLastIndex` | `Array.prototype.findLastIndex` | `src/builtins/array-findlastindex.tq` |
| `ArrayReduce` | `Array.prototype.reduce` | `src/builtins/array-reduce.tq` |
| `ArrayReduceRight` | `Array.prototype.reduceRight` | `src/builtins/array-reduce-right.tq` |
| `ArrayFilter` | `Array.prototype.filter` | `src/builtins/array-filter.tq` |
| `ArrayMap` | `Array.prototype.map` | `src/builtins/array-map.tq` |
| `ArrayFlatMap` | `Array.prototype.flatMap` | `ArrayPrototypeFlatMap` in `src/builtins/array-flat.tq` |
| `ArrayCopyCommon` | shared by `toReversed`, `with`, `toSpliced` and `slice` | the copying helpers those builtins call |
| `ArrayToReversed` | `Array.prototype.toReversed` | `src/builtins/array-to-reversed.tq` |
| `ArrayWith` | `Array.prototype.with` | `src/builtins/array-with.tq` |
| `ArrayToSpliced` | `Array.prototype.toSpliced` | `src/builtins/array-to-spliced.tq` |
| `ArraySlice` | `Array.prototype.slice` | `src/builtins/array-slice.tq` |
| `InPlace` | shared by `reverse`, `shift`, `unshift` and `splice` | the in-place stores, moves and transitions those builtins perform |
| `ArrayReverse` | `Array.prototype.reverse` | `src/builtins/array-reverse.tq` |
| `ArrayShift` | `Array.prototype.shift` | `src/builtins/array-shift.tq` |
| `ArrayUnshift` | `Array.prototype.unshift` | `src/builtins/array-unshift.tq` |
| `ArraySplice` | `Array.prototype.splice` | `src/builtins/array-splice.tq` |
| `ArrayJoin` | `Array.prototype.join`, `toString` and `toLocaleString` | `src/builtins/array-join.tq` and `WriteChunkListToFlat` in `src/objects/objects.cc` |
| `ArrayFromAsync` | `Array.fromAsync` | `src/builtins/array-from-async.tq` |
| `ArraySort` | `Array.prototype.sort`, `toSorted` and the inlined sort continuations | `third_party/v8/builtins/array-sort.tq`, `src/builtins/array-to-sorted.tq` and the continuations in `src/builtins/array.tq` |

Each library has a `README.md` with the correspondence to the V8 sources, the
theorems, the assumptions and what is not modeled.
