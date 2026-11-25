# Lean 4 models and safety proofs for V8 Torque builtins

This directory is one Lake project with three libraries. `Torque` models the
heap objects and the Torque and CodeStubAssembler macros that several builtins
share. `ArrayFlat` and `ArrayCopyWithin` model one builtin each on top of it and
prove its safety properties. The proofs use only the Lean 4 core library.

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
| `Torque/ElementsKind.lean` | `Kind`, `Kind.isFast`, `Kind.isDouble`, `kindOk` | `ElementsKind` and the contents each kind allows |
| `Torque/JSArray.lean` | `JSArr`, `JSArr.elems`, `JSArr.WF`, `Heap`, `HeapWF`, `Config` | `JSArray`, its backing store, the `FastJSArrayForRead`, `FastJSArray` and `FastJSArrayForCopy` casts, and copy-on-write backing stores |
| `Torque/FixedArray.lean` | `blit`, `moveElements`, `ensureWritable` | `TorqueCopyElements`, `TorqueMoveElements` and `EnsureWriteableFastElements` |
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
sound as those ranges. `RangeProcessor` has an overload for
`TruncateCheckedNumberOrOddballToInt32` that intersects the input range with
`Int32`, which would give `[0, 2^31 - 1]` for an input in `[0, 3e9]` although
`ToInt32(3e9)` is negative. That overload takes no `ProcessingState`, so the
two-argument dispatch of `GraphProcessor` never selects it, and the generic
overload gives the node the full `Int32` range instead.

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

`ArrayFlat/README.md` covers `TryFastFlat` in `src/builtins/array-flat.tq`, and
`ArrayCopyWithin/README.md` covers `TryFastArrayCopyWithin` in
`src/builtins/array-copywithin.tq`.
