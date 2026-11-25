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

## Builtins

`ArrayFlat/README.md` covers `TryFastFlat` in `src/builtins/array-flat.tq`, and
`ArrayCopyWithin/README.md` covers `TryFastArrayCopyWithin` in
`src/builtins/array-copywithin.tq`.
