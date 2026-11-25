# Lean 4 model and safety proofs for the `Array.prototype.flat` fast path

This directory contains a machine-checked model of the Torque fast path
`TryFastFlat` in `src/builtins/array-flat.tq` and proofs of its safety
properties. The model builds on the shared library in `formal/Torque`, and
`formal/README.md` describes how to check the proofs.

## Files

| File | Contents |
| --- | --- |
| `ArrayFlat/Model.lean` | The reference semantics `flatSpec`, frames, `fetch` and the termination measure |
| `ArrayFlat/Lemmas.lean` | Spec, frame and measure lemmas shared by the proofs |
| `ArrayFlat/Machine.lean` | The three loops as step functions, their runs, `calcLength` and `tryFastFlat` |
| `ArrayFlat/Safety.lean` | Invariants, absence of undefined behavior, result well-formedness, functional correctness |
| `ArrayFlat/StackBound.lean` | Bounds on the explicit traversal stack |
| `ArrayFlat/Examples.lean` | Executable `#guard` checks on concrete heaps |

## Correspondence with `array-flat.tq`

| Lean | Torque |
| --- | --- |
| `fetch` | `index < currentLength`, `index >= fastOW.Get().length` bailout and `LoadElementNoHole` with `FoundHole` |
| `descend?` | `currentDepth > 0 && Is<JSArray>(element)` |
| `step1` | one iteration of the loops in `CalculateFlattenedLengthFast` |
| `calcLength` | entry of `CalculateFlattenedLengthFast`, including the packed numeric early return |
| `stepDbl` | one iteration of the `PACKED_DOUBLE_ELEMENTS` second pass in `TryFastFlat` |
| `stepGen` | one iteration of the `FixedArray` second pass in `TryFastFlat` |
| `finish` | the `targetIndex != flattenedLength` bailout and `NewJSArray` |
| `tryFastFlat` | `TryFastFlat` |
| `Frame` | the four stack entries `array`, `length`, `index`, `depth` |
| `Torque.blit` | `TorqueCopyElements` and single-slot stores into the result backing store |
| `Outcome.ub` | an out-of-bounds read or write, or `UnsafeCast<Number>` on a non-number |
| `Outcome.fatal` | `FatalProcessOutOfMemoryInvalidArrayLength` from `AllocateFixedArray` |

The `didDescend` flag and the `break`/`continue` structure of the Torque loops
are folded into the step functions: a descent makes the next step process the
new array, and an exhausted array pops the stack.

## Theorems

Termination. `Torque.run` is defined by well-founded recursion on a measure, and
each loop runs it with `frameMeasure`;
`step1_decreases`, `stepGen_decreases` and `stepDbl_decreases` show that every
step of each loop decreases it. The measure is computed by recursion on the
remaining depth, so the three loops terminate on every heap, including heaps
with cyclic arrays, without any well-formedness assumption.

`tryFastFlat_ne_ub`. On a well-formed heap, `TryFastFlat` never reads a source
backing store out of bounds, never writes or copies outside the result backing
store, and the double path applies `UnsafeCast<Number>` only to numbers. The
last property depends on the first pass: it holds because the first pass only
selects `PACKED_DOUBLE_ELEMENTS` when every flattened leaf is a number.

`tryFastFlat_ok`. When `TryFastFlat` returns an array, the array is
well-formed for its elements kind, the kind is one of `PACKED_SMI_ELEMENTS`,
`PACKED_DOUBLE_ELEMENTS` and `PACKED_ELEMENTS`, every slot of the backing store
is initialized, and the contents equal `flatSpec`, the result of the
specification's `FlattenIntoArray` on the same heap. In particular a
`PACKED_SMI_ELEMENTS` result never contains a heap object, and the uninitialized
`FixedDoubleArray` allocated in the double path is always fully written.

`tryFastFlat_ne_fatal`. The result backing store is never larger than
`FixedArray::kMaxLength`, under the assumption `hStale` described below.

`pass1_stack_bound` and `gen_stack_bound`. The first pass and the `FixedArray`
second pass never hold more than 1024 frames, that is 4096 stack entries.

`dbl_stack_bound`. The double second pass has no `kMaxFlatFastStackEntries`
check, yet it never holds more than 1025 frames when it runs after a successful
first pass. The proof bounds its nesting by the nesting of the first pass plus
one level for `PACKED_SMI_ELEMENTS` subarrays, which the double pass enters and
the first pass counts without entering.

`calcLength_ok`. Outside the packed numeric early return, the length computed
by the first pass equals the length of the flattened result.

## Assumptions

The proofs assume the shared heap invariants `HeapWF` described in
`formal/README.md`.

The heap is a single snapshot for the whole of `TryFastFlat`. No JavaScript
runs inside `TryFastFlat`, so `fastOW.Recheck()` and `PerformStackCheck()` are
modeled as no-ops. Garbage collection triggered by `AllocateHeapNumberWithValue`
does not change the values the model observes.

`hStale` covers the packed numeric early return, which reuses the length that
`ArrayPrototypeFlat` read before calling `ToInteger` on the depth argument.
That call can run user code, so the length can be stale. The assumption says
that this length is at most `FixedArray::kMaxLength` whenever the receiver is
`PACKED_SMI_ELEMENTS` or `PACKED_DOUBLE_ELEMENTS` at the time of the fast path.
It follows from three facts of V8 that the model does not encode: elements kind
transitions only generalize, a dictionary backing store only converts back to a
holey kind (`BestFittingFastElementsKind` in `src/objects/js-objects.cc`), and
a fast backing store never exceeds `kMaxFixedArrayCapacity`.

Casts of a subarray backing store to `FixedArray` or `FixedDoubleArray` are
modeled as succeeding. A failing cast only adds a bailout, which every theorem
already allows. `TrySmiSub(currentDepth, 1)` is omitted because the depth is
positive at that point. Numbers are abstract: `Val.num` stands for a heap
number and its float64 payload is not modeled.

`Config` fixes `kSmiMaxValue` and `FixedArray::kMaxLength`. The theorems hold
for every `Config`; `Examples.v8Config` uses 31-bit Smis and the
`kMaxFixedArrayCapacity` of non-lower-limits builds.

## Not covered

The slow path `FlattenIntoArraySlow`, `Array.prototype.flatMap`, the
compilation of Torque to machine code and the faithfulness of the hand
translation from Torque to Lean are outside the proofs.
