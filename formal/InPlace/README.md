# Lean 4 model and safety proofs for the in-place mutation helpers

`InPlace` models the element loads, stores, moves, copies, copy-on-write
handling and elements kind transitions that the builtins mutating an array in
place share, and proves the lemmas they need about them once. `ArrayReverse`,
`ArrayShift`, `ArrayUnshift` and `ArraySplice` build on it.

## Files

| File | Contents |
| --- | --- |
| `InPlace/Model.lean` | The result types, map checks, slot accesses, moves and copies, `EnsureWriteableFastElements` and the kind transition |
| `InPlace/Lemmas.lean` | In-bounds behavior of the accesses, properties of the writable copy and of transitions, well-formedness of new arrays |

## Correspondence with the V8 sources

| Lean | V8 |
| --- | --- |
| `Result.done` | the array after the builtin and its return value |
| `Result.slow` | the jump to the generic or runtime implementation of a builtin |
| `Result.throws` | a JavaScript exception |
| `Result.ub`, `Res.ub` | undefined behavior: a write into a copy-on-write backing store, or a move or copy outside a backing store that is checked only with `CSA_DCHECK` |
| `Result.abort`, `Res.abort` | a failed bounds check, `unreachable` or a failed `CHECK` |
| `MapInfo.lengthWritable` | `EnsureArrayLengthWritable` in `src/builtins/array.tq`, which rejects a dictionary map and a read-only `length` |
| `MapInfo.pushable` | `EnsureArrayPushable` in `src/codegen/code-stub-assembler.cc`, which adds `IsExtensibleNonPrototypeMap` |
| `loadSlot`, `storeSlot` | element accesses through bounds-checked Torque slices |
| `memmove` | `MoveElements` through `TorqueMoveElements` and `FastJSArrayWitness.MoveElements` |
| `memcpy` | `CopyElements` through `TorqueCopyElements` |
| `castElements` | the `Cast<FixedDoubleArray>` of the backing store with `otherwise unreachable` in the `FastJSArrayWitness` methods, which fails on `empty_fixed_array` |
| `ensureWritableChecked` | `EnsureWriteableFastElements` in `src/builtins/array.tq`, with its `Cast<Smi>(array.length) otherwise unreachable` and `ExtractFixedArray` |
| `Torque.ensureWritable` | the copy that replaces a copy-on-write backing store |
| `transitionTo` | `TransitionElementsKindImpl` in `src/objects/elements.cc`, which makes the target holey for a holey source, only changes the map for `empty_fixed_array` or the same representation, and converts the backing store otherwise |
| `newArray` | a new fast array whose backing store has exactly its length |

## Theorems

`loadSlot_nat`, `storeSlot_nat`, `memmove_ok`, `memcpy_ok` and
`castElements_ok`. In bounds and without a copy-on-write backing store, the
accesses return the expected list, and the cast succeeds when a double kind has
a non-empty backing store.

`ensureWritableChecked_ok`. For a well-formed array with a backing store length
of at most `c.maxLen` and `c.maxLen ≤ c.smiMax`, `ensureWritableChecked`
succeeds with `ensureWritable a`. `ensureWritableChecked_cases` shows that it
otherwise only aborts. `ensureWritable_wf`, `ensureWritable_slack`,
`ensureWritable_cow`, `ensureWritable_kind`, `ensureWritable_length` and
`ensureWritable_elems` show that the writable copy is well formed, preserves
`JSArr.SlackHoles`, is not copy-on-write, and keeps the kind, the length and the
elements.

`transitionTo_spec`. For a well-formed array, `transitionTo` has no undefined
behavior, and a result satisfies `Transitioned`: its kind is
`a.kind.transitionTarget k`, its backing store, length and flags are those of
`a`, and it is not copy-on-write when its kind is a double kind or when `a` was
not. `transitionTo_ok` shows that it succeeds when the backing store length is
at most `c.maxLen`, and `transitionTo_cases` that it otherwise only aborts.

`cow_false_of_double`. A well-formed array with a double kind is not
copy-on-write.

`newArray_wf`, `newArray_slack` and `newArray_elems`. A new array of a fast
kind whose values the kind allows is well formed, satisfies `JSArr.SlackHoles`
and has the given elements.

## Assumptions

The lemmas take only the explicit bounds above and, where stated, `JSArr.WF`
or `JSArr.SlackHoles`. A well-formed array is never copy-on-write with a double
kind, as `EnsureWriteableFastElements` states.

## Not modeled

Write barriers, the allocation of new backing stores, map transitions beyond the
elements kind and the float64 representation of doubles are outside the model.
