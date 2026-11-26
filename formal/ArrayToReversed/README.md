# Lean 4 model and safety proofs for `Array.prototype.toReversed`

This directory models `TryFastArrayToReversed` in
`src/builtins/array-to-reversed.tq` with its copy loops
`FastArrayToReversed` and `FastPackedDoubleArrayToReversed`, and proves that the
fast path never reads or writes outside a backing store, never lets a garbage
collection see an uninitialized slot, never aborts, and returns a well-formed
packed array holding the reversed elements with holes read as `undefined`. The
result type and the copy helpers come from `ArrayCopyCommon`, which this
library imports.

## Files

| File | Contents |
| --- | --- |
| `ArrayToReversed/Model.lean` | The element loads, the copy loop, the kind dispatch and the specification |
| `ArrayToReversed/Safety.lean` | Absence of undefined behavior and aborts, agreement with the specification, well-formedness |
| `ArrayToReversed/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-to-reversed.tq`

| Lean | Torque |
| --- | --- |
| `loadTagged` | `LoadElementOrUndefined` on a `FixedArray`, which reads a hole as `undefined` |
| `loadPackedDouble` | `elements.values[from].Value()` in `FastPackedDoubleArrayToReversed`, which goes to `unreachable` on `undefined` and on a hole |
| `loadHoleyDouble` | `LoadElementOrUndefined` on a `FixedDoubleArray`, which allocates a HeapNumber for each number |
| `Load.val v true` | a load that can allocate and so trigger a garbage collection |
| `revLoop` | the `while (k < length)` loop with `from = length - k - 1`, storing through `StoreElement<FixedArray>` or `StoreFixedDoubleArrayElement` |
| `copyReversed` | `FastArrayToReversed` and `FastPackedDoubleArrayToReversed`, with `AllocateFixedArray(kind, SmiUntag(length))` |
| `init` | `initializeArray`, the `FillFixedArrayWithSmiZero` that `FastArrayToReversed` runs for `HOLEY_DOUBLE_ELEMENTS` |
| `tryFast` | `TryFastArrayToReversed` |
| `a.fast = false` | `Cast<FastJSArray>(receiver) otherwise Slow` |
| `a.length = 0` | `if (array.length < 1) return ArrayCreate(0)` |
| `resultKind` | `PACKED_SMI_ELEMENTS` and `PACKED_DOUBLE_ELEMENTS` kept, every other kind copied into `PACKED_ELEMENTS` |
| `Result.slow` | `goto Slow` and `GenericArrayToReversed` |
| `specReversed` | the specification, which reads `Get(O, from)` for each `from` |

`JSArr.fast` stands for the `FastJSArray` cast, which already checks
`IsPrototypeInitialArrayPrototype` and `IsNoElementsProtectorCellInvalid`, so
the repeated checks before the holey kinds always pass and reading a hole as
`undefined` matches `Get`.

## Theorems

`tryFast_ne_ub` and `tryFast_ne_abort`. For every well-formed array whose
backing store length is at most `lim.maxLen`, the fast path has no undefined
behavior and does not abort.

`tryFast_done`. Under the same hypotheses, when the fast path returns `res`
for source `src`, `src = a`, `res` is well formed, satisfies
`JSArr.SlackHoles`, is not copy-on-write, has a packed kind and the length of
`a`, and its elements are `specReversed a.elems`.

`tryFast_cases`. For every well-formed array with `a.length ≤ lim.maxLen`, the
fast path either goes to the slow path, or returns an empty
`PACKED_SMI_ELEMENTS` array for length 0, or returns
`newArray (resultKind a.kind) (specReversed a.elems)`.

`Examples.lean` checks that copying `HOLEY_DOUBLE_ELEMENTS` without
initializing the copy is undefined behavior, since `LoadElementOrUndefined`
allocates while the copy still holds uninitialized slots, which is why
`FastArrayToReversed` takes `initializeArray`. It also checks that a hole or
`undefined` in a `PACKED_DOUBLE_ELEMENTS` array reaches `unreachable`, which
`JSArr.WF` rules out, and that the copy aborts above `lim.maxLen`.

## Assumptions

The array satisfies `JSArr.WF`, and its backing store length is at most
`lim.maxLen`, the `FixedArray::kMaxLength` limit of `AllocateFixedArray`.

## Not modeled

`ToObject`, `GetLengthProperty` and `GenericArrayToReversed` are outside the
model, and `LoadJSArrayElementsMap`, `NewJSArray` and the float64
representation of doubles are not modeled.
