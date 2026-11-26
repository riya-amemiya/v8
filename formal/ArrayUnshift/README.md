# Lean 4 model and safety proofs for `Array.prototype.unshift`

`ArrayPrototypeUnshift` in `src/builtins/array-unshift.tq` checks the receiver
and tail calls the C++ builtin `ArrayUnshift` in
`src/builtins/builtins-array.cc`, which transitions the elements kind in
`MatchArrayElementsKindToArguments` and inserts the arguments through
`FastElementsAccessor::AddArguments` in `src/objects/elements.cc`. This
directory models that chain and proves that it never reads or writes outside a
backing store and never writes into a copy-on-write backing store, and that it
leaves a well-formed array with holes past its length holding the arguments
followed by the old elements. The accesses, the map checks, the copy-on-write
handling and the kind transition come from `InPlace`, which this library
imports.

## Files

| File | Contents |
| --- | --- |
| `ArrayUnshift/Model.lean` | The kind matching, the capacity computation, the insertion, the builtin and the specification |
| `ArrayUnshift/Safety.lean` | Absence of undefined behavior and aborts, agreement with the specification, well-formedness, the throwing case |
| `ArrayUnshift/Examples.lean` | Executable `#guard` checks |

## Correspondence with the V8 sources

| Lean | V8 |
| --- | --- |
| `unshift` | `ArrayPrototypeUnshift` followed by the C++ `ArrayUnshift` |
| `a.fast = false` | `Cast<FastJSArray>(receiver) otherwise Slow` |
| `ensureWritableChecked` | `array::EnsureWriteableFastElements(array)` |
| `m.extensible`, `m.lengthWritable` | `IsExtensibleMap(map)` and `EnsureArrayLengthWritable(map) otherwise Slow` |
| `argsKind`, `isObjectKind`, `matchKind` | `MatchArrayElementsKindToArguments`, which leaves object kinds alone and otherwise picks `PACKED_DOUBLE_ELEMENTS` for a HeapNumber and `PACKED_ELEMENTS` for any other heap object |
| `transitionTo` | `JSObject::TransitionElementsKind` |
| `xs = []` | `if (to_add == 0) return array->length()` |
| `addArguments` | `AddArguments` with `AT_START` |
| `newElementsCapacity` | `JSObject::NewElementsCapacity`, with `c.maxLen` for `kMaxFixedArrayCapacity` |
| `grownStore` | `ConvertElementsWithCapacity` with `copy_dst_index` equal to the number of arguments |
| `Result.throws` | the RangeError `ConvertElementsWithCapacity` throws for a capacity above `FixedArray::kMaxLength` |
| `memmove` in `addArguments` | `MoveElements(isolate, add_size, 0, length, mode)` when the backing store is large enough |
| `copyArguments` | `CopyArguments`, with `ub` for a copy-on-write store, too few slots, or a non-number into a double store |
| `Result.slow` | `Slow` and `GenericArrayUnshift` |
| `specUnshift` | the arguments followed by the old elements |

## Theorems

`unshift_ne_ub`. For every well-formed array, every map and every argument
list, the builtin has no undefined behavior.

`unshift_ne_abort`. For every well-formed array whose backing store length is
at most `c.maxLen`, when `c.maxLen ≤ c.smiMax`, the builtin does not abort.

`unshift_done`. For every well-formed array with holes past its length, when
the builtin returns `a'` and `r`, `a'` is well formed, satisfies
`JSArr.SlackHoles` and is not copy-on-write, its length and `r` are
`a.length + xs.length`, and its elements are `specUnshift a.elems xs`.

`unshift_throws`. When the builtin throws, the writable copy has fewer slots
than `a.length + xs.length` and `c.maxLen < a.length + xs.length + 16`.

`unshift_handles`. Under the hypotheses of `unshift_ne_abort`, for a fast array
whose map is extensible with a writable length and with
`a.length + xs.length + 16 ≤ c.maxLen`, the builtin returns.

`matchKind_spec`. For a well-formed array of a fast kind, `matchKind` has no
undefined behavior, and a result keeps the backing store and the length and
satisfies the `KindFits` of `InPlace`: its kind allows every value the old kind
allows and every argument, and every argument is a number when the kind is a
double kind. This
is what makes the insertion safe. `Examples.lean` checks that `addArguments`
without the transition is undefined behavior when it stores `undefined` into a
`PACKED_DOUBLE_ELEMENTS` array, the capacity cap of `newElementsCapacity`, and
the RangeError for a capacity above `c.maxLen`.

## Assumptions

The array satisfies `JSArr.WF`, and `unshift_done` also requires
`JSArr.SlackHoles`. `unshift_ne_abort` and `unshift_handles` require a backing
store length of at most `c.maxLen` and `c.maxLen ≤ c.smiMax`. Both hold in V8:
`c.maxLen` stands for `kMaxFixedArrayCapacity` in
`src/objects/fixed-array-base.h`, 128 Mi slots, which bounds every backing
store, and `c.smiMax` for the Smi maximum, `2^30 - 1` with the 31-bit Smis of
`include/v8-internal.h`.

## Not modeled

`ToObject`, `GenericArrayUnshift`, the `kMaxSafeInteger` check of the generic
path, write barriers and the float64 representation of doubles are outside the
model. `MapInfo` stands for the map bits the Torque checks read.
