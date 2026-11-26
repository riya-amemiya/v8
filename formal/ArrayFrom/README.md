# Lean 4 model and safety proofs for `Array.from`

This directory models `ArrayFrom` in `src/builtins/array-from.tq`, the fast
array and string branches of `FastIterableToList` it calls, and proves their
safety. The element stores go through `FastCreateDataProperty` and the fast
array copy through `CloneFastJSArray`, both modeled in `formal/ArrayBuild`. The
Map and Set branches of `FastIterableToList` are covered by
`formal/ArrayFromCollections`.

## Files

| File | Contents |
| --- | --- |
| `ArrayFrom/Model.lean` | The fast array copy, `StringToList`, the iterator loop and the array-like loop |
| `ArrayFrom/Safety.lean` | Absence of undefined behavior and aborts, agreement with the specification, well-formedness |
| `ArrayFrom/Examples.lean` | Executable `#guard` checks |

## Correspondence with the V8 sources

| Lean | V8 |
| --- | --- |
| `fromFastArray` | the `FastJSArrayForReadWithNoCustomIteration` branch of `FastIterableToList` in `src/builtins/builtins-iterator-gen.cc`, which calls `CloneFastJSArrayFillingHoles` |
| `iterated` | what `%ArrayIteratorPrototype%.next` yields for such an array: each element, with holes read as `undefined` |
| `stringToList`, `stringLoop` | `StringToList` in `src/builtins/builtins-string.tq`, which `FastIterableToList` calls for a string primitive of at most `kMaxFastArrayLength` code units |
| `isLead`, `isTrail`, `codePoints` | `LoadSurrogatePairAt` with `UnicodeEncoding::UTF16` and the specification's `CodePointAt`, which the string iterator uses |
| `writeAt` | `elements[arrayLength] = value`, a bounds-checked Torque slice store |
| `fromIterable` | the iterator loop of `ArrayFrom`, from `Construct(c)` or `ArrayCreate(0)` to `SetPropertyLength(a, k)` |
| `fromArrayLike` | the array-like loop of `ArrayFrom` |
| `allocated` | `AllocateJSArray(PACKED_SMI_ELEMENTS, map, len, 0)`, whose backing store `AllocateJSArray` fills with holes |
| `create` | `Construct(c, len)` with `c` equal to `%Array%` for a length above `kMaxFastArrayLength`, and `ArrayCreate(len)` |

## Theorems

`fromFastArray_spec`. For every well-formed fast array, the copy never reads
past the backing store, and its elements equal the values that iterating the
array yields.

`stringToList_spec`. For every string, every store of `StringToList` is in
bounds, the result holds one string for each code point that the string
iterator yields, in order, a lone surrogate counting as one code point, and the
array is a well-formed `PACKED_ELEMENTS` array whose unused capacity holds
holes. The proof rests on the number of code points never exceeding the number
of code units, which `codePoints_length_le` shows.

`fromIterable_spec` and `fromArrayLike_spec`. For every sequence of values that
the iterator and `mapfn`, or `Get` and `mapfn`, produce, and every runtime
fallback satisfying `RuntimeOK`, the result is a well-formed array whose
elements are exactly those values and whose length is their number. These cover
every receiver except a user-defined constructor.

## Assumptions

The source array is well-formed with holes past its length. The protector
checks of `IsFastJSArrayForReadWithNoCustomIteration` and the string check
ensure that iteration has no observable side effects, so the iterated values
are the elements with holes read as `undefined`. `StringToList` allocates the
array with length `stringLength` and kind `PACKED_ELEMENTS` before the loop and
lowers the length at the end. Until then the array is not visible to
JavaScript, and the allocation in `StringFromSingleUTF16EncodedCodePoint` does
not inspect its contents. The constructor result satisfies the same conditions
as in `formal/ArrayOf`.

## Not modeled

The iterator protocol, `IteratorClose` on an abrupt completion, `mapfn`, the
interceptor branch of `FastIterableToList`, user-defined constructors and
`SetPropertyLength` are outside the model. The `k < 2^53 - 1` check of the
specification is a `dcheck` in `ArrayFrom`, as its comment explains.
