# Lean 4 model and safety proofs for `Array.prototype.slice`

This directory models `ArrayPrototypeSlice` in `src/builtins/array-slice.tq`
from step 3 on, its clone case `CloneFastJSArray`, and `HandleFastSlice` with
its array, simple arguments and aliased sloppy arguments cases, and proves that
none of them has undefined behavior or fails a bounds check, and that each
returns the specified slice. The result type and `ExtractFastJSArray` come from
`ArrayCopyCommon`, and the clone from the `CloneFastJSArray` model of
`ArrayBuild`, both of which this library imports.

## Files

| File | Contents |
| --- | --- |
| `ArraySlice/Model.lean` | Receivers, the three fast cases, the clone case, the index computation and the specifications |
| `ArraySlice/Safety.lean` | Absence of undefined behavior and bounds check failures, agreement with the specifications |
| `ArraySlice/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-slice.tq`

| Lean | Torque |
| --- | --- |
| `Config.lim` | the `ArrayCopyCommon` limits of `ExtractFastJSArray` |
| `Config.smiMax` | `Cast<Smi>(startNumber)` and `Cast<Smi>(countNumber)` in `HandleFastSlice` |
| `Config.maxFolded` | the size limit of `AllocateJSArrayFolded`, which goes to `Bailout` above it |
| `Recv.array`, `a.forCopy` | an array receiver and the `FastJSArrayForCopy` case of the typeswitch |
| `Recv.strictArgs`, `Recv.sloppyArgs` | `JSStrictArgumentsObject` and a `JSSloppyArgumentsObject` with `IsSloppyArgumentsMap`, with `none` when `Cast<FixedArray>(args.elements)` fails |
| `Recv.aliasedArgs`, `Aliased` | a `JSSloppyArgumentsObject` with `IsFastAliasedArgumentsMap`, whose `SloppyArgumentsElements` give the parameter map, `argumentsContext` and the unmapped `FixedArray` |
| `simpleArgs` | `HandleSimpleArgumentsSlice` |
| `mappedValue`, `aliasedLoop` | the loop over the context-mapped parameters, which reads `sloppyElements.objects[current]` and then `argumentsContext.elements` or `unmappedElements.objects[current]` |
| `aliasedArgs` | `HandleFastAliasedSloppyArgumentsSlice`, with the final `CopyElements` of the unmapped rest |
| `holeyArray` | the `HOLEY_ELEMENTS` result of `AllocateJSArrayFolded` |
| `handleFastSlice` | `HandleFastSlice` |
| `a.length < start + count` | `if (SmiAbove(start + count, a.length)) goto Bailout` |
| `clamp`, `sliceIndices` | steps 4 to 7, computing `k`, `final` and `count` |
| `StartArg` | `start == Undefined`, `TaggedEqual(start, SmiConstant(0))` and any other start |
| `slice` | `ArrayPrototypeSlice` from step 3 to the call of `HandleFastSlice` |
| `ArrayBuild.cloneFastJSArray false` | `CloneFastJSArray(context, a)` |
| `Out.slow` | `Bailout`, `Slow` and the generic loop |
| `Out.fatal` | a failed bounds check or an abort |
| `argsSpec`, `aliasedSpec` | the specified slice of an arguments object, through its parameter map for the aliased case |

`slice` takes the length `len` read before `ToInteger_Inline`, the receiver
tested by the clone case and the object passed to `HandleFastSlice` as
separate inputs, and `slice_safe` holds for every combination.

## Theorems

`slice_safe`. For every receiver and object satisfying `RecvOK`, every length,
start and end, `slice` never ends in `ub` or `fatal`.

`handleFastSlice_safe`. For every object satisfying `RecvOK`, `HandleFastSlice`
never ends in `ub` or `fatal`.

`array_spec`. For every well-formed array whose backing store length is at
most `lim.maxLen`, `HandleFastSlice` either goes to the slow path or, with
`start + count ≤ a.length`, returns a new array of the source kind whose
elements are `specSlice a.elems start count`. `newArray_slice_wf` shows that
this array is well formed for a `FastJSArrayForCopy` source.

`simpleArgs_spec`. For every simple arguments object, the slice either goes to
the slow path or, when the elements are a `FixedArray` of length at least
`start + count`, returns a `HOLEY_ELEMENTS` array with elements
`specSlice src start count`.

`aliasedArgs_spec`. For every aliased arguments object satisfying `Aliased.OK`,
the slice either goes to the slow path or, when the unmapped elements have
length at least `start + count`, returns a `HOLEY_ELEMENTS` array with elements
`aliasedSpec s src start count`.

`clone_path`. For every well-formed `FastJSArrayForCopy` with holes past its
length, a successful clone is well formed, has the length of the source, and
its elements are `specSlice a.elems 0 a.length`.

`Examples.lean` checks that an aliased arguments object whose parameter map
points past the context fails a bounds check, which is why `Aliased.OK` is
needed, and that `extractFast` on an array whose length exceeds its empty
backing store is undefined behavior, which `JSArr.WF` rules out. It also checks
that the clone of a copy-on-write array stays copy-on-write.

## Assumptions

`RecvOK` requires `JSArr.WF` and a backing store length of at most
`lim.maxLen` for an array, and `Aliased.OK` for an aliased arguments object:
every mapped parameter refers to a slot inside the context. `clone_path`
also requires `JSArr.SlackHoles`.

## Not modeled

`ToObject`, `GetLengthProperty`, `ToInteger_Inline`, `ArraySpeciesCreate`, the
generic loop and the allocation of the result arrays are outside the model.
