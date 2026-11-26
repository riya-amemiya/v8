# Lean 4 model and safety proofs for the `Array.prototype.concat` fast paths

This directory models the two fast paths of `ArrayPrototypeConcat` in
`src/builtins/array-concat.tq` and proves their safety. Both copy one array
with `CloneFastJSArray`, modeled in `formal/ArrayBuild`. Every other call
tail-calls the C++ builtin `ArrayConcat`, which is outside the model.

## Files

| File | Contents |
| --- | --- |
| `ArrayConcat/Model.lean` | The two fast paths and the specification result |
| `ArrayConcat/Safety.lean` | Absence of undefined behavior, agreement with the specification, well-formedness |
| `ArrayConcat/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-concat.tq`

| Lean | Torque |
| --- | --- |
| `fastPath` | `ArrayPrototypeConcat` up to the tail call of `ArrayConcat` |
| `forConcat` | the `FastJSArrayForConcat` cast, which requires an intact `IsConcatSpreadable` protector and the `FastJSArrayForCopy` cast |
| `JSArr.forCopy` | the `FastJSArrayForCopy` cast, which requires an intact `ArraySpecies` protector and the `FastJSArray` cast |
| `(H p).length = 0` | `IsEmpty` |
| `Result.generic` | the tail call of the C++ builtin `ArrayConcat` |
| `specConcat` | steps 5 and 6 of the specification for spreadable arrays, which keep holes as absent elements |

## Theorems

`fastPath_ne_ub`. For every well-formed heap, receiver and argument list, the
fast paths never read past a backing store.

`fastPath_done`. When a fast path handles `a.concat()` or `[].concat(b)`, the
result is a well-formed array with holes past its length, and its elements and
length equal the specification result for the receiver alone or for the empty
receiver followed by the argument.

## Assumptions

The heap satisfies `HeapWF` and every array has holes past its length. With
the `IsConcatSpreadable` protector intact, `IsConcatSpreadable` of an array is
`true`, and with the `ArraySpecies` protector intact `ArraySpeciesCreate`
creates a plain array, so the specification result is a copy that keeps holes.

## Not modeled

The C++ builtin `ArrayConcat` and the identity of the created array are
outside the model.
