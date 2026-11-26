# Lean 4 model and safety proofs for `Array.of`

This directory models `ArrayOf` in `src/builtins/array-of.tq` and proves its
safety. The element stores go through `FastCreateDataProperty`, modeled in
`formal/ArrayBuild`.

## Files

| File | Contents |
| --- | --- |
| `ArrayOf/Model.lean` | The choice of the result array and the store loop |
| `ArrayOf/Safety.lean` | Absence of undefined behavior and aborts, agreement with the specification, well-formedness |
| `ArrayOf/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-of.tq`

| Lean | Torque |
| --- | --- |
| `Ctor.arrayFunction` | `c == GetArrayFunction()` |
| `Ctor.otherConstructor` | a constructor other than `%Array%`, which `Construct(c, len)` calls with arbitrary user code |
| `Ctor.notConstructor` | a non-constructor receiver, for which `ArrayCreate(len)` creates the array |
| `filledWithZero` | `NewJSArrayFilledWithZero`, which allocates `PACKED_SMI_ELEMENTS` filled with zeros, or returns `NewJSArray` for length 0 |
| `Config.maxFast` | `kMaxFastArrayLength`, above which `NewJSArrayFilledWithZero` bails out to `Construct` |
| `create` | `Construct(%Array%, len)` after that bailout, and `ArrayCreate(len)` |
| `createLoop` | the loop of `FastCreateDataProperty(a, k, items[k])` |

## Theorems

`arrayOf_spec`. For every list of arguments and every runtime fallback
satisfying `RuntimeOK`, when the receiver is `%Array%` or not a constructor, the
result is a well-formed array with holes past its length whose elements are
exactly the arguments and whose length is their number.

`arrayOf_safe`. No call writes outside a backing store, into a copy-on-write
backing store, or fails a bounds check.

## Assumptions

`create` returns a well-formed array of the requested length with holes past
it, and the runtime `CreateDataProperty` satisfies `RuntimeOK`. The loop index
`k` stays below the argument count, so `items[k]` is in bounds. The final
`SetPropertyLength(a, len)` sets the length the array already has, which the
specification leaves without effect.

## Not modeled

`Construct` with a user-defined constructor, `SetPropertyLength` itself and the
argument frame are outside the model.
