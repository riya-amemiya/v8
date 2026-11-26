# Lean 4 model and proofs for `Array.prototype.at`

This directory models the index computation of `ArrayPrototypeAt` in
`src/builtins/array-at.tq`. The builtin reads the element with `GetProperty`,
so it has no direct memory access; the proof covers the float64 arithmetic of
`ConvertRelativeIndex`.

## Files

| File | Contents |
| --- | --- |
| `ArrayAt/Model.lean` | `ConvertRelativeIndex` and the specification steps |
| `ArrayAt/Safety.lean` | Agreement with the specification |
| `ArrayAt/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-at.tq`

| Lean | Torque |
| --- | --- |
| `convertRelativeIndex` | `ConvertRelativeIndex` applied to `ToInteger_Inline(index)` and `GetLengthProperty(o)` |
| `ExtInt` | the integer or infinite Number that `ToInteger_Inline` returns |
| `fadd` | the float64 addition `length + index` |
| `specAt` | steps 3 to 7 of the specification |

## Theorems

`convertRelativeIndex_spec`. For every length up to `2^53 - 1` and every
integer or infinite index, and for every addition that is exact on integers of
magnitude at most `2^53` and keeps the sign of a negative sum, which round to
nearest float64 addition does, the computed index equals the specification's
`k`, or both report an index out of range.

`convertRelativeIndex_lt`. The index passed to `GetProperty` is below the
length.

## Not modeled

`ToObject`, `GetLengthProperty`, `ToInteger` and `GetProperty` are outside the
model.
