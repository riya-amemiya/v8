# Lean 4 model and safety proofs for the `Array.prototype.copyWithin` fast path

This directory contains a machine-checked model of `TryFastArrayCopyWithin` in
`src/builtins/array-copywithin.tq`, together with the index computation of
`ArrayPrototypeCopyWithin` that feeds it, and proofs of its safety properties.
The model builds on the shared library in `formal/Torque`, and
`formal/README.md` describes how to check the proofs.

## Files

| File | Contents |
| --- | --- |
| `ArrayCopyWithin/Model.lean` | Index computation, the fast path and the specification loop |
| `ArrayCopyWithin/Safety.lean` | Equivalence of the specification loop and `memmove`, absence of undefined behavior, result well-formedness |
| `ArrayCopyWithin/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-copywithin.tq`

| Lean | Torque |
| --- | --- |
| `clampIndex` | `ConvertAndClampRelativeIndex` and `ConvertRelativeIndex` |
| `targetIndex`, `startIndex`, `finalIndex`, `count` | steps 3 to 9 of `ArrayPrototypeCopyWithin` |
| `tryFast` | `TryFastArrayCopyWithin` |
| `fastPath` | `TryFastArrayCopyWithin` applied to the clamped indices |
| `moveChecked` | `DoMoveElements`, whose `MoveElements` checks its bounds only with `CSA_DCHECK` |
| `Torque.ensureWritable` | `EnsureWriteableFastElements` |
| `Torque.SmiRepr.add`, `Torque.SmiRepr.above` | `to + count`, `from + count` and `SmiAbove` |
| `copyFwd`, `copyBwd`, `specCopy` | steps 10 to 12 on an array whose holes are absent elements |
| `Result.ub` | a `memmove` outside the backing store, or a write into a copy-on-write backing store |

`tryFast` takes the array `a` as it is after the `ToInteger` calls and the
length `len` read before them as independent inputs, so the theorems cover any
change user code makes to the array in between.

## Theorems

`fastPath_ne_ub`. For every well-formed array, every length and every
argument, the fast path never moves elements outside the backing store and
never writes into a copy-on-write backing store.

`fastPath_ok`. When the fast path handles the call, the array keeps its
elements kind and length, stays well-formed, and its elements equal the result
of the specification loop on the original elements.

`specCopy_eq`. Within the bounds the fast path checks, the specification loop,
with its direction switch for overlapping ranges, equals one `memmove`. This is
the claim of the comment above `TryFastArrayCopyWithin`.

The proof of `fastPath_ne_ub` uses three facts. `ConvertAndClampRelativeIndex`
returns non-negative indices, so a negative target never reaches
`TryFastArrayCopyWithin`. `SmiAbove` compares tagged words without sign, so a sum
`to + count` that leaves the Smi range is still rejected. A fast array's length
is at most its backing store length. `Examples.lean` checks that `tryFast` with
a negative target reaches `Result.ub`, and that `SmiGreaterThan` would accept an
overflowed sum that `SmiAbove` rejects.

## Assumptions

The array satisfies `JSArr.WF` from `formal/Torque`, and its length is at most
`SmiRepr.max`, because the length of a `FastJSArray` is a Smi. The Smi layout
satisfies `shift < width`, which holds for `SmiRepr.compressed` and
`SmiRepr.full`.

`CastFastJSArray` in `src/builtins/cast.tq` already requires the initial array
prototype and an intact `NoElementsProtector`, so the model folds the same
checks in the holey branch into `JSArr.fast`. With those two conditions a hole
is an absent element, which is how `specCopy` treats it.

Write barriers in `MoveElements` and the float64 payload of doubles are not
modeled.

## Not covered

The generic loop that runs when the fast path bails out, `ToObject`,
`GetLengthProperty` and `ToInteger`, and the faithfulness of the hand
translation from Torque to Lean are outside the proofs.
