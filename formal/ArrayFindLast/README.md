# Lean 4 model and safety proofs for `Array.prototype.findLast`

This directory models `FastArrayFindLast` in `src/builtins/array-findlast.tq`,
the fast path of `ArrayPrototypeFindLast`, and proves that it never fails a
bounds check or a backing store cast, that its result is the result of the
specification loop, and that a bailout hands `ArrayFindLastLoopContinuation` a
state from which the specification loop gives the same result. The loop is the
witness loop of `ArrayWitness`, which this library imports, run over the
indices from `len - 1` down to 0.

## Files

| File | Contents |
| --- | --- |
| `ArrayFindLast/Model.lean` | The loop body, the fast path and the specification loop |
| `ArrayFindLast/Safety.lean` | The simulation and the three theorems |
| `ArrayFindLast/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-findlast.tq`

| Lean | Torque |
| --- | --- |
| `Callback` | the call of `predicate` with `value`, `k` and `fastOW.Get()`, followed by `ToBoolean(testResult)`, where `none` is `undefined` |
| `body` | one iteration: `LoadElementOrUndefined`, the call, and `return value` when the result is true |
| `fastFindLast` | `FastArrayFindLast` |
| `cfg.smiMax < a.length` | `Cast<Smi>(len) otherwise goto Bailout(len - 1)` |
| `a.fast = false` | `Cast<FastJSArray>(o) otherwise goto Bailout(k)` |
| `backward a.length` | the loop from `smiLen - 1` while `k >= 0` |
| `fun _ => .done none` | `return Undefined` after the loop |
| `Res.bailout` | `Bailout(k)` and the call of `ArrayFindLastLoopContinuation` from `k` |
| `specBody`, `specFindLast` | `ArrayFindLastLoopContinuation` from `len - 1`, which calls the predicate on holes too |

`fastFindLast` loops from the array's own length, which is what
`GetLengthProperty` returns for a `JSArray`.

## Theorems

`fastFindLast_safe`. For every well-formed array and every callback satisfying
`CallbackOk a.kind`, the fast path never ends in `fatal` or `ub`.

`fastFindLast_done`. Under the same hypotheses, when the fast path returns `r`,
`r = specFindLast cb a`.

`fastFindLast_bailout`. Under the same hypotheses, when the fast path bails out
with indices `ks` and state `s`, there is `m ≤ a.length` with `ks = backward m`,
the specification loop reaches `ks` and `s.arr` from the start, and the
specification loop run on `ks` from `s.arr` gives `specFindLast cb a`.

`Examples.lean` checks a bailout after a callback that shrinks the array, where
the remaining indices still count down to 0, a bailout before the loop for an
array that is not fast, and an empty array.

## Assumptions

The array satisfies `JSArr.WF`, and the callback satisfies `CallbackOk a.kind`
from `ArrayWitness`: it leaves a well-formed array whose kind is unchanged
whenever it reports the map unchanged.

## Not modeled

`ToObject`, `GetLengthProperty`, the callable check, `thisArg` and exceptions
from the callback are outside the model. `ArrayFindLastLoopContinuation` is
represented by the specification loop.
