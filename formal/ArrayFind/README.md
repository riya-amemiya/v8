# Lean 4 model and safety proofs for `Array.prototype.find`

This directory models `FastArrayFind` in `src/builtins/array-find.tq`, the fast
path of `ArrayPrototypeFind`, and proves that it never fails a bounds check or
a backing store cast, that its result is the result of the specification loop,
and that a bailout hands `ArrayFindLoopContinuation` a state from which the
specification loop gives the same result. The loop is the witness loop of
`ArrayWitness`, which this library imports.

## Files

| File | Contents |
| --- | --- |
| `ArrayFind/Model.lean` | The loop body, the fast path and the specification loop |
| `ArrayFind/Safety.lean` | The simulation and the three theorems |
| `ArrayFind/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-find.tq`

| Lean | Torque |
| --- | --- |
| `Callback` | the call of `callbackfn` with `value`, `k` and `fastOW.Get()`, followed by `ToBoolean(testResult)`, where `none` is `undefined` |
| `body` | one iteration: `LoadElementOrUndefined`, the call, and `return value` when the result is true |
| `fastFind` | `FastArrayFind` |
| `cfg.smiMax < a.length` | `Cast<Smi>(len) otherwise goto Bailout(k)` |
| `a.fast = false` | `Cast<FastJSArray>(o) otherwise goto Bailout(k)` |
| `fun _ => .done none` | `return Undefined` after the loop |
| `Res.bailout` | `Bailout(k)` and the call of `ArrayFindLoopContinuation` from `k` |
| `specBody`, `specFind` | `ArrayFindLoopContinuation` from 0, which calls the predicate on holes too |

`fastFind` loops to the array's own length, which is what `GetLengthProperty`
returns for a `JSArray`.

## Theorems

`fastFind_safe`. For every well-formed array and every callback satisfying
`CallbackOk a.kind`, the fast path never ends in `fatal` or `ub`.

`fastFind_done`. Under the same hypotheses, when the fast path returns `r`,
`r = specFind cb a`.

`fastFind_bailout`. Under the same hypotheses, when the fast path bails out
with indices `ks` and state `s`, there is `k ≤ a.length` with
`ks = List.range' k (a.length - k)`, the specification loop reaches `ks` and
`s.arr` from the start, and the specification loop run on `ks` from `s.arr`
gives `specFind cb a`.

`Examples.lean` checks that a hole reaches the predicate as `undefined`, and a
bailout after a callback that shrinks the array.

## Assumptions

The array satisfies `JSArr.WF`, and the callback satisfies `CallbackOk a.kind`
from `ArrayWitness`: it leaves a well-formed array whose kind is unchanged
whenever it reports the map unchanged.

## Not modeled

`ToObject`, `GetLengthProperty`, the callable check, `thisArg`, exceptions from
the callback and the deopt continuations are outside the model.
`ArrayFindLoopContinuation` is represented by the specification loop.
