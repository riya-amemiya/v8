# Lean 4 model and safety proofs for `Array.prototype.every`

This directory models `FastArrayEvery` in `src/builtins/array-every.tq`, the
fast path of `ArrayEvery`, and proves that it never fails a bounds check or a
backing store cast, that its result is the result of the specification loop,
and that a bailout hands `ArrayEveryLoopContinuation` a state from which the
specification loop gives the same result. The loop is the witness loop of
`ArrayWitness`, which this library imports.

## Files

| File | Contents |
| --- | --- |
| `ArrayEvery/Model.lean` | The loop body, the fast path and the specification loop |
| `ArrayEvery/Safety.lean` | The simulation and the three theorems |
| `ArrayEvery/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-every.tq`

| Lean | Torque |
| --- | --- |
| `Callback` | the call of `callbackfn` with `value`, `k` and `fastOW.Get()`, followed by `ToBoolean(result)` |
| `body` | one iteration after `LoadElementNoHole`: `continue` on a hole, `return False` when the result is false |
| `fastEvery` | `FastArrayEvery` |
| `cfg.smiMax < a.length` | `Cast<Smi>(len) otherwise goto Bailout(k)` |
| `a.fast = false` | `Cast<FastJSArray>(o) otherwise goto Bailout(k)` |
| `fun _ => .done true` | `return True` after the loop |
| `Res.bailout` | `Bailout(k)` and the call of `ArrayEveryLoopContinuation` from `k` |
| `specBody`, `specEvery` | `ArrayEveryLoopContinuation` from 0 |

`fastEvery` loops to the array's own length, which is what `GetLengthProperty`
returns for a `JSArray`.

## Theorems

`fastEvery_safe`. For every well-formed array and every callback satisfying
`CallbackOk a.kind`, the fast path never ends in `fatal` or `ub`.

`fastEvery_done`. Under the same hypotheses, when the fast path returns `r`,
`r = specEvery cb a`.

`fastEvery_bailout`. Under the same hypotheses, when the fast path bails out
with indices `ks` and state `s`, there is `k ≤ a.length` with
`ks = List.range' k (a.length - k)`, the specification loop reaches `ks` and
`s.arr` from the start, and the specification loop run on `ks` from `s.arr`
gives `specEvery cb a`.

`Examples.lean` checks bailouts after a callback that shrinks the array,
changes its kind or invalidates the protector, and before the loop for a
length above `smiMax` and for an array that is not fast.

## Assumptions

The array satisfies `JSArr.WF`, and the callback satisfies `CallbackOk a.kind`
from `ArrayWitness`: it leaves a well-formed array whose kind is unchanged
whenever it reports the map unchanged.

## Not modeled

`ToObject`, `GetLengthProperty`, the callable check, `thisArg`, exceptions from
the callback and the deopt continuations are outside the model.
`ArrayEveryLoopContinuation` is represented by the specification loop.
