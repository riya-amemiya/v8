# Lean 4 model and safety proofs for `Array.prototype.findIndex`

This directory models `FastArrayFindIndex` in `src/builtins/array-findindex.tq`,
the fast path of `ArrayPrototypeFindIndex`, and proves that it never fails a
bounds check or a backing store cast, that its result is the result of the
specification loop, and that a bailout hands `ArrayFindIndexLoopContinuation`
a state from which the specification loop gives the same result. The loop is
the witness loop of `ArrayWitness`, which this library imports.

## Files

| File | Contents |
| --- | --- |
| `ArrayFindIndex/Model.lean` | The loop body, the fast path and the specification loop |
| `ArrayFindIndex/Safety.lean` | The simulation and the three theorems |
| `ArrayFindIndex/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-findindex.tq`

| Lean | Torque |
| --- | --- |
| `Callback` | the call of `callbackfn` with `value`, `k` and `fastOW.Get()`, followed by `ToBoolean(testResult)`, where `none` is `undefined` |
| `body` | one iteration: `LoadElementOrUndefined`, the call, and `return k` when the result is true |
| `fastFindIndex` | `FastArrayFindIndex` |
| `cfg.smiMax < a.length` | `Cast<Smi>(len) otherwise goto Bailout(k)` |
| `a.fast = false` | `Cast<FastJSArray>(o) otherwise goto Bailout(k)` |
| `fun _ => .done (-1)` | the return of -1 after the loop |
| `Res.bailout` | `Bailout(k)` and the call of `ArrayFindIndexLoopContinuation` from `k` |
| `specBody`, `specFindIndex` | `ArrayFindIndexLoopContinuation` from 0, which calls the predicate on holes too |

`fastFindIndex` loops to the array's own length, which is what
`GetLengthProperty` returns for a `JSArray`.

## Theorems

`fastFindIndex_safe`. For every well-formed array and every callback
satisfying `CallbackOk a.kind`, the fast path never ends in `fatal` or `ub`.

`fastFindIndex_done`. Under the same hypotheses, when the fast path returns
`r`, `r = specFindIndex cb a`.

`fastFindIndex_bailout`. Under the same hypotheses, when the fast path bails
out with indices `ks` and state `s`, there is `k ≤ a.length` with
`ks = List.range' k (a.length - k)`, the specification loop reaches `ks` and
`s.arr` from the start, and the specification loop run on `ks` from `s.arr`
gives `specFindIndex cb a`.

`Examples.lean` checks that a hole reaches the predicate as `undefined`, and a
bailout after a callback that changes the kind.

## Assumptions

The array satisfies `JSArr.WF`, and the callback satisfies `CallbackOk a.kind`
from `ArrayWitness`: it leaves a well-formed array whose kind is unchanged
whenever it reports the map unchanged.

## Not modeled

`ToObject`, `GetLengthProperty`, the callable check, `thisArg`, exceptions from
the callback and the deopt continuations are outside the model.
`ArrayFindIndexLoopContinuation` is represented by the specification loop.
