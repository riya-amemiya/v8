# Lean 4 model and safety proofs for `Array.prototype.some`

This directory models `FastArraySome` in `src/builtins/array-some.tq`, the fast
path of `ArraySome`, and proves that it never fails a bounds check or a backing
store cast, that its result is the result of the specification loop, and that
a bailout hands `ArraySomeLoopContinuation` a state from which the
specification loop gives the same result. The loop is the witness loop of
`ArrayWitness`, which this library imports.

## Files

| File | Contents |
| --- | --- |
| `ArraySome/Model.lean` | The loop body, the fast path and the specification loop |
| `ArraySome/Safety.lean` | The simulation and the three theorems |
| `ArraySome/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-some.tq`

| Lean | Torque |
| --- | --- |
| `Callback` | the call of `callbackfn` with `value`, `k` and `fastOW.Get()`, followed by `ToBoolean(result)` |
| `body` | one iteration after `LoadElementNoHole`: `continue` on a hole, `return True` when the result is true |
| `fastSome` | `FastArraySome` |
| `cfg.smiMax < a.length` | `Cast<Smi>(len) otherwise goto Bailout(k)` |
| `a.fast = false` | `Cast<FastJSArray>(o) otherwise goto Bailout(k)` |
| `fun _ => .done false` | `return False` after the loop |
| `Res.bailout` | `Bailout(k)` and the call of `ArraySomeLoopContinuation` from `k` |
| `specBody`, `specSome` | `ArraySomeLoopContinuation` from 0 |

`fastSome` loops to the array's own length, which is what `GetLengthProperty`
returns for a `JSArray`.

## Theorems

`fastSome_safe`. For every well-formed array and every callback satisfying
`CallbackOk a.kind`, the fast path never ends in `fatal` or `ub`.

`fastSome_done`. Under the same hypotheses, when the fast path returns `r`,
`r = specSome cb a`.

`fastSome_bailout`. Under the same hypotheses, when the fast path bails out
with indices `ks` and state `s`, there is `k ≤ a.length` with
`ks = List.range' k (a.length - k)`, the specification loop reaches `ks` and
`s.arr` from the start, and the specification loop run on `ks` from `s.arr`
gives `specSome cb a`.

`Examples.lean` checks that the fast path and the specification loop agree
after a callback that grows the array, and that a callback changing the kind
causes a bailout.

## Assumptions

The array satisfies `JSArr.WF`, and the callback satisfies `CallbackOk a.kind`
from `ArrayWitness`: it leaves a well-formed array whose kind is unchanged
whenever it reports the map unchanged.

## Not modeled

`ToObject`, `GetLengthProperty`, the callable check, `thisArg`, exceptions from
the callback and the deopt continuations are outside the model.
`ArraySomeLoopContinuation` is represented by the specification loop.
