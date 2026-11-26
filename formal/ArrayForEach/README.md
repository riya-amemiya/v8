# Lean 4 model and safety proofs for `Array.prototype.forEach`

This directory models `FastArrayForEach` in `src/builtins/array-foreach.tq`,
the fast path of `ArrayForEach`, and proves that it never fails a bounds check
or a backing store cast, that it leaves the array the specification loop
leaves, and that a bailout hands `ArrayForEachLoopContinuation` a state from
which the specification loop leaves the same array. The loop is the witness
loop of `ArrayWitness`, which this library imports.

## Files

| File | Contents |
| --- | --- |
| `ArrayForEach/Model.lean` | The loop body, the fast path and the specification loop |
| `ArrayForEach/Safety.lean` | The simulation and the three theorems |
| `ArrayForEach/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-foreach.tq`

| Lean | Torque |
| --- | --- |
| `Callback` | the call of `callbackfn` with `value`, `k` and `fastOW.Get()`, whose result is ignored |
| `body` | one iteration after `LoadElementNoHole`: `continue` on a hole, otherwise the call |
| `fastForEach` | `FastArrayForEach` |
| `cfg.smiMax < a.length` | `Cast<Smi>(len) otherwise goto Bailout(k)` |
| `a.fast = false` | `Cast<FastJSArray>(o) otherwise goto Bailout(k)` |
| `fun s => .done s.arr` | `return Undefined` after the loop, with the array left by the calls as the observable result |
| `Res.bailout` | `Bailout(k)` and the call of `ArrayForEachLoopContinuation` from `k` |
| `specBody`, `specForEach` | `ArrayForEachLoopContinuation` from 0 |

`fastForEach` loops to the array's own length, which is what
`GetLengthProperty` returns for a `JSArray`.

## Theorems

`fastForEach_safe`. For every well-formed array and every callback satisfying
`CallbackOk a.kind`, the fast path never ends in `fatal` or `ub`.

`fastForEach_done`. Under the same hypotheses, when the fast path finishes with
array `r`, `r = specForEach cb a`.

`fastForEach_bailout`. Under the same hypotheses, when the fast path bails out
with indices `ks` and state `s`, there is `k ≤ a.length` with
`ks = List.range' k (a.length - k)`, the specification loop reaches `ks` and
`s.arr` from the start, and the specification loop run on `ks` from `s.arr`
gives `specForEach cb a`.

`Examples.lean` checks the array left by a callback that writes into it, with
and without holes, and bailouts after a callback that clears the array or makes
it holey.

## Assumptions

The array satisfies `JSArr.WF`, and the callback satisfies `CallbackOk a.kind`
from `ArrayWitness`: it leaves a well-formed array whose kind is unchanged
whenever it reports the map unchanged.

## Not modeled

`ToObject`, `GetLengthProperty`, the callable check, `thisArg`, exceptions from
the callback and the deopt continuations are outside the model.
`ArrayForEachLoopContinuation` is represented by the specification loop.
