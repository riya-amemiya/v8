# Lean 4 model and safety proofs for `Array.prototype.findLastIndex`

This directory models `FastArrayFindLastIndex` in
`src/builtins/array-findlastindex.tq`, the fast path of
`ArrayPrototypeFindLastIndex`, and proves that it never fails a bounds check or
a backing store cast, that its result is the result of the specification loop,
and that a bailout hands `ArrayFindLastIndexLoopContinuation` a state from
which the specification loop gives the same result. The loop is the witness
loop of `ArrayWitness`, which this library imports, run over the indices from
`len - 1` down to 0.

## Files

| File | Contents |
| --- | --- |
| `ArrayFindLastIndex/Model.lean` | The loop body, the fast path and the specification loop |
| `ArrayFindLastIndex/Safety.lean` | The simulation and the three theorems |
| `ArrayFindLastIndex/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-findlastindex.tq`

| Lean | Torque |
| --- | --- |
| `Callback` | the call of `predicate` with `value`, `k` and `fastOW.Get()`, followed by `ToBoolean(testResult)`, where `none` is `undefined` |
| `body` | one iteration: `LoadElementOrUndefined`, the call, and `return k` when the result is true |
| `fastFindLastIndex` | `FastArrayFindLastIndex` |
| `cfg.smiMax < a.length` | `Cast<Smi>(len) otherwise goto Bailout(len - 1)` |
| `a.fast = false` | `Cast<FastJSArray>(o) otherwise goto Bailout(k)` |
| `backward a.length` | the loop from `smiLen - 1` while `k >= 0` |
| `fun _ => .done (-1)` | the return of -1 after the loop |
| `Res.bailout` | `Bailout(k)` and the call of `ArrayFindLastIndexLoopContinuation` from `k` |
| `specBody`, `specFindLastIndex` | `ArrayFindLastIndexLoopContinuation` from `len - 1`, which calls the predicate on holes too |

`fastFindLastIndex` loops from the array's own length, which is what
`GetLengthProperty` returns for a `JSArray`.

## Theorems

`fastFindLastIndex_safe`. For every well-formed array and every callback
satisfying `CallbackOk a.kind`, the fast path never ends in `fatal` or `ub`.

`fastFindLastIndex_done`. Under the same hypotheses, when the fast path returns
`r`, `r = specFindLastIndex cb a`.

`fastFindLastIndex_bailout`. Under the same hypotheses, when the fast path
bails out with indices `ks` and state `s`, there is `m ≤ a.length` with
`ks = backward m`, the specification loop reaches `ks` and `s.arr` from the
start, and the specification loop run on `ks` from `s.arr` gives
`specFindLastIndex cb a`.

`Examples.lean` checks that a hole reaches the predicate as `undefined`, and a
bailout after a callback that invalidates the protector.

## Assumptions

The array satisfies `JSArr.WF`, and the callback satisfies `CallbackOk a.kind`
from `ArrayWitness`: it leaves a well-formed array whose kind is unchanged
whenever it reports the map unchanged.

## Not modeled

`ToObject`, `GetLengthProperty`, the callable check, `thisArg` and exceptions
from the callback are outside the model. `ArrayFindLastIndexLoopContinuation`
is represented by the specification loop.
