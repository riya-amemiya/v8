# Lean 4 model and safety proofs for `Array.prototype.reduceRight`

This directory models `FastArrayReduceRight` in
`src/builtins/array-reduce-right.tq`, the fast path of `ArrayReduceRight`, and
proves that it never fails a bounds check or a backing store cast, that its
result is the result of the specification, and that a bailout hands
`ArrayReduceRightLoopContinuation` an index and an accumulator from which the
specification loop gives the same result. The loop is the witness loop of
`ArrayWitness`, which this library imports, on a `FastJSArrayForReadWitness`
and over the indices from `len - 1` down to 0.

## Files

| File | Contents |
| --- | --- |
| `ArrayReduceRight/Model.lean` | The loop body, the fast path, the specification loop and the closed form of the specification |
| `ArrayReduceRight/Safety.lean` | The simulation and the three theorems |
| `ArrayReduceRight/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-reduce-right.tq`

| Lean | Torque |
| --- | --- |
| `Option Val` accumulator | `accumulator`, with `none` for `TheHole` |
| `Callback` | the call of `callbackfn` with `accumulatorNotHole`, `value`, `k` and `fastOW.Get()` |
| `body` | one iteration after `LoadElementNoHole`: `continue` on a hole, `accumulator = value` while the accumulator is `TheHole`, otherwise the call |
| `fastReduceRight` | `FastArrayReduceRight` |
| `cfg.smiMax < a.length` | `Cast<Smi>(len) otherwise goto Bailout(len - 1, accumulator)` |
| `a.forRead = false` | `Cast<FastJSArrayForRead>(o) otherwise goto Bailout(len - 1, accumulator)` |
| `backward a.length` | the loop from `smiLen - 1` while `k >= 0` |
| `fun s => .done s.acc` | the final `typeswitch (accumulator)`, where `none` stands for `ThrowTypeError(MessageTemplate::kReduceNoInitial)` |
| `Res.bailout` | `Bailout(k, accumulator)` and the call of `ArrayReduceRightLoopContinuation` |
| `specBody` | the loop of `ArrayReduceRightLoopContinuation` |
| `accumulate`, `search`, `specReduceRight` | the specification with and without an initial value, which searches for the last present element when there is none |

`fastReduceRight` loops from the array's own length, which is what
`GetLengthProperty` returns for a `JSArray`.

## Theorems

`fastReduceRight_safe`. For every well-formed array, every initial accumulator
and every callback satisfying `CallbackOk a.kind`, the fast path never ends in
`fatal` or `ub`.

`fastReduceRight_done`. Under the same hypotheses, when the fast path returns
`r`, `r = specReduceRight cb a init`.

`fastReduceRight_bailout`. Under the same hypotheses, when the fast path bails
out with indices `ks` and state `s`, there is `m ≤ a.length` with
`ks = backward m`, the specification loop reaches `ks`, the accumulator `s.acc`
and `s.arr` from the start, and the specification loop run on `ks` from `s.acc`
and `s.arr` gives `specReduceRight cb a init`.

`spec_eq` connects the specification loop to `specReduceRight`.

`Examples.lean` checks a trailing hole, an empty array without an initial
value, and a bailout after a callback that shrinks the array, which carries the
accumulator to the continuation.

## Assumptions

The array satisfies `JSArr.WF`, and the callback satisfies `CallbackOk a.kind`
from `ArrayWitness`: it leaves a well-formed array whose kind is unchanged
whenever it reports the map unchanged.

## Not modeled

`ToObject`, `GetLengthProperty`, the callable check, the TypeError itself,
exceptions from the callback and the deopt continuations are outside the model.
`ArrayReduceRightLoopContinuation` is represented by the specification loop.
