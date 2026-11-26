# Lean 4 model and safety proofs for `Array.prototype.reduce`

This directory models `FastArrayReduce` in `src/builtins/array-reduce.tq`, the
fast path of `ArrayReduce`, and proves that it never fails a bounds check or a
backing store cast, that its result is the result of the specification, and
that a bailout hands `ArrayReduceLoopContinuation` an index and an accumulator
from which the specification loop gives the same result. The loop is the
witness loop of `ArrayWitness`, which this library imports, on a
`FastJSArrayForReadWitness`.

## Files

| File | Contents |
| --- | --- |
| `ArrayReduce/Model.lean` | The loop body, the fast path, the specification loop and the closed form of the specification |
| `ArrayReduce/Safety.lean` | The simulation and the three theorems |
| `ArrayReduce/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-reduce.tq`

| Lean | Torque |
| --- | --- |
| `Option Val` accumulator | `accumulator`, with `none` for `TheHole` |
| `Callback` | the call of `callbackfn` with `accumulatorNotHole`, `value`, `k` and `fastOW.Get()` |
| `body` | one iteration after `LoadElementNoHole`: `continue` on a hole, `accumulator = value` while the accumulator is `TheHole`, otherwise the call |
| `fastReduce` | `FastArrayReduce` |
| `cfg.smiMax < a.length` | `Cast<Smi>(len) otherwise goto Bailout(k, accumulator)` |
| `a.forRead = false` | `Cast<FastJSArrayForRead>(o) otherwise goto Bailout(k, accumulator)` |
| `fun s => .done s.acc` | the final `typeswitch (accumulator)`, where `none` stands for `ThrowTypeError(MessageTemplate::kReduceNoInitial)` |
| `Res.bailout` | `Bailout(k, accumulator)` and the call of `ArrayReduceLoopContinuation` |
| `specBody` | the loop of `ArrayReduceLoopContinuation` |
| `accumulate`, `search`, `specReduce` | the specification with and without an initial value, which searches for the first present element when there is none |

`fastReduce` loops to the array's own length, which is what
`GetLengthProperty` returns for a `JSArray`.

## Theorems

`fastReduce_safe`. For every well-formed array, every initial accumulator and
every callback satisfying `CallbackOk a.kind`, the fast path never ends in
`fatal` or `ub`.

`fastReduce_done`. Under the same hypotheses, when the fast path returns `r`,
`r = specReduce cb a init`.

`fastReduce_bailout`. Under the same hypotheses, when the fast path bails out
with indices `ks` and state `s`, there is `k ≤ a.length` with
`ks = List.range' k (a.length - k)`, the specification loop reaches `ks`, the
accumulator `s.acc` and `s.arr` from the start, and the specification loop run
on `ks` from `s.acc` and `s.arr` gives `specReduce cb a init`. The accumulator
handed to the continuation is therefore the one the specification has at that
index, including `TheHole` when no element has been seen yet.

`spec_eq` connects the specification loop to `specReduce`.

`Examples.lean` checks holes before the first element, an array of holes
without an initial value, a bailout after a callback that makes the array
non-fast, which carries the accumulator, and that a non-fast array that is still
`FastJSArrayForRead` stays on the fast path.

## Assumptions

The array satisfies `JSArr.WF`, and the callback satisfies `CallbackOk a.kind`
from `ArrayWitness`: it leaves a well-formed array whose kind is unchanged
whenever it reports the map unchanged.

## Not modeled

`ToObject`, `GetLengthProperty`, the callable check, the TypeError itself,
exceptions from the callback and the deopt continuations are outside the model.
`ArrayReduceLoopContinuation` is represented by the specification loop.
