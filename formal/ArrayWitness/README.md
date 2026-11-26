# Lean 4 model and safety proofs for the witness-based iteration loop

`ArrayWitness` models the fast loop that the iteration builtins build on
`FastJSArrayWitness` and `FastJSArrayForReadWitness` in
`src/objects/js-array.tq`, and proves once, for any loop body, that the loop
never fails a bounds check or a backing store cast and that it agrees with the
specification loop, both when it finishes and when it bails out to the
continuation builtin. `ArrayEvery`, `ArraySome`, `ArrayForEach`, `ArrayFind`,
`ArrayFindIndex`, `ArrayFindLast`, `ArrayFindLastIndex`, `ArrayReduce`,
`ArrayReduceRight`, `ArrayFilter`, `ArrayMap` and `ArrayFlatMap` build on it.

## Files

| File | Contents |
| --- | --- |
| `ArrayWitness/Model.lean` | Callback results, the witness load, the fast loop, the index orders and the specification loop |
| `ArrayWitness/Safety.lean` | The loop invariant, the simulation condition and the generic loop theorems |
| `ArrayWitness/Examples.lean` | Executable `#guard` checks |

## Correspondence with `js-array.tq`

| Lean | Torque |
| --- | --- |
| `Post` | what a callback call hands back to the loop: its result, the array afterwards, whether its map is still the witness `map`, and whether the no-elements protector is still valid |
| `Post.recheck` | `Recheck`, which compares `stable.map` with `map` and tests `IsNoElementsProtectorCellInvalid` |
| `load` | `LoadElementNoHole` of both witnesses, whose `Cast<FixedDoubleArray>` or `Cast<FixedArray>` ends in `unreachable` when `hasDoubles` does not match the backing store, and whose indexed read is bounds checked |
| `get` | `HasProperty` and `GetProperty` in the continuation builtins, with holes and indices at or past the current length absent |
| `St` | the loop state: the accumulator of the builtin, the array `Get()` returns, and whether the next `Recheck` succeeds |
| `loop` | the shared loop: `Recheck() otherwise goto Bailout(k)`, `if (k >= fastOW.Get().length) goto Bailout(k)`, `LoadElementNoHole`, then the body of the builtin |
| `forward`, `backward` | the index orders `0, ..., len - 1` and `len - 1, ..., 0` |
| `Res.bailout` | `Bailout(k)`, carrying the indices left and the state |
| `Res.fatal` | a failed bounds check or `unreachable` |
| `Res.ub` | undefined behavior reported by a loop body |
| `SBody`, `spec` | the specification loop that the continuation builtins run |
| `Reaches` | a run of the specification loop from one state to a later one |

`load` is called with the `hasDoubles` flag of the kind the witness was created
with, while `St.arr` is the array as user code left it.

## Theorems

`loop_ok`. Let `Sim K body sbody fin sfin R Q` hold, meaning that for
accumulators related by `R`, a step of `body` on a well-formed array of kind
`K` at an index below its length either continues with a state whose
accumulator is related by `R` to the one `sbody` produces, whose array is the
array `sbody` produces, and which satisfies `Inv K`, or stops with a result
related by `Q` to the one `sbody` stops with, and that `fin` returns `done` with
a result related by `Q` to the result of `sfin`. Then for
every state `s` with `Inv K s` and `R ks s.acc b`, the loop over `ks` never ends
in `fatal` or `ub`, a result `done r` satisfies
`Q r (spec sbody sfin ks b s.arr)`, and a bailout with indices `ks'` and state
`s'` comes with a specification accumulator `b'` such that the specification
loop reaches `ks'`, `b'` and `s'.arr` from `ks`, `b` and `s.arr`,
`R ks' s'.acc b'` and `Inv K s'` hold, and `ks'` is a suffix of `ks`.
`loop_ne_fatal`, `loop_ne_ub`, `loop_done` and `loop_bailout` state these cases
separately.

`Reaches.spec_eq`. If the specification loop reaches one state from another,
running it to the end from either state gives the same result. Together with
`loop_bailout`, this shows that the continuation started at the bailout state
returns what the specification returns from the start.

`forward_bailout` and `backward_bailout`. For the loops over `forward len` and
`backward len`, the indices left at a bailout are `List.range' k (len - k)` for
some `k ≤ len`, or `backward m` for some `m ≤ len`, so the continuation resumes
at a single index.

`Inv K s` says that `s.arr` is well formed and that its kind is `K` whenever
`s.ok` holds. This is what makes the load safe: a successful `Recheck` implies
an unchanged kind, so the `hasDoubles` flag still matches the backing store,
and `load_ok` shows that the load then returns `get` below the length.
`Examples.lean` checks that `load` fails when `hasDoubles` does not match the
kind and when the index is past the backing store, the two ways the loop can
reach `fatal`.

## Assumptions

The generic theorems take `Sim`, which each builtin proves for its own body,
and `Inv K s` for the start state, which `inv_start` gives for every array
satisfying `JSArr.WF`. The builtins prove `Sim` from `CallbackOk K cb`, through
`inv_post`: every callback leaves a well-formed array, and when it reports the
map unchanged, the kind is still `K`. The comment in `Recheck` states the V8
side of the second half: if the map remains the same, the elements kind and the
prototype have not changed.

## Not modeled

The witness methods that write, `EnsureArrayPushable`, `ChangeLength`, `Push`,
`MoveElements` and `StoreHole`, are not part of this loop. `ArrayFilter` models
`Push` itself and `ArrayShift` models the shift through `InPlace`. The deopt
continuation builtins, exceptions thrown by callbacks and `thisArg` are outside
the model.
