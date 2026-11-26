# Lean 4 model and safety proofs for `Array.prototype.join`, `toString` and `toLocaleString`

This directory models the JSArray half of `src/builtins/array-join.tq`, the
C++ routine `WriteChunkListToFlat` in `src/objects/objects.cc` that turns the
join buffer into a string, and the join stack that detects cyclic joins. It
proves that the buffer never fails a Torque bounds check or reaches an
`unreachable`, that the C++ writer writes exactly as many characters as the
buffer reserved and only copies characters it has already written, that the
fast path returns the specification result, and that the join stack restores
its contents after every nested call.

## Files

| File | Contents |
| --- | --- |
| `ArrayJoin/Buffer.lean` | The Torque `Buffer`, its chunks, and the C++ writer |
| `ArrayJoin/Cycle.lean` | The closed form of the doubling copy that writes repeated strings |
| `ArrayJoin/BufferSafety.lean` | The buffer invariant and its preservation by appends and repeats |
| `ArrayJoin/BufferSpec.lean` | `Buffer.Add`, the trailing separators and `BufferJoin` |
| `ArrayJoin/Fast.lean`, `ArrayJoin/FastSafety.lean` | `FastArrayJoin` and its specification |
| `ArrayJoin/Generic.lean`, `ArrayJoin/GenericSafety.lean` | `ArrayJoinImpl`, the loader selection in `ArrayJoin<JSArray>` and the empty dictionary shortcut |
| `ArrayJoin/Stack.lean` | `JoinStackPushInline`, `JoinStackPopInline` and `CycleProtectedArrayJoin` |
| `ArrayJoin/Entry.lean` | `ArrayPrototypeJoin`, `ArrayPrototypeJoinImpl`, `ArrayPrototypeToString`, `ArrayPrototypeToString_Inline` and `ArrayPrototypeToLocaleString` |
| `ArrayJoin/Examples.lean` | Executable `#guard` checks |

## Correspondence with the sources

| Lean | Source |
| --- | --- |
| `Item.str`, `Item.seps`, `Item.rep` | a string, a positive Smi separator count and a negative Smi repeat count in a chunk |
| `Buf.full`, `Buf.cap`, `Buf.cur` | the filled chunks of the linked list, the length of the current chunk and its entries after the link slot |
| `newBuffer` | `NewBuffer` |
| `appendToChunk` | `Buffer.AppendToChunk`, with `grow` for `CalculateNewElementsCapacity` and `Limits.maxChunk` for `kMaxBufferChunkSize` |
| `repeatLast` | `Buffer.RepeatLast` |
| `addSeparators`, `addLen` | `Buffer.AddSeparators` and `AddStringLength` |
| `add` | `Buffer.Add` |
| `bufferJoin` | `BufferJoin` |
| `writeChunks`, `readChunk`, `slots` | the chunk loop of `WriteChunkListToFlat`, its `CHECK`s on the chunk length, and the zeroed slots of `AllocateZeroedFixedArray` |
| `wItem`, `writeSeps` | one iteration of the element loop, including the separator writes |
| `repStep`, `dbl`, `repTail` | the repeat branch: the doubling `memcpy` loop and the final `memcpy` |
| `fastNext`, `fastLoop`, `finalSeps`, `fastArrayJoin` | `FastArrayJoin` for the six fast elements kinds |
| `loadFast`, `load`, `cannotUseSame` | `LoadJoinElement` for fast object and double elements, the generic accessor, and `CannotUseSameArrayAccessor<JSArray>` |
| `implLoop`, `implJoin` | `ArrayJoinImpl<JSArray>` |
| `select`, `arrayJoin` | `ArrayJoin<JSArray>` |
| `earlyThrow` | the separator overflow check at the start of `CycleProtectedArrayJoin` |
| `pushInline`, `joinStackPush`, `popInline`, `joinStackPop` | `JoinStackPushInline`, `JoinStackPush`, `JoinStackPopInline` and `JoinStackPop` |
| `cycleJoin`, `cycleProtected` | `CycleProtectedArrayJoin` |
| `joinImpl`, `arrayPrototypeJoin` | `ArrayPrototypeJoinImpl` and `ArrayPrototypeJoin` |
| `toStringInline`, `arrayPrototypeToString` | `ArrayPrototypeToString_Inline` and `ArrayPrototypeToString` |
| `arrayPrototypeToLocaleString` | `ArrayPrototypeToLocaleString` |

`Res.fatal` stands for a failed Torque bounds check, a failed `CHECK` or an
`unreachable`, and `Res.ub` for a violated `dcheck` whose release behaviour
corrupts the buffer, a store past the end of the result string, a read of
characters not yet written, or an `UnsafeCast` that does not hold. The writer
returns `none` in all of the latter cases.

## Theorems

`bufferJoin_spec` together with `add_spec` and `finish_spec`. As long as every
added string is non-empty and the pending separator count is at least one
whenever the buffer is not empty, `Buffer.Add` and the trailing
`AddSeparators` either throw a range error or produce a buffer from which
`BufferJoin` returns exactly the concatenation the additions describe. In
particular `WriteChunkListToFlat` writes exactly `totalStringLength`
characters, so its `DCHECK_EQ(sink, sink_end)` holds, every `memcpy` in the
repeat branch reads from characters already written in the current repeated
region, and the `CHECK`s on chunk lengths pass.

`rep_closed` is the core of that result. When the last written string `s` is
non-empty and followed by one separator, the doubling copy of
`WriteChunkListToFlat` writes `s` repeated with separators exactly `n` more
times. `Examples.lean` checks that repeating an empty string after a
separator makes the final `memcpy` read one character before the start of the
result string.

`fastArrayJoin_spec`. For a well-formed fast array, `FastArrayJoin` throws a
range error, bails out, or returns `fastSpec`, the specification join of the
array as it is after `ToString(separator)`: elements up to the current length
converted, holes, `undefined` and `null` as empty strings, and the elements
past a length that user code shortened as empty strings. It never fails a
bounds check, never casts a non-Smi to a Smi and never reads a hole as a
double.

`implJoin_spec` and `arrayJoin_spec`. For every environment whose arrays are
well-formed, the generic loop throws or returns the join of exactly the
strings it obtained from its loads and conversions, one per index. The fast
loaders never fail their bounds checks because `CannotUseSameArrayAccessor`
switches to the generic accessor as soon as the elements kind or the length
differs from the values the loader was chosen for. `inner_spec` discharges the
separator bound from `earlyThrow`.

`cycleJoin_preserves` and `cycleProtected_preserves`. If the join stack holds
the receivers of the joins in progress, in call order and without duplicates,
then a cycle-protected join whose inner computation keeps that property for
the extended list never reaches the `unreachable` in `JoinStackPop` or
`JoinStackPopInline`, and leaves the stack holding the original list, on
normal return and on exceptions. A nested cycle-protected join is such an
inner computation, so the theorem applies to any nesting depth.
`cycleJoin_cycle` states that a receiver already on the stack makes the join
return the empty string without running the inner computation.

`joinImpl_spec`, `joinImpl_safe`, `arrayPrototypeJoin_safe` and
`toStringInline_eq` connect the entry builtins to these results.

## Deviation from the specification in `toLocaleString`

`LoadJoinElement<array::FastSmiOrObjectElements>`,
`LoadJoinElement<array::FastDoubleElements>` and the `IfHole` branch of
`LoadJoinElement<array::DictionaryElements>` return `kEmptyString` for a hole.
`ArrayJoinImpl` with `useToLocaleString` then passes that string to
`ConvertToLocaleString`, which calls `String.prototype.toLocaleString` on it.
ECMA-262 23.1.3.18.1 `JoinIndexedProperties`, which
`Array.prototype.toLocaleString` calls, reads the element with
`Get(obj, ! ToString(𝔽(k)))` and only invokes `toLocaleString` "If element is
neither undefined nor null". A hole in an array whose prototypes have no
elements reads as `undefined`, so the specification invokes nothing for it.
The two differ as soon as user code replaces `String.prototype.toLocaleString`.
On the V8 12.4 bundled with Node 22, after
`String.prototype.toLocaleString = function () { return "X"; }`,
`[1, , 2].toLocaleString()` returns `"1,X,2"` and `[1.5, , 2.5].toLocaleString()`
returns `"1.5,X,2.5"`, while `[1, undefined, 2].toLocaleString()` returns
`"1,,2"`. `Examples.lean` reproduces the difference: the fast object loader
produces `1,X,2` and the generic accessor, which follows the specification,
produces `1,,2`. `join` and `toString` are not affected, because their
typeswitch skips the empty string without a call. The ECMA-402 text of
`Array.prototype.toLocaleString` was not consulted.

## Assumptions

The canonical empty string is the only zero-length string, as the comment in
`FactoryBase<Impl>::AllocateRawOneByteInternalizedString` in
`src/heap/factory-base.cc` states and the `DCHECK_GT(length, 0)` in
`NewRawStringWithMap` enforces. The model therefore treats the identity check
`str == kEmptyString` as a check for an empty character list. `Examples.lean`
shows why the repeat branch depends on it.

`Limits.OK` states that `kMaxBufferChunkSize` is at least 2 and that
`String::kMaxLength` fits in a Smi and in an `intptr`.

Every array the environment can observe satisfies `JSArr.WF`, and the
receivers passed to `FastArrayJoin` are fast arrays, as
`CastFastJSArrayForRead` and the kind dispatch in `ArrayPrototypeJoinImpl`
guarantee.

## Not modeled

The one-byte or two-byte choice of the result string, the TypedArray loaders,
nonextensible elements kinds, and the contents of dictionary elements are
outside the model. The dictionary loader is folded into the generic accessor.
Property lookups, `ToString`, `ToLocaleString` and every other call into user
code are oracles of the environment, which may change the array between
loads.
