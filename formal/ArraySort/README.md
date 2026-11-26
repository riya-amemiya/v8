# Lean 4 model and safety proofs for `Array.prototype.sort` and `Array.prototype.toSorted`

This directory models the PowerSort implementation in
`third_party/v8/builtins/array-sort.tq`, the copying variant in
`src/builtins/array-to-sorted.tq` and the deoptimization continuations of the
inlined sort in `src/builtins/array.tq`. It proves that none of them fails a
Torque bounds check or reaches undefined behavior, for any comparator, and that
what they write is a permutation of the values they collected, followed by the
right number of `undefined` stores and deletes.

## Files

| File | Contents |
| --- | --- |
| `ArraySort/Model.lean` | The sort state, the core sort, compaction, write-back and the entry points |
| `ArraySort/Basic.lean` | The predicate `Res.Good`, segments, `PermOn` and `Vals` |
| `ArraySort/Copy.lean` | `Copy` |
| `ArraySort/Insertion.lean` | `BinaryInsertionSort`, `CountAndMakeRun` and `ReverseRange` |
| `ArraySort/Gallop.lean` | `GallopLeft` and `GallopRight` |
| `ArraySort/MergeLow.lean` | `MergeLow` |
| `ArraySort/MergeHigh.lean` | `MergeHigh` |
| `ArraySort/Stack.lean` | The run stack and `MergeAt` |
| `ArraySort/Power.lean` | `NodePower` and the bound on the run stack |
| `ArraySort/Impl.lean` | `ArrayPowerSortImpl` and the core sort theorem `sortCore_good` |
| `ArraySort/Pres.lean` | Preservation of invariants on the receiver state through the core sort |
| `ArraySort/Spec.lean` | The receiver assumptions, the specification of compaction and the write-back log |
| `ArraySort/Compact.lean` | `CompactReceiverElementsIntoWorkArray` |
| `ArraySort/Writeback.lean` | `CopyWorkArrayToReceiver` and the accessors |
| `ArraySort/Tail.lean` | `CheckAccessor` and `ArrayPowerSortTail` |
| `ArraySort/ToSorted.lean` | `ArrayPowerSortIntoCopy` and its copy macros |
| `ArraySort/Safety.lean` | The theorems about the entry points |
| `ArraySort/Order.lean` | Total preorders, the stable merge, and `mergeSort` of a concatenation |
| `ArraySort/Post.lean` | The partial correctness predicate `Res.Post` and the comparator hypothesis `CmpOK` |
| `ArraySort/SortGallop.lean` | Exact results of `GallopLeft` and `GallopRight` on a sorted run |
| `ArraySort/SortRun.lean` | Sortedness of `BinaryInsertionSort`, `CountAndMakeRun` and `ReverseRange` |
| `ArraySort/SortMergeLow.lean` | `MergeLow` computes the stable merge |
| `ArraySort/SortMergeHigh.lean` | `MergeHigh` computes the stable merge |
| `ArraySort/SortStack.lean` | `MergeAt` trims and merges two runs stably |
| `ArraySort/SortImpl.lean` | The run stack invariant through `ArrayPowerSortImpl` |
| `ArraySort/Sorted.lean` | Sortedness and stability of the entry points |
| `ArraySort/Examples.lean` | Executable `#guard` checks |

## Correspondence with the Torque sources

| Lean | Torque |
| --- | --- |
| `Core` | the fields `work_array`, `temp_array`, `pending_runs`, `pending_powers`, `pending_runs_size` and `min_gallop` of `SortState`, `array-sort.tq` line 25 |
| `ld`, `st`, `ldInt`, `setRun`, `setPower` | `objects[i]` on those arrays, which is bounds checked and fails with `Res.abort` |
| `jsAny` | `UnsafeCast<JSAny>`, which is undefined behavior on `TheHole` |
| `dcheck` | `dcheck`, undefined behavior when false |
| `Cmp`, `compare`, `sortCompare` | `Compare`, `SortCompareUserFn` and `SortCompareDefault`, lines 80, 378 and 402 |
| `getTempArray` | `GetTempArray`, line 551 |
| `copy` | `Copy`, line 568 |
| `binaryInsertionSort` | `BinaryInsertionSort`, line 614 |
| `countAndMakeRun`, `reverseRange` | `CountAndMakeRun` and `ReverseRange`, lines 680 and 723 |
| `gallop` | `GallopLeft` and `GallopRight`, lines 815 and 915 |
| `mergeLow`, `mergeHigh` | `MergeLow` and `MergeHigh`, lines 1010 and 1141 |
| `mergeAt` | `MergeAt`, line 737 |
| `nodePower`, `nodePowerValue` | the 64-bit branch of `NodePower`, line 505 |
| `nodePower32` | `NodePower32`, line 477 |
| `pushRun` | `PushRun`, line 535 |
| `mrLoop`, `mainLoop`, `mergeCollapse`, `collapseAndPush`, `finalLoop`, `powerSortImpl` | `ArrayPowerSortImpl`, line 1290 |
| `sortCore` | the choice between `BinaryInsertionSort` and `ArrayPowerSortImpl` in `ArrayPowerSortTail` and `ArrayPowerSortIntoCopy` |
| `GFA`, `gfaPush` | `GrowableFixedArray.Push` in `src/builtins/growable-fixed-array.tq` |
| `compact`, `compactFast`, `compactGeneric` | `CompactReceiverElementsIntoWorkArray`, line 1382 |
| `workArrayLength` | `CalculateWorkArrayLength`, line 126 |
| `checkAccessor` | `CheckAccessor` and `CanUseSameAccessor`, lines 90 and 417 |
| `selectAcc`, `storeTo`, `deleteAt` | the accessor choice in `CopyWorkArrayToReceiver` and `Store<...>` and `Delete<...>`, lines 300 to 376 |
| `storeLoop`, `undefLoop`, `deleteLoop`, `copyBack` | the three loops of `CopyWorkArrayToReceiver`, line 1486 |
| `sortTail` | `ArrayPowerSortTail`, line 1559 |
| `ensureWritableRecv` | `EnsureWriteableFastElements` in `src/builtins/array.tq` line 19, called from `NewSortState` |
| `arraySort` | `ArrayPrototypeSort`, `NewSortState` and `ArrayPowerSort`, lines 1592, 158 and 1582 |
| `arrayToSorted` | `ArrayPrototypeToSorted`, `array-to-sorted.tq` line 92 |
| `intoCopy`, `smiScan` | `ArrayPowerSortIntoCopy`, line 54 |
| `copyToNewFast`, `fillUndef` | `CopyWorkArrayToNewFastJSArray`, line 6 |
| `slowCopy` | `CopyWorkArrayToNewJSArray`, line 36 |
| `continueFromSnapshot` | `ArraySortContinueFromSnapshot` and `NewSortStateFromSnapshot`, `array.tq` line 116 and `array-sort.tq` line 206 |
| `continueAfterCallback` | `ArraySortConvertResultAndContinueFromSnapshot`, `array.tq` line 127, which the `AfterCallbackEager` and `Lazy` continuations at lines 148 and 156 call |
| `Env.call` | `Call` and `ToNumber_Inline` in `SortCompareUserFn` |
| `Env.str` | `ToString_Inline` and `StringCompare` in `SortCompareDefault` |
| `Env.load` | `Load<GenericElementsAccessor>` and `LoadNoHasPropertyCheck<GenericElementsAccessor>` |
| `Env.set`, `Env.del` | `SetProperty` and `DeleteProperty` in the generic `Store` and `Delete` |
| `Env.toNum` | `ToNumber_Inline` in `ArraySortConvertResultAndContinueFromSnapshot` |
| `Ext.log` | the sequence of stores and deletes the write-back performs |
| `Result.throws` | a JavaScript exception |
| `Result.throwType`, `Result.throwRange` | `kBadSortComparisonFunction` and `kInvalidArrayLength` |

The comparator and the receiver accessors are oracles in `Env`. They may return
any number, throw, or replace the receiver with any well-formed receiver, but
they never see the work array or the temp array: the core sort keeps those in
`Core`, which no oracle receives.

## Theorems

`sortCore_good`. For every comparator, if `[0, n)` of the work array holds
values, `n ≤ smiMax < 2^31` and the run stack is empty, the core sort reaches no
undefined behavior and no failed bounds check, and the work array afterwards is
a permutation of the work array before on `[0, n)` and unchanged elsewhere. The
run stack never holds more than 32 runs (`pi_size`), because the powers of the
pending runs strictly increase from the bottom of the stack and lie in
`[1, 31]`; the 85 slots of `pending_runs` hold 42 runs.

`arraySort_safe`. For every argument, every receiver satisfying `RecvOK`, every
environment satisfying `EnvOK` and every length that equals the receiver's
length when the receiver is a fast array, `arraySort` returns neither `ub` nor
`abort`.

`arraySort_perm`. Under the same assumptions and `2 ≤ len`, when `arraySort`
returns normally, compaction of the receiver as `gather` describes it returns
values `vals` and an `undefined` count `u`, and the write-back log equals
`writeLog sorted u len` for some permutation `sorted` of `vals`: the stores of
`sorted` to `[0, sorted.length)`, then `u` stores of `undefined`, then deletes
up to `len`.

`arrayToSorted_safe` and `arrayToSorted_perm`. The same for `toSorted`, where
the new array's backing store is `sorted` followed by `u` copies of
`undefined` and its length is `len`.

`continueFromSnapshot_safe` and `continueFromSnapshot_perm`. For every
environment, every receiver state and every snapshot `temp` whose slots
`[0, len)` hold values, with `len ≤ smiMax < 2^31`, the continuation reaches no
undefined behavior and no failed bounds check, and when it returns normally it
appends `writeLog sorted 0 len` to the log, for some permutation `sorted` of
the values in `[0, len)` of the snapshot.

`continueAfterCallback_safe` and `continueAfterCallback_perm`. The same after
`ToNumber` of the comparator result.

`sortCore_sorted`. If `le` is a total preorder (`TotalPreorder le`) and every
answer of the comparator is negative exactly when `le y x = false`
(`CmpOK le cmp`), the core sort additionally leaves `[0, n)` equal to
`msort le` of the input region, where `msort le` is `List.mergeSort` under the
order `le` lifted to the slots. Because `List.mergeSort` is stable, this states
sortedness and stability at once: equivalent values keep their input order.

`arraySort_sorted`. Under the assumptions of `arraySort_perm` and `CmpOK` for the
comparator the call uses, the write-back log is
`writeLog (vals.mergeSort le) u len`.

`arrayToSorted_sorted`. Under the assumptions of `arrayToSorted_perm` and
`CmpOK`, the new array's backing store is `(vals.mergeSort le).map some`
followed by `u` copies of `undefined`.

`continueFromSnapshot_sorted`. Under the assumptions of
`continueFromSnapshot_perm` and `CmpOK`, the continuation appends
`writeLog (snapshot.mergeSort le) 0 len`.

`cmpOK_user` and `cmpOK_default` reduce `CmpOK` to the oracles: for a user
comparator, `env.call` returns a negative number exactly when `le y x = false`
and NaN never stands for "less"; for the default comparator, the same holds for
`SmiLexicographicCompare` on Smi pairs and for `env.str` on the other pairs.

The order proofs follow the merges step by step. Each run on the stack holds
`msort le` of its input range. `GallopLeft` and `GallopRight` return exactly
the boundary of the elements strictly below, or at most, the key. `MergeLow`
and `MergeHigh` keep the invariant that the merged output so far, followed by
the stable merge of the remaining parts of both runs, is the stable merge of
the two runs, including the exits that copy the last element of one run and the
initial trimming in `MergeAt`. A strictly descending run reversed by
`CountAndMakeRun` is the stable sort of that run because it contains no two
equivalent elements. The library lemma `msort_append` proves that the stable
merge of the stable sorts of two adjacent ranges is the stable sort of their
concatenation, through a characterization of the stable sort by permutation,
sortedness and the order of each equivalence class.

None of the galloping steps breaks order or stability for a consistent
comparator.

No V8 bug was found. Every `dcheck` on these paths holds, including those in
`MergeLow`, `MergeHigh`, `GallopLeft`, `GallopRight`, `Copy`, `MergeAt`,
`PushRun`, the minrun computation and the strict-power check in
`ArrayPowerSortImpl`. `PushRun` checks `stackSize < kMaxMergePending`, which
is weaker than the 42 runs that fit in `pending_runs`; the bound of 32 runs
makes the difference unreachable.

## Assumptions

`RecvOK` is the well-formedness of every receiver state the builtins observe.

1. `JSArr.WF` from `Torque/JSArray.lean`.
2. The elements kind is a function of the map, as `CheckAccessor` and
   `CopyWorkArrayToReceiver` read it from `receiver.map.elements_kind`
   (`array-sort.tq` lines 94 and 1494).
3. A receiver is a fast array exactly when its map passes the map checks of
   `CastFastJSArray` and the NoElements protector is valid
   (`src/builtins/cast.tq` lines 584 to 598).
4. A double backing store holds numbers, holes and, only with
   `V8_ENABLE_UNDEFINED_DOUBLE`, `undefined`; loads box values into heap
   numbers (`array-sort.tq` lines 1438 to 1452 and 323 to 339). `Cfg.ud`
   stands for `kEnableUndefinedDouble`.

`EnvOK` requires that every oracle maps a receiver satisfying `RecvOK` to one
that satisfies `RecvOK`, never re-validates a protector, and never installs a
copy-on-write backing store. Protectors only expose `Is...Intact` and
`Invalidate...` outside fuzzing (`src/execution/protectors.h` lines 107 to
114). `NewSortState` makes the backing store of a fast receiver writable
before sorting (`array-sort.tq` line 171 and `src/builtins/array.tq` lines 19
to 34), and the fast stores rely on it staying so.

The length passed to `arraySort` and `arrayToSorted` equals the receiver's
length when the receiver is a fast array, because `GetLengthProperty` returns
`a.length` for a `JSArray` (`src/builtins/base.tq` lines 1857 and 1858).
`smiMax < 2^31` holds for both Smi sizes (`include/v8-internal.h` lines 86 to
90 and 136 to 140).

The snapshot continuations assume that `[0, len)` of `temp` holds values and
that `len` is a Smi. Their callers guarantee it.
`JSCallReducer::ReduceArraySort` (`src/compiler/js-call-reducer.cc` lines 4154
to 4187) inlines only packed, non-double kinds, and
`ReduceArrayPrototypeSort` (lines 1757 to 1997) takes the inline path only for
lengths up to `kMaxInlineSortSize = JSArray::kMaxInlineSortLength = 16`
(`src/objects/js-array.h` line 140), allocates a temp array of 16 slots
initialized to Smi zero, and copies the receiver's elements into `[0, len)`
before the first comparator call, deoptimizing on `undefined`. After each shift
of the insertion sort it writes the pivot back, so the temp array stays a
permutation of the copied elements at every deoptimization point.
`MaglevGraphBuilder::TryReduceArrayPrototypeSort`
(`src/maglev/maglev-graph-builder.cc` line 9654) follows the same scheme with
the same constant at line 9794.

The sortedness theorems assume `TotalPreorder le` and `CmpOK le cmp`. The model
of the comparator never sees the work array or the temp array, so a comparator
with side effects on the receiver satisfies them as long as its answers depend
only on the two values. Every comparison in the Torque code tests only
`order < 0` or `order >= 0` (`array-sort.tq` lines 641, 699 to 709, 827 to 894,
927 to 992, 1052 and 1184, modeled by `compare` and `compareKey`), so the sign
of the answer is all the hypothesis has to fix.

## Not modeled

`ToObject` and `GetLengthProperty` are outside the model, which takes the
receiver and its length as inputs. Non-Smi lengths are covered only by the
range check. The model fixes `Is64()`; `NodePower32` is checked against
`nodePowerValue` only by the examples. `min_gallop` is an unbounded integer, so
a Smi overflow of it is not represented. The generic `SetProperty` calls of
`CopyWorkArrayToNewJSArray` on the fresh copy are modeled as plain stores, so
setters on `Array.prototype` are not represented. After a throw the theorems
say nothing about the receiver or the log. Loops that would not make progress
return `ub` in the model to keep it total, and the safety theorems show that
these branches are unreachable. `IsForceSlowPath` is not modeled.
