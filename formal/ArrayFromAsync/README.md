# Lean 4 model and proofs for `Array.fromAsync`

This directory models `ArrayFromAsync` in `src/builtins/array-from-async.tq`
as a resumable state machine: the synchronous part of the builtin, the two
resolve contexts with their slots, the step labels of `ArrayFromAsyncLabels`,
`ArrayFromAsyncAwaitPoint`, the four reaction builtins and
`ArrayFromAsyncAsyncIteratorCloseOnException`. User code, promises and the event
loop are oracles: every user-observable operation and every fulfilment or
rejection of an awaited promise takes the next response of one arbitrary
stream. The library proves that no context slot read and no label dispatch can
fail for any sequence of reactions, that the outer promise is settled at most
once, and that the operations the builtin performs equal those of the
specification algorithm, written as its own resumable machine, except at five
places where V8 deviates from the specification. `Examples.lean` checks a
concrete counterexample for each of them.

## Files

| File | Contents |
| --- | --- |
| `ArrayFromAsync/Model.lean` | Values, slot types, labels, the observable operations, the resolve contexts and the Torque state machine |
| `ArrayFromAsync/Spec.lean` | The specification algorithm with its suspension points and the deviation tags |
| `ArrayFromAsync/Safety.lean` | Context slot safety and the single settlement of the outer promise |
| `ArrayFromAsync/Agreement.lean` | Agreement of the operation traces with the specification |
| `ArrayFromAsync/Examples.lean` | Executable `#guard` checks and the counterexamples |

## Correspondence with `array-from-async.tq`

| Lean | Torque |
| --- | --- |
| `JSVal`, `JSVal.isSmi`, `isNumber`, `isReceiver`, `isCallable`, `isConstructor`, `isPromise`, `isFunctionOrUndefined` | `JSAny` values and the types `Smi`, `Number`, `JSReceiver`, `Callable`, `Constructor`, `JSPromise` and `JSFunction\|Undefined` |
| `Ty`, `Ty.holds`, `chk` | the `UnsafeCast` each `*ContextSlot(...)` read performs to the type of its `Slot<..., T>`, `UnsafeCast<Callable>(mapfn)` and `UnsafeCast<JSPromise>(resultPromise)` |
| `Label`, `Label.code`, `Label.decode` | `ArrayFromAsyncLabels`, `SmiTag<ArrayFromAsyncLabels>`, `SmiUntag` after `%RawDownCast<SmiTagged<ArrayFromAsyncLabels>>` |
| `IterCtx`, `ALCtx` | `ArrayFromAsyncIterableResolveContext`, `ArrayFromAsyncArrayLikeResolveContext` and the slots of their `...ResolveContextSlots` enums |
| `IterLocals`, `ALLocals` | `ArrayFromAsyncIterableResumeState` with the locals `mappedValue` and `nextValue`, `ArrayFromAsyncArrayLikeResumeState` |
| `initIterCtx`, `initALCtx` | `CreateArrayFromAsyncIterableResolveContext`, `CreateArrayFromAsyncArrayLikeResolveContext` |
| `iterAwaitPoint`, `alAwaitPoint` | `ArrayFromAsyncAwaitPoint` through `ArrayFromAsyncIterableAwaitPoint` and `ArrayFromAsyncArrayLikeAwaitPoint` |
| `promiseResolve` | `promise::PromiseResolve` |
| `iterClose`, `CloseRes` | `ArrayFromAsyncAsyncIteratorCloseOnException` and its `RejectPromise` label |
| `iterTry`, `iterLoop` | the slot reads and the `while (true)` dispatch of `CreateArrayFromIterableAsynchronously` |
| `iterCatch`, `iterHandler`, `iterRejectFromSlots` | its `catch (e, _message)` block and `RejectArrayFromAsyncPromise` |
| `iterBody` | `CreateArrayFromIterableAsynchronously` |
| `iterOnFulfilled`, `iterOnRejected` | `ArrayFromAsyncIterableOnFulfilled`, `ArrayFromAsyncIterableOnRejected` |
| `alTry`, `alLoop`, `alCatch`, `alHandler`, `alBody` | `CreateArrayFromArrayLikeAsynchronously` |
| `alOnFulfilled`, `alOnRejected` | `ArrayFromAsyncArrayLikeOnFulfilled`, `ArrayFromAsyncArrayLikeOnRejected` |
| `smiInc` | `resumeState.index++`, which is `SmiAdd` |
| `numberOf` | the `Number` that `GetLengthProperty` returns, a Smi when it fits |
| `arrayFromAsync`, `getIterator`, `createArray` | `ArrayFromAsync`, `iterator::GetIterator(items, method)`, and the `typeswitch (c)` between `Construct` and `ArrayCreate` |
| `react`, `Event` | the promise reaction job that calls one of the two closures of a context |
| `drive`, `run` | the event loop delivering one settlement to each registered reaction |
| `reactAll`, `runEvents` | an arbitrary sequence of calls to the closures |
| `Op`, `Resp`, `perform` | the observable operations and the responses of user code and the event loop |
| `fromAsync`, `iterHead`, `iterAfterNext`, `iterDefine`, `asyncIteratorClose`, `alHead`, `alAfterValue`, `alDefine`, `resume`, `specDrive`, `specRun` | steps 3.a to 3.i of the specification, `AsyncIteratorClose`, and the suspension of the closure at each `Await` |
| `Dev` | the specification steps at which V8 deviates |

## Theorems

`runEvents_safe`. For every input, every response stream and every sequence of
fulfilments and rejections delivered to the reaction closures, at any time and
in any number, the model returns a trace: every context slot read finds a value
of its declared type, `UnsafeCast<Callable>(mapfn)` and
`UnsafeCast<JSPromise>(resultPromise)` succeed, and every dispatch on the step
label hits a defined case, so neither `ub` nor `fatal` occurs.
`runEvents_ne_ub_fatal` states the same with `ub` and `fatal` named, and
`run_safe` states it for the event loop driver.

`run_settles_at_most_once`. When the event loop delivers one settlement to each
registered reaction, the trace contains exactly one `resolve` or `reject` if the
run ends settled and none otherwise. `run_settle_le_one` is the bound by one.

`spec_agreement`. For every Smi range below `2^53 - 1`, every fuel, input and
response stream, if the specification run raises no `Dev` tag, the model
returns exactly the trace and the end state of the specification. It covers the
async iterable and the array-like branch. `spec_agreement_arrayLike` drops the
tag hypothesis for the array-like branch: whenever both iterator methods are
`undefined` or `null` and the length is at most the largest Smi, the traces
agree.

The `Dev` tags mark the five deviations. Each has a counterexample in
`Examples.lean` on the same response stream.

`closesIterator`. The specification propagates an abrupt completion of
`Call(next)`, of `Await(nextResult)`, of the object check, of
`IteratorComplete`, of `IteratorValue` and of `Set(A, "length")` without
closing the iterator. V8 catches all of them in the `catch` of lines 362 to 381
and calls `return` through `ArrayFromAsyncAsyncIteratorCloseOnException` at
line 371. The throwing sites are lines 250, 252 to 253, 258 to 260, 264, 268 to
269 and 331, and a rejected `nextResult` reaches
`ArrayFromAsyncIterableOnRejected`, which at lines 422 to 426 sets
`kCloseAsyncIterator` and closes the iterator at lines 339 to 351.

`closeAbrupt`. `AsyncIteratorClose` returns the original throw completion when
`GetMethod(iterator, "return")`, the call of `return` or the `Await` of its
result is abrupt, so the promise is rejected with the original error. The
`catch` at lines 461 to 463 swallows the exceptions of `GetProperty` at line 444,
of `Call` at line 455, including its `TypeError` for a non-callable `return`, and
of the await point at line 460, and the macro returns normally.
Its callers treat a normal return as a registered reaction: line 348 and the
fall-through to line 382 return `undefined` without rejecting, so the outer
promise never settles.

`closeRejected`. When the promise returned by `return` rejects,
`ArrayFromAsyncIterableOnRejected` overwrites the step with
`kCloseAsyncIterator` at lines 422 to 426 and the error slot at lines 427 to
430. V8 calls `return` again, and rejects with the new reason, or calls it
forever if every call rejects. The specification rejects with the original
error.

`indexOverflow`. `resumeState.index++` at lines 320 and 700 is `SmiAdd`
(`src/builtins/base.tq:1124`), which wraps
(`src/codegen/code-stub-assembler.h:452` to `465`). After the largest Smi,
`2^30 - 1` with pointer compression, the index becomes `-2^30` and the
following `CreateDataPropertyOrThrow`, mapping call, `Get` at line 655 and
length use it, and the array-like loop of line 653 never reaches a length above
the largest Smi. A constructor returning a proxy whose `defineProperty` trap
stores nothing reaches this point without exhausting memory. The specification
continues with `k = 2^30` and checks `k ≥ 2^53 - 1`, which V8 omits.
`Examples.lean` shows the wrap with `smiMax = 1` on whole runs and with the real
largest Smi on one resumption.

`nextReadTwice`. For a sync iterable, lines 915 to 918 pass the record of
`iterator::GetIterator`, which reads `next`
(`src/builtins/builtins-iterator-gen.cc:61` to `62`), to
`GetIteratorRecordAfterCreateAsyncFromSyncIterator`, which passes only the
iterator object to `CreateAsyncFromSyncIterator` (`src/builtins/iterator.tq:153`),
and that reads `next` a second time (`src/codegen/code-stub-assembler.cc:12612`
to `12613`). The specification reads it once in `GetIteratorFromMethod` and
keeps that value in the record.

Four of the deviations are observable on the V8 12.4 bundled with Node 22. A
`next` that throws makes `Array.fromAsync` call `return` before it rejects. A
`return` getter that throws after the mapping function threw leaves the result
promise pending. A `return` whose promise rejects is called again, six times
with an iterator whose `return` rejects five times, and the result is rejected
with the last reason instead of the mapping error. A sync iterable whose `next`
is a getter has the getter run twice. `indexOverflow` needs `2^30` iterations
and was not run.

## Assumptions

The closures receive the context they were created with: lines 141 to 150 and
563 to 572 allocate each pair with its own context, which justifies the
`%RawDownCast` at lines 406, 420, 766 and 780 and the separate `Ctx`
constructors. The context is private: `AllocateSyntheticFunctionContext` at
lines 107 to 111 and 524 to 528 creates it, and only the two closures, which
only the promise reaction jobs call, can reach it. The oracles therefore change
everything except the context.

Each await point registers one pair of reactions with `PerformPromiseThenImpl`
at lines 37 to 38, and a promise runs one of them once
(`src/builtins/promise-abstract-operations.tq:469` to `506`). `drive` delivers
one settlement for each registered reaction. `runEvents_safe` does not rely on
this.

The promise function slot holds the `%Promise%` of the native context, stored
at lines 820 to 821 and 941 to 943, and `PromiseResolve` with that constructor
returns a `JSPromise` (`src/builtins/promise-resolve.tq:27` to `76`). The model
lets `PromiseResolve` throw, which it can through the `constructor` getter of a
promise.

`RejectPromise` and `ResolvePromise` do not throw
(`src/builtins/promise-abstract-operations.tq:241` to `277`,
`src/builtins/promise-resolve.tq:157` to `165`), so the catch blocks never
throw and the `catch` of `ArrayFromAsync` at lines 948 to 951 never sees an
exception from lines 894 and 945. `GetLengthProperty` returns a `Number`
(`src/builtins/base.tq:1853` to `1873`), `Construct` a `JSReceiver` and
`iterator::GetIterator` an object (`src/builtins/builtins-iterator-gen.cc:37` to
`65`). `GetMethod` at `src/builtins/base.tq:1875` to `1888` returns a callable
or takes one of its two labels. `HasBuiltinSubclassingFlag` at line 811 is on,
so `C` is the receiver.

## Not modeled

The heap, property semantics and the internals of the iterator, the
async-from-sync iterator, `ToLength`, `Construct`, `ArrayCreate`,
`CreateDataPropertyOrThrow` and `Set` are oracles. The model fixes the order of
the operations of one call, not their interleaving with other jobs. The debugger
and promise hook paths of `RejectPromise` and `ResolvePromise`, the use counter,
stack overflow and out-of-memory are outside the model, and numbers are
integers.
