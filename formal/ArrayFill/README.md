# Lean 4 model and safety proofs for the `Array.prototype.fill` fast path

This directory contains a machine-checked model of `TryFastArrayFill` in
`src/builtins/builtins-array.cc`, the index computation of
`BUILTIN(ArrayPrototypeFill)` that feeds it, and the parts of the elements
accessors in `src/objects/elements.cc` that it calls. Unlike `TryFastFlat` and
`TryFastArrayCopyWithin`, this fast path is C++, not Torque. The model builds on
the shared library in `formal/Torque`, and `formal/README.md` describes how to
check the proofs.

## Files

| File | Contents |
| --- | --- |
| `ArrayFill/Model.lean` | Index computation, the elements kind handling, the accessor fill, the length update and the specification result |
| `ArrayFill/Safety.lean` | Absence of undefined behavior, result well-formedness, agreement with the specification, and the condition under which the `SetLengthImpl` DCHECK fails |
| `ArrayFill/Examples.lean` | Executable `#guard` checks, and a proof that the DCHECK fails with V8's constants |

## Correspondence with the C++ sources

| Lean | V8 |
| --- | --- |
| `relIndex`, `startIndex`, `endIndex` | `GetRelativeIndex` |
| `fastPath` | `BUILTIN(ArrayPrototypeFill)` from the empty range check to the call of `TryFastArrayFill` |
| `tryFast` | `TryFastArrayFill` |
| `FillConfig.maxLen`, `FillConfig.maxFast` | `FixedArray::kMaxLength` and `JSArray::kMaxFastArrayLength` |
| `FillConfig.undefinedDouble` | `V8_ENABLE_UNDEFINED_DOUBLE`, which `v8_enable_undefined_double` in `BUILD.gn` turns on by default |
| `Env.movingAllowed`, `Env.isArrayPrototype` | `IsJSArrayFastElementMovingAllowed` and `IsInitialArrayPrototype` in `IsJSArrayWithAddableFastElements` |
| `Env.readOnlyLength` | `HasReadOnlyLength` in `JSArray::WouldChangeReadOnlyLength` |
| `Env.replaced` | whether `GetReplacedElementsKindsMap` returns a map |
| `Torque.optimalKind` | `Object::OptimalElementsKind` |
| `prepare` | the elements kind handling between `OptimalElementsKind` and `GetElementsAccessor` |
| `replaceAll` | the `is_replacing_all_elements` branch, which may move the map backwards and reallocates the backing store when the doubleness differs or it is copy-on-write |
| `transition`, `Torque.Kind.moreGeneral`, `Torque.Kind.transitionTarget` | `GetMoreGeneralElementsKind` and `JSObject::TransitionElementsKind`, which makes the target holey when the source is holey |
| `Torque.Kind.isMoreGeneral` | `IsMoreGeneralElementsKindTransition` for fast targets |
| `accessorFill` | `FillImpl` of the Smi and object accessors, which calls `EnsureWritableFastElements`, and of the double accessor, which does not |
| `Torque.growTo` | `EnsureFillRangeCapacity` through `GrowCapacityAndConvertImpl`, whose copy initializes the new slots to the hole |
| `numberValueOk` | `Object::NumberValue`, which casts a non-Smi to `HeapNumber` without a check in release builds, and the `set_undefined` branch of the double `FillImpl` |
| `setLength` | `accessor->SetLength`, that is `SetLengthImpl` with its `DCHECK(!array->SetLengthWouldNormalize(length))`, which makes the kind holey when the length grows |
| `Result.ub` | a write into a copy-on-write backing store, `NumberValue` on a value that is neither a Smi nor a `HeapNumber`, or a write past the backing store |
| `Result.done a true` | a call of `SetLengthImpl` that fails its DCHECK |
| `specFill` | steps 7 and 8 of the specification on an array whose holes are absent elements, where `Set` past the length grows the length |

`fastPath` takes the array `a` as it is after the `ToInteger` calls and the
length `len` read before them as independent inputs, so the theorems cover any
change user code makes to the array in between, including a length shrunk below
`end` and a dictionary array that became fast again.

## Theorems

`fastPath_ne_ub`. For every well-formed array, every length and every argument,
the fast path never writes into a copy-on-write backing store, never reads a
non-number as a double, and never writes past the backing store.

`fastPath_done`. When the fast path handles the call with a non-empty range, the
array stays well-formed, its spare slots stay holes, its backing store is no
longer copy-on-write, its length is the larger of the current length and `end`,
and its elements equal the specification result on the current elements.

`fastPath_dcheck`. The DCHECK of `SetLengthImpl` fails only when the current
length is smaller than the length read before the `ToInteger` calls and `end`
exceeds `JSArray::kMaxFastArrayLength`. `fastPath_done` gives the converse for
any call the fast path handles.

`tryFast_handles`. The fast path handles every call on a fast array that passes
the explicit checks of `TryFastArrayFill`, so neither the accessor nor the
length update reports a failure.

The proof of `fastPath_ne_ub` uses three facts. A double kind after the kind
handling comes from a number, or from `undefined` when
`V8_ENABLE_UNDEFINED_DOUBLE` is on, because `OptimalElementsKind` maps every
other value to an object kind and every transition towards it leaves the double
kinds. A double kind after the kind handling never has a copy-on-write backing
store. The backward branch reallocates when the doubleness changes,
`TransitionElementsKind` either reallocates or keeps `empty_fixed_array`, whose
map is `fixed_array_map`, and a double array never has a copy-on-write backing
store to begin with. `EnsureFillRangeCapacity` grows the backing store to `end`
before any write. `Examples.lean` checks that the accessor fill fails, which
`tryFast` turns into `Result.ub`, for an object value in a double array and for
a copy-on-write double backing store.

## Finding: `SetLengthImpl` DCHECK failure

When user code in `ToInteger` shrinks the length below `end`, `TryFastArrayFill`
restores it with `accessor->SetLength(isolate, array, end)`. This skips
`JSArray::SetLength`, which normalizes the array to dictionary elements when
`SetLengthWouldNormalize(end)` holds, and `SetLengthImpl` begins with
`DCHECK(!array->SetLengthWouldNormalize(length))`. `SetLengthWouldNormalize(n)`
is `n > JSArray::kMaxFastArrayLength`, which is `32 * 1024 * 1024`, or
`1024 * 1024` with `V8_LOWER_LIMITS_MODE`, while the fast path accepts `end` up
to `FixedArray::kMaxLength`. Every `end` in between fails the DCHECK in builds
with DCHECKs, which `dcheck_always_on` also enables.

The following script reaches that state according to the sources read, and was
not run.

```js
const a = [];
for (let i = 0; i < 32 * 1024 * 1024 + 1; i++) a.push(0);
a.fill(1, { valueOf() { a.length = 1; return 0; } });
```

`Array.prototype.push` keeps the array fast past `kMaxFastArrayLength`. Its CSA
builtin falls back to `BUILTIN(ArrayPush)`, whose `AddArguments` grows a fast
backing store without that limit, and `Runtime_GrowArrayElements`, which
inlined pushes call, either grows the fast backing store or returns zero
without normalizing the array. `GetLengthProperty`
reads `32 * 1024 * 1024 + 1` before `valueOf` sets the length to 1 without
normalization, so `end` keeps the old length. The value is a Smi and the array is
`PACKED_SMI_ELEMENTS`, so no transition happens. `FillImpl` grows the backing
store to `end`, and the length 1 is then below `end`. `dcheck_reachable` in
`Examples.lean` proves that the model reaches `Result.done a true` on this
input with V8's constants.

In a release build `SetLengthImpl` sets the length to `end` on fast elements.
`fastPath_done` shows that this result is well-formed and equals the
specification result, and a fast array longer than `kMaxFastArrayLength` is
already reachable through `Array.prototype.push`, so the failure is in the
DCHECK and not in memory safety.

## Assumptions

The array satisfies `JSArr.WF` from `formal/Torque`. `fastPath_ne_ub` needs
nothing else. `fastPath_done` also assumes `JSArr.SlackHoles`, the invariant that
the slots between the length and the end of the backing store hold the hole.
`SetLengthImpl` fills them with holes when it shortens an array, and the copy in
`GrowCapacityAndConvertImpl` initializes new slots to the hole. The fast path
needs the invariant because a length that grows to `end` turns spare slots
below `start` into elements, and the specification requires them to be absent.

`IsJSArrayFastElementMovingAllowed` accepts the array only when its prototype
chain has no elements, either through the initial array prototype with an
intact `NoElementsProtector` or through `JSObject::PrototypeHasNoElements`, so a
hole is an absent element, which is how `specFill` treats it.

## Not modeled

`GenericArrayFill`, `ToObject`, `GetLengthProperty` and the double arithmetic of
`GetRelativeIndex` are outside the model, which takes the integer arguments as
`Int`. The model's `ensureWritable` keeps only the first `length` slots of a
copied backing store, NaN canonicalization, write barriers, allocation sites,
`NotifyLeafMapLayoutChange`, `UpdateNoElementsProtectorOnSetLength` and the
backing store trimming in `SetLengthImpl` are not modeled, and an allocation
failure is not a result. The faithfulness of the hand translation from C++ to
Lean is outside the proofs.
