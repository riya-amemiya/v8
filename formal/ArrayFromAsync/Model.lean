import Torque

namespace ArrayFromAsync

open Torque

inductive JSVal where
  | undef
  | null
  | bool (b : Bool)
  | smi (n : Int)
  | heapNumber (n : Int)
  | str (n : Nat)
  | obj (id : Nat)
  | fn (id : Nat)
  | ctor (id : Nat)
  | promise (id : Nat)
  | promiseCtor
  | reaction (onFulfilled : Bool)
  | asyncFromSyncIterator
  | asyncFromSyncNext
  | typeError
  deriving DecidableEq, Repr

namespace JSVal

def isSmi : JSVal → Bool
  | smi _ => true
  | _ => false

def isNumber : JSVal → Bool
  | smi _ => true
  | heapNumber _ => true
  | _ => false

def isReceiver : JSVal → Bool
  | obj _ => true
  | fn _ => true
  | ctor _ => true
  | promise _ => true
  | promiseCtor => true
  | reaction _ => true
  | asyncFromSyncIterator => true
  | asyncFromSyncNext => true
  | typeError => true
  | _ => false

def isCallable : JSVal → Bool
  | fn _ => true
  | ctor _ => true
  | promiseCtor => true
  | reaction _ => true
  | asyncFromSyncNext => true
  | _ => false

def isConstructor : JSVal → Bool
  | ctor _ => true
  | promiseCtor => true
  | _ => false

def isPromise : JSVal → Bool
  | promise _ => true
  | _ => false

def isFunctionOrUndefined : JSVal → Bool
  | undef => true
  | fn _ => true
  | ctor _ => true
  | promiseCtor => true
  | reaction _ => true
  | asyncFromSyncNext => true
  | _ => false

def isNullish : JSVal → Bool
  | undef => true
  | null => true
  | _ => false

def truthy : JSVal → Bool
  | undef => false
  | null => false
  | bool b => b
  | smi n => n != 0
  | heapNumber n => n != 0
  | str n => n != 0
  | _ => true

def toReceiver (v : JSVal) : JSVal := if v.isReceiver then v else .obj 0

def lengthOf : JSVal → Nat
  | smi n => n.toNat
  | heapNumber n => min n.toNat (2 ^ 53 - 1)
  | _ => 0

def num : JSVal → Int
  | smi n => n
  | heapNumber n => n
  | _ => 0

end JSVal

inductive Ty where
  | smi
  | number
  | any
  | promise
  | receiver
  | callable
  | functionOrUndefined
  deriving DecidableEq, Repr

def Ty.holds : Ty → JSVal → Bool
  | .smi, v => v.isSmi
  | .number, v => v.isNumber
  | .any, _ => true
  | .promise, v => v.isPromise
  | .receiver, v => v.isReceiver
  | .callable, v => v.isCallable
  | .functionOrUndefined, v => v.isFunctionOrUndefined

def obind {α β : Type} : Outcome α → (α → Outcome β) → Outcome β
  | .ok a, f => f a
  | .bailout, _ => .bailout
  | .throwRange, _ => .throwRange
  | .ub, _ => .ub
  | .fatal, _ => .fatal

def omap {α β : Type} (f : α → β) (v : Outcome α) : Outcome β := obind v fun a => .ok (f a)

def chk {α : Type} (t : Ty) (v : JSVal) (k : JSVal → Outcome α) : Outcome α :=
  if t.holds v then k v else .ub

inductive Label where
  | getIteratorStep
  | checkIteratorValueAndMapping
  | iteratorMapping
  | getIteratorValueWithMapping
  | addIteratorValueToTheArray
  | getArrayLikeValue
  | checkArrayLikeValueAndMapping
  | getArrayLikeValueWithMapping
  | addArrayLikeValueToTheArray
  | doneAndResolvePromise
  | closeAsyncIterator
  | rejectPromise
  deriving DecidableEq, Repr

def Label.code : Label → Int
  | .getIteratorStep => 0
  | .checkIteratorValueAndMapping => 1
  | .iteratorMapping => 2
  | .getIteratorValueWithMapping => 3
  | .addIteratorValueToTheArray => 4
  | .getArrayLikeValue => 5
  | .checkArrayLikeValueAndMapping => 6
  | .getArrayLikeValueWithMapping => 7
  | .addArrayLikeValueToTheArray => 8
  | .doneAndResolvePromise => 9
  | .closeAsyncIterator => 10
  | .rejectPromise => 11

def Label.all : List Label :=
  [.getIteratorStep, .checkIteratorValueAndMapping, .iteratorMapping, .getIteratorValueWithMapping,
    .addIteratorValueToTheArray, .getArrayLikeValue, .checkArrayLikeValueAndMapping,
    .getArrayLikeValueWithMapping, .addArrayLikeValueToTheArray, .doneAndResolvePromise,
    .closeAsyncIterator, .rejectPromise]

def Label.decode (n : Int) : Option Label := Label.all.find? fun l => l.code == n

theorem Label.decode_code (l : Label) : Label.decode l.code = some l := by
  cases l <;> rfl

inductive Op where
  | getAsyncIteratorMethod (items : JSVal)
  | getIteratorMethod (items : JSVal)
  | callIteratorMethod (method items : JSVal)
  | getNextMethod (iterator : JSVal)
  | getLength (arrayLike : JSVal)
  | construct (c : JSVal) (len : Option Nat)
  | arrayCreate (len : Nat)
  | callNext (next iterator : JSVal)
  | await (v : JSVal)
  | iteratorComplete (r : JSVal)
  | iteratorValue (r : JSVal)
  | get (o : JSVal) (k : Int)
  | callMapfn (f thisArg v : JSVal) (k : Int)
  | define (a : JSVal) (k : Int) (v : JSVal)
  | setLength (a : JSVal) (n : Int)
  | getReturn (iterator : JSVal)
  | callReturn (f iterator : JSVal)
  | resolve (a : JSVal)
  | reject (e : JSVal)
  deriving DecidableEq, Repr

def Op.isSettle : Op → Bool
  | .resolve _ => true
  | .reject _ => true
  | _ => false

inductive Resp where
  | ok (v : JSVal)
  | err (e : JSVal)
  deriving DecidableEq, Repr

structure W where
  rs : List Resp
  tr : List Op

def W.emit (w : W) (o : Op) : W := ⟨w.rs, o :: w.tr⟩

def perform {β : Type} (o : Op) (w : W) (exh : W → β) (k : Resp → W → β) : β :=
  match w.rs with
  | [] => exh (w.emit o)
  | r :: rs => k r ⟨rs, o :: w.tr⟩

inductive Exit where
  | suspended
  | settled
  | idle
  | exhausted
  deriving DecidableEq, Repr

inductive Res (σ : Type) where
  | exit (x : Exit) (c : σ) (w : W)
  | thrown (e : JSVal) (c : σ) (w : W)

inductive Aw (σ : Type) where
  | registered (c : σ) (w : W)
  | thrown (e : JSVal) (c : σ) (w : W)
  | exhausted (c : σ) (w : W)

def Aw.toRes {σ : Type} : Aw σ → Res σ
  | .registered c w => .exit .suspended c w
  | .thrown e c w => .thrown e c w
  | .exhausted c w => .exit .exhausted c w

inductive CloseRes (σ : Type) where
  | normal (registered : Bool) (c : σ) (w : W)
  | rejectPromise (c : σ) (w : W)
  | exhausted (c : σ) (w : W)

def Aw.toClose {σ : Type} : Aw σ → CloseRes σ
  | .registered c w => .normal true c w
  | .thrown _ c w => .normal false c w
  | .exhausted c w => .exhausted c w

def promiseResolve (ctor v : JSVal) : JSVal :=
  if ctor = .promiseCtor then
    match v with
    | .promise p => .promise p
    | _ => .promise 1
  else .obj 0

def smiInc (smiMax : Nat) (n : Int) : Int := if n = smiMax then -(smiMax : Int) - 1 else n + 1

def numberOf (smiMax n : Nat) : JSVal := if n ≤ smiMax then .smi n else .heapNumber n

structure IterCtx where
  step : JSVal
  awaitedValue : JSVal
  index : JSVal
  promise : JSVal
  promiseFunction : JSVal
  onFulfilled : JSVal
  onRejected : JSVal
  resultArray : JSVal
  iterator : JSVal
  nextMethod : JSVal
  error : JSVal
  mapfn : JSVal
  thisArg : JSVal
  deriving DecidableEq, Repr

structure IterLocals where
  step : Option Label
  awaitedValue : JSVal
  index : Int
  mappedValue : JSVal
  nextValue : JSVal

def iterAwaitPoint (c : IterCtx) (l : Label) (v : JSVal) (w : W) : Outcome (Aw IterCtx) :=
  let c := { c with step := .smi l.code }
  chk .receiver c.promiseFunction fun pf =>
  chk .functionOrUndefined c.onFulfilled fun _ =>
  chk .functionOrUndefined c.onRejected fun _ =>
  perform (.await v) w (fun w => .ok (.exhausted c w)) fun r w =>
    match r with
    | .err e => .ok (.thrown e c w)
    | .ok _ => chk .promise (promiseResolve pf v) fun _ => .ok (.registered c w)

def iterClose (c : IterCtx) (it : JSVal) (w : W) : Outcome (CloseRes IterCtx) :=
  perform (.getReturn it) w (fun w => .ok (.exhausted c w)) fun r w =>
    match r with
    | .err _ => .ok (.normal false c w)
    | .ok m =>
      if m.isNullish then .ok (.rejectPromise c w)
      else if m.isCallable then
        perform (.callReturn m it) w (fun w => .ok (.exhausted c w)) fun r w =>
          match r with
          | .err _ => .ok (.normal false c w)
          | .ok ir => omap Aw.toClose (iterAwaitPoint c .rejectPromise ir w)
      else .ok (.normal false c w)

def iterLoop (smiMax : Nat) (mapfn thisArg arr : JSVal) :
    Nat → IterLocals → IterCtx → W → Outcome (Res IterCtx)
  | 0, _, _, _ => .fatal
  | fuel + 1, s, c, w =>
    match s.step with
    | some .getIteratorStep =>
      chk .receiver c.iterator fun it =>
      chk .any c.nextMethod fun nx =>
      if nx.isCallable then
        perform (.callNext nx it) w (fun w => .ok (.exit .exhausted c w)) fun r w =>
          match r with
          | .err e => .ok (.thrown e c w)
          | .ok v => omap Aw.toRes (iterAwaitPoint c .checkIteratorValueAndMapping v w)
      else .ok (.thrown .typeError c w)
    | some .checkIteratorValueAndMapping =>
      if s.awaitedValue.isReceiver then
        perform (.iteratorComplete s.awaitedValue) w (fun w => .ok (.exit .exhausted c w)) fun r w =>
          match r with
          | .err e => .ok (.thrown e c w)
          | .ok d =>
            if d.truthy then
              iterLoop smiMax mapfn thisArg arr fuel { s with step := some .doneAndResolvePromise } c w
            else
              perform (.iteratorValue s.awaitedValue) w (fun w => .ok (.exit .exhausted c w))
                fun r w =>
                  match r with
                  | .err e => .ok (.thrown e c w)
                  | .ok v =>
                    if mapfn = .undef then
                      iterLoop smiMax mapfn thisArg arr fuel { s with step := some .addIteratorValueToTheArray, nextValue := v, mappedValue := v } c w
                    else
                      iterLoop smiMax mapfn thisArg arr fuel { s with step := some .iteratorMapping, nextValue := v } c w
      else .ok (.thrown .typeError c w)
    | some .iteratorMapping =>
      chk .callable mapfn fun f =>
      perform (.callMapfn f thisArg s.nextValue s.index) w (fun w => .ok (.exit .exhausted c w))
        fun r w =>
          match r with
          | .err e => .ok (.thrown e c w)
          | .ok m => omap Aw.toRes (iterAwaitPoint c .getIteratorValueWithMapping m w)
    | some .getIteratorValueWithMapping =>
      iterLoop smiMax mapfn thisArg arr fuel { s with step := some .addIteratorValueToTheArray, mappedValue := s.awaitedValue } c w
    | some .addIteratorValueToTheArray =>
      perform (.define arr s.index s.mappedValue) w (fun w => .ok (.exit .exhausted c w)) fun r w =>
        match r with
        | .err e => .ok (.thrown e c w)
        | .ok _ =>
          iterLoop smiMax mapfn thisArg arr fuel { s with step := some .getIteratorStep, index := smiInc smiMax s.index } { c with index := .smi (smiInc smiMax s.index) } w
    | some .doneAndResolvePromise =>
      perform (.setLength arr s.index) w (fun w => .ok (.exit .exhausted c w)) fun r w =>
        match r with
        | .err e => .ok (.thrown e c w)
        | .ok _ => chk .promise c.promise fun _ => .ok (.exit .settled c (w.emit (.resolve arr)))
    | some .closeAsyncIterator =>
      chk .receiver c.iterator fun it =>
      chk .any c.nextMethod fun _ =>
      obind (iterClose c it w) fun
        | .normal reg c w => .ok (.exit (if reg then .suspended else .idle) c w)
        | .rejectPromise c w =>
          iterLoop smiMax mapfn thisArg arr fuel { s with step := some .rejectPromise } c w
        | .exhausted c w => .ok (.exit .exhausted c w)
    | some .rejectPromise =>
      chk .any c.error fun e =>
      chk .promise c.promise fun _ =>
      .ok (.exit .settled c (w.emit (.reject e)))
    | _ => iterLoop smiMax mapfn thisArg arr fuel s c w

def iterTry (smiMax : Nat) (c : IterCtx) (w : W) : Outcome (Res IterCtx) :=
  chk .any c.mapfn fun mapfn =>
  chk .any c.thisArg fun thisArg =>
  chk .receiver c.resultArray fun arr =>
  chk .smi c.step fun st =>
  chk .any c.awaitedValue fun av =>
  chk .smi c.index fun ix =>
  iterLoop smiMax mapfn thisArg arr 8 ⟨Label.decode st.num, av, ix.num, .undef, .undef⟩ c w

def iterRejectFromSlots (c : IterCtx) (w : W) : Outcome (Exit × IterCtx × W) :=
  chk .any c.error fun e =>
  chk .promise c.promise fun _ =>
  .ok (.settled, c, w.emit (.reject e))

def iterCatch (c : IterCtx) (e : JSVal) (w : W) : Outcome (Exit × IterCtx × W) :=
  let c := { c with error := e }
  chk .receiver c.iterator fun it =>
  chk .any c.nextMethod fun _ =>
  obind (iterClose c it w) fun
    | .normal reg c w => .ok (if reg then .suspended else .idle, c, w)
    | .rejectPromise c w => iterRejectFromSlots c w
    | .exhausted c w => .ok (.exhausted, c, w)

def iterBody (smiMax : Nat) (c : IterCtx) (w : W) : Outcome (Exit × IterCtx × W) :=
  obind (iterTry smiMax c w) fun
    | .exit x c w => .ok (x, c, w)
    | .thrown e c w => iterCatch c e w

def iterOnFulfilled (smiMax : Nat) (c : IterCtx) (v : JSVal) (w : W) :
    Outcome (Exit × IterCtx × W) :=
  iterBody smiMax { c with awaitedValue := v } w

def iterOnRejected (smiMax : Nat) (c : IterCtx) (v : JSVal) (w : W) :
    Outcome (Exit × IterCtx × W) :=
  iterBody smiMax { c with step := .smi Label.closeAsyncIterator.code, error := v } w

structure ALCtx where
  step : JSVal
  awaitedValue : JSVal
  len : JSVal
  index : JSVal
  promise : JSVal
  promiseFunction : JSVal
  onFulfilled : JSVal
  onRejected : JSVal
  resultArray : JSVal
  arrayLike : JSVal
  error : JSVal
  mapfn : JSVal
  thisArg : JSVal
  deriving DecidableEq, Repr

structure ALLocals where
  step : Option Label
  awaitedValue : JSVal
  len : JSVal
  index : Int

def alAwaitPoint (c : ALCtx) (l : Label) (v : JSVal) (w : W) : Outcome (Aw ALCtx) :=
  let c := { c with step := .smi l.code }
  chk .receiver c.promiseFunction fun pf =>
  chk .functionOrUndefined c.onFulfilled fun _ =>
  chk .functionOrUndefined c.onRejected fun _ =>
  perform (.await v) w (fun w => .ok (.exhausted c w)) fun r w =>
    match r with
    | .err e => .ok (.thrown e c w)
    | .ok _ => chk .promise (promiseResolve pf v) fun _ => .ok (.registered c w)

def alLoop (smiMax : Nat) (mapfn thisArg arr : JSVal) :
    Nat → ALLocals → ALCtx → W → Outcome (Res ALCtx)
  | 0, _, _, _ => .fatal
  | fuel + 1, s, c, w =>
    match s.step with
    | some .getArrayLikeValue =>
      chk .receiver c.arrayLike fun al =>
      if s.index < s.len.num then
        perform (.get al s.index) w (fun w => .ok (.exit .exhausted c w)) fun r w =>
          match r with
          | .err e => .ok (.thrown e c w)
          | .ok v => omap Aw.toRes (alAwaitPoint c .checkArrayLikeValueAndMapping v w)
      else alLoop smiMax mapfn thisArg arr fuel { s with step := some .doneAndResolvePromise } c w
    | some .checkArrayLikeValueAndMapping =>
      if mapfn = .undef then
        alLoop smiMax mapfn thisArg arr fuel { s with step := some .addArrayLikeValueToTheArray } c w
      else
        alLoop smiMax mapfn thisArg arr fuel { s with step := some .getArrayLikeValueWithMapping } c w
    | some .getArrayLikeValueWithMapping =>
      chk .callable mapfn fun f =>
      perform (.callMapfn f thisArg s.awaitedValue s.index) w (fun w => .ok (.exit .exhausted c w))
        fun r w =>
          match r with
          | .err e => .ok (.thrown e c w)
          | .ok m => omap Aw.toRes (alAwaitPoint c .addArrayLikeValueToTheArray m w)
    | some .addArrayLikeValueToTheArray =>
      perform (.define arr s.index s.awaitedValue) w (fun w => .ok (.exit .exhausted c w)) fun r w =>
        match r with
        | .err e => .ok (.thrown e c w)
        | .ok _ =>
          alLoop smiMax mapfn thisArg arr fuel { s with step := some .getArrayLikeValue, index := smiInc smiMax s.index } { c with index := .smi (smiInc smiMax s.index) } w
    | some .doneAndResolvePromise =>
      perform (.setLength arr s.index) w (fun w => .ok (.exit .exhausted c w)) fun r w =>
        match r with
        | .err e => .ok (.thrown e c w)
        | .ok _ => chk .promise c.promise fun _ => .ok (.exit .settled c (w.emit (.resolve arr)))
    | some .rejectPromise =>
      chk .any c.error fun e =>
      chk .promise c.promise fun _ =>
      .ok (.exit .settled c (w.emit (.reject e)))
    | _ => alLoop smiMax mapfn thisArg arr fuel s c w

def alTry (smiMax : Nat) (c : ALCtx) (w : W) : Outcome (Res ALCtx) :=
  chk .any c.mapfn fun mapfn =>
  chk .any c.thisArg fun thisArg =>
  chk .receiver c.resultArray fun arr =>
  chk .smi c.step fun st =>
  chk .any c.awaitedValue fun av =>
  chk .number c.len fun len =>
  chk .smi c.index fun ix =>
  alLoop smiMax mapfn thisArg arr 8 ⟨Label.decode st.num, av, len, ix.num⟩ c w

def alCatch (c : ALCtx) (e : JSVal) (w : W) : Outcome (Exit × ALCtx × W) :=
  let c := { c with error := e }
  chk .any c.error fun e =>
  chk .promise c.promise fun _ =>
  .ok (.settled, c, w.emit (.reject e))

def alBody (smiMax : Nat) (c : ALCtx) (w : W) : Outcome (Exit × ALCtx × W) :=
  obind (alTry smiMax c w) fun
    | .exit x c w => .ok (x, c, w)
    | .thrown e c w => alCatch c e w

def alOnFulfilled (smiMax : Nat) (c : ALCtx) (v : JSVal) (w : W) : Outcome (Exit × ALCtx × W) :=
  alBody smiMax { c with awaitedValue := v } w

def alOnRejected (smiMax : Nat) (c : ALCtx) (v : JSVal) (w : W) : Outcome (Exit × ALCtx × W) :=
  alBody smiMax { c with step := .smi Label.rejectPromise.code, error := v } w

inductive Ctx where
  | iter (c : IterCtx)
  | arrayLike (c : ALCtx)
  deriving Repr

inductive Event where
  | fulfil (v : JSVal)
  | reject (v : JSVal)
  deriving DecidableEq, Repr

def Event.ofResp : Resp → Event
  | .ok v => .fulfil v
  | .err e => .reject e

def liftIter (r : Exit × IterCtx × W) : Exit × Ctx × W := (r.1, .iter r.2.1, r.2.2)

def liftAL (r : Exit × ALCtx × W) : Exit × Ctx × W := (r.1, .arrayLike r.2.1, r.2.2)

def react (smiMax : Nat) : Ctx → Event → W → Outcome (Exit × Ctx × W)
  | .iter c, .fulfil v, w => omap liftIter (iterOnFulfilled smiMax c v w)
  | .iter c, .reject v, w => omap liftIter (iterOnRejected smiMax c v w)
  | .arrayLike c, .fulfil v, w => omap liftAL (alOnFulfilled smiMax c v w)
  | .arrayLike c, .reject v, w => omap liftAL (alOnRejected smiMax c v w)

structure Input where
  receiver : JSVal
  items : JSVal
  mapfn : JSVal
  thisArg : JSVal
  deriving DecidableEq, Repr

inductive Start where
  | withCtx (x : Exit) (c : Ctx) (w : W)
  | noCtx (x : Exit) (w : W)

def initIterCtx (inp : Input) (it nx arr : JSVal) : IterCtx :=
  ⟨.smi Label.getIteratorStep.code, .undef, .smi 0, .promise 0, .promiseCtor, .reaction true,
    .reaction false, arr, it, nx, .undef, inp.mapfn, inp.thisArg⟩

def initALCtx (smiMax : Nat) (inp : Input) (al : JSVal) (len : Nat) (arr : JSVal) : ALCtx :=
  ⟨.smi Label.getArrayLikeValue.code, .undef, numberOf smiMax len, .smi 0, .promise 0, .promiseCtor,
    .reaction true, .reaction false, arr, al, .undef, inp.mapfn, inp.thisArg⟩

def startIter (smiMax : Nat) (inp : Input) (it nx arr : JSVal) (w : W) : Outcome Start :=
  omap (fun r => .withCtx r.1 (.iter r.2.1) r.2.2) (iterBody smiMax (initIterCtx inp it nx arr) w)

def startAL (smiMax : Nat) (inp : Input) (al : JSVal) (len : Nat) (arr : JSVal) (w : W) :
    Outcome Start :=
  omap (fun r => .withCtx r.1 (.arrayLike r.2.1) r.2.2) (alBody smiMax (initALCtx smiMax inp al len arr) w)

def startReject (e : JSVal) (w : W) : Outcome Start := .ok (.noCtx .settled (w.emit (.reject e)))

def startExh (w : W) : Outcome Start := .ok (.noCtx .exhausted w)

def createArray (c : JSVal) (len : Option Nat) (w : W) (k : JSVal → W → Outcome Start) :
    Outcome Start :=
  if c.isConstructor then
    perform (.construct c len) w startExh fun r w =>
      match r with
      | .err e => startReject e w
      | .ok a => k a.toReceiver w
  else
    perform (.arrayCreate (len.getD 0)) w startExh fun r w =>
      match r with
      | .err e => startReject e w
      | .ok a => k a.toReceiver w

def getIterator (items method : JSVal) (w : W) (k : JSVal → JSVal → W → Outcome Start) :
    Outcome Start :=
  perform (.callIteratorMethod method items) w startExh fun r w =>
    match r with
    | .err e => startReject e w
    | .ok it =>
      if it.isReceiver then
        perform (.getNextMethod it) w startExh fun r w =>
          match r with
          | .err e => startReject e w
          | .ok nx => k it nx w
      else startReject .typeError w

def arrayFromAsync (smiMax : Nat) (inp : Input) (w : W) : Outcome Start :=
  if inp.mapfn ≠ .undef ∧ inp.mapfn.isCallable = false then startReject .typeError w
  else
    perform (.getAsyncIteratorMethod inp.items) w startExh fun r w =>
      match r with
      | .err e => startReject e w
      | .ok m =>
        if m.isNullish then
          perform (.getIteratorMethod inp.items) w startExh fun r w =>
            match r with
            | .err e => startReject e w
            | .ok m' =>
              if m'.isNullish then
                perform (.getLength inp.items.toReceiver) w startExh fun r w =>
                  match r with
                  | .err e => startReject e w
                  | .ok lv =>
                    createArray inp.receiver (some lv.lengthOf) w fun arr w =>
                      startAL smiMax inp inp.items.toReceiver lv.lengthOf arr w
              else if m'.isCallable then
                getIterator inp.items m' w fun it _ w =>
                  perform (.getNextMethod it) w startExh fun r w =>
                    match r with
                    | .err e => startReject e w
                    | .ok _ =>
                      createArray inp.receiver none w fun arr w =>
                        startIter smiMax inp .asyncFromSyncIterator .asyncFromSyncNext arr w
              else startReject .typeError w
        else if m.isCallable then
          getIterator inp.items m w fun it nx w =>
            createArray inp.receiver none w fun arr w => startIter smiMax inp it nx arr w
        else startReject .typeError w

inductive End where
  | settled
  | pending
  | idle
  | exhausted
  | outOfFuel
  deriving DecidableEq, Repr

def Exit.toEnd : Exit → End
  | .suspended => .pending
  | .settled => .settled
  | .idle => .idle
  | .exhausted => .exhausted

def drive (smiMax : Nat) : Nat → Ctx → W → Outcome (End × W)
  | 0, _, w => .ok (.outOfFuel, w)
  | n + 1, c, w =>
    match w.rs with
    | [] => .ok (.pending, w)
    | r :: rs =>
      obind (react smiMax c (Event.ofResp r) ⟨rs, w.tr⟩) fun res =>
        match res.1 with
        | .suspended => drive smiMax n res.2.1 res.2.2
        | x => .ok (x.toEnd, res.2.2)

def run (smiMax fuel : Nat) (inp : Input) (rs : List Resp) : Outcome (List Op × End) :=
  obind (arrayFromAsync smiMax inp ⟨rs, []⟩) fun
    | .withCtx .suspended c w => omap (fun r => (r.2.tr.reverse, r.1)) (drive smiMax fuel c w)
    | .withCtx x _ w => .ok (w.tr.reverse, x.toEnd)
    | .noCtx x w => .ok (w.tr.reverse, x.toEnd)

def reactAll (smiMax : Nat) : Ctx → List Event → W → Outcome (Ctx × W)
  | c, [], w => .ok (c, w)
  | c, e :: es, w => obind (react smiMax c e w) fun res => reactAll smiMax res.2.1 es res.2.2

def runEvents (smiMax : Nat) (inp : Input) (evs : List Event) (rs : List Resp) :
    Outcome (List Op) :=
  obind (arrayFromAsync smiMax inp ⟨rs, []⟩) fun
    | .withCtx _ c w => omap (fun r => r.2.tr.reverse) (reactAll smiMax c evs w)
    | .noCtx _ w => .ok w.tr.reverse

end ArrayFromAsync
