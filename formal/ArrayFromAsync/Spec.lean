import ArrayFromAsync.Model

namespace ArrayFromAsync

open Torque

structure IterRec where
  A : JSVal
  iterator : JSVal
  next : JSVal
  mapfn : JSVal
  thisArg : JSVal
  deriving DecidableEq, Repr

structure ALRec where
  A : JSVal
  arrayLike : JSVal
  len : Nat
  mapfn : JSVal
  thisArg : JSVal
  deriving DecidableEq, Repr

inductive Susp where
  | iterNext (E : IterRec) (k : Nat)
  | iterMapped (E : IterRec) (k : Nat)
  | iterClose (E : IterRec) (e : JSVal)
  | alValue (E : ALRec) (k : Nat)
  | alMapped (E : ALRec) (k : Nat)
  deriving DecidableEq, Repr

inductive Out where
  | susp (s : Susp)
  | stop (x : Exit)

inductive Dev where
  | closesIterator
  | closeAbrupt
  | closeRejected
  | indexOverflow
  | nextReadTwice
  deriving DecidableEq, Repr

structure SRes where
  out : Out
  w : W
  devs : List Dev

def SRes.dev (d : Dev) (r : SRes) : SRes := ⟨r.out, r.w, d :: r.devs⟩

def sReject (e : JSVal) (w : W) : SRes := ⟨.stop .settled, w.emit (.reject e), []⟩

def sResolve (a : JSVal) (w : W) : SRes := ⟨.stop .settled, w.emit (.resolve a), []⟩

def sExh (w : W) : SRes := ⟨.stop .exhausted, w, []⟩

def sSusp (s : Susp) (w : W) : SRes := ⟨.susp s, w, []⟩

def asyncIteratorClose (E : IterRec) (e : JSVal) (w : W) : SRes :=
  perform (.getReturn E.iterator) w sExh fun r w =>
    match r with
    | .err _ => (sReject e w).dev .closeAbrupt
    | .ok m =>
      if m.isNullish then sReject e w
      else if m.isCallable then
        perform (.callReturn m E.iterator) w sExh fun r w =>
          match r with
          | .err _ => (sReject e w).dev .closeAbrupt
          | .ok ir =>
            perform (.await ir) w sExh fun r w =>
              match r with
              | .err _ => (sReject e w).dev .closeAbrupt
              | .ok _ => sSusp (.iterClose E e) w
      else (sReject e w).dev .closeAbrupt

def iterHead (E : IterRec) (k : Nat) (w : W) : SRes :=
  if 2 ^ 53 - 1 ≤ k then asyncIteratorClose E .typeError w
  else if E.next.isCallable then
    perform (.callNext E.next E.iterator) w sExh fun r w =>
      match r with
      | .err e => (sReject e w).dev .closesIterator
      | .ok v =>
        perform (.await v) w sExh fun r w =>
          match r with
          | .err e => (sReject e w).dev .closesIterator
          | .ok _ => sSusp (.iterNext E k) w
  else (sReject .typeError w).dev .closesIterator

def iterDefine (smiMax : Nat) (E : IterRec) (k : Nat) (v : JSVal) (w : W) : SRes :=
  perform (.define E.A k v) w sExh fun r w =>
    match r with
    | .err e => asyncIteratorClose E e w
    | .ok _ =>
      if k = smiMax then (iterHead E (k + 1) w).dev .indexOverflow else iterHead E (k + 1) w

def iterAfterNext (smiMax : Nat) (E : IterRec) (k : Nat) (v : JSVal) (w : W) : SRes :=
  if v.isReceiver then
    perform (.iteratorComplete v) w sExh fun r w =>
      match r with
      | .err e => (sReject e w).dev .closesIterator
      | .ok d =>
        if d.truthy then
          perform (.setLength E.A k) w sExh fun r w =>
            match r with
            | .err e => (sReject e w).dev .closesIterator
            | .ok _ => sResolve E.A w
        else
          perform (.iteratorValue v) w sExh fun r w =>
            match r with
            | .err e => (sReject e w).dev .closesIterator
            | .ok x =>
              if E.mapfn = .undef then iterDefine smiMax E k x w
              else
                perform (.callMapfn E.mapfn E.thisArg x k) w sExh fun r w =>
                  match r with
                  | .err e => asyncIteratorClose E e w
                  | .ok m =>
                    perform (.await m) w sExh fun r w =>
                      match r with
                      | .err e => asyncIteratorClose E e w
                      | .ok _ => sSusp (.iterMapped E k) w
  else (sReject .typeError w).dev .closesIterator

def alHead (E : ALRec) (k : Nat) (w : W) : SRes :=
  if k < E.len then
    perform (.get E.arrayLike k) w sExh fun r w =>
      match r with
      | .err e => sReject e w
      | .ok v =>
        perform (.await v) w sExh fun r w =>
          match r with
          | .err e => sReject e w
          | .ok _ => sSusp (.alValue E k) w
  else
    perform (.setLength E.A E.len) w sExh fun r w =>
      match r with
      | .err e => sReject e w
      | .ok _ => sResolve E.A w

def alDefine (smiMax : Nat) (E : ALRec) (k : Nat) (v : JSVal) (w : W) : SRes :=
  perform (.define E.A k v) w sExh fun r w =>
    match r with
    | .err e => sReject e w
    | .ok _ => if k = smiMax then (alHead E (k + 1) w).dev .indexOverflow else alHead E (k + 1) w

def alAfterValue (smiMax : Nat) (E : ALRec) (k : Nat) (v : JSVal) (w : W) : SRes :=
  if E.mapfn = .undef then alDefine smiMax E k v w
  else
    perform (.callMapfn E.mapfn E.thisArg v k) w sExh fun r w =>
      match r with
      | .err e => sReject e w
      | .ok m =>
        perform (.await m) w sExh fun r w =>
          match r with
          | .err e => sReject e w
          | .ok _ => sSusp (.alMapped E k) w

def resume (smiMax : Nat) : Susp → Resp → W → SRes
  | .iterNext E k, .ok v, w => iterAfterNext smiMax E k v w
  | .iterNext _ _, .err e, w => (sReject e w).dev .closesIterator
  | .iterMapped E k, .ok m, w => iterDefine smiMax E k m w
  | .iterMapped E _, .err e, w => asyncIteratorClose E e w
  | .iterClose _ e, .ok _, w => sReject e w
  | .iterClose _ e, .err _, w => (sReject e w).dev .closeRejected
  | .alValue E k, .ok v, w => alAfterValue smiMax E k v w
  | .alValue _ _, .err e, w => sReject e w
  | .alMapped E k, .ok m, w => alDefine smiMax E k m w
  | .alMapped _ _, .err e, w => sReject e w

def getIteratorFromMethod (obj method : JSVal) (w : W) (k : JSVal → JSVal → W → SRes) : SRes :=
  perform (.callIteratorMethod method obj) w sExh fun r w =>
    match r with
    | .err e => sReject e w
    | .ok it =>
      if it.isReceiver then
        perform (.getNextMethod it) w sExh fun r w =>
          match r with
          | .err e => sReject e w
          | .ok nx => k it nx w
      else sReject .typeError w

def iterableBranch (inp : Input) (it nx : JSVal) (w : W) : SRes :=
  if inp.receiver.isConstructor then
    perform (.construct inp.receiver none) w sExh fun r w =>
      match r with
      | .err e => sReject e w
      | .ok a => iterHead ⟨a.toReceiver, it, nx, inp.mapfn, inp.thisArg⟩ 0 w
  else
    perform (.arrayCreate 0) w sExh fun r w =>
      match r with
      | .err e => sReject e w
      | .ok a => iterHead ⟨a.toReceiver, it, nx, inp.mapfn, inp.thisArg⟩ 0 w

def arrayLikeBranch (inp : Input) (w : W) : SRes :=
  perform (.getLength inp.items.toReceiver) w sExh fun r w =>
    match r with
    | .err e => sReject e w
    | .ok lv =>
      if inp.receiver.isConstructor then
        perform (.construct inp.receiver (some lv.lengthOf)) w sExh fun r w =>
          match r with
          | .err e => sReject e w
          | .ok a =>
            alHead ⟨a.toReceiver, inp.items.toReceiver, lv.lengthOf, inp.mapfn, inp.thisArg⟩ 0 w
      else
        perform (.arrayCreate lv.lengthOf) w sExh fun r w =>
          match r with
          | .err e => sReject e w
          | .ok a =>
            alHead ⟨a.toReceiver, inp.items.toReceiver, lv.lengthOf, inp.mapfn, inp.thisArg⟩ 0 w

def fromAsync (inp : Input) (w : W) : SRes :=
  if inp.mapfn ≠ .undef ∧ inp.mapfn.isCallable = false then sReject .typeError w
  else
    perform (.getAsyncIteratorMethod inp.items) w sExh fun r w =>
      match r with
      | .err e => sReject e w
      | .ok m =>
        if m.isNullish then
          perform (.getIteratorMethod inp.items) w sExh fun r w =>
            match r with
            | .err e => sReject e w
            | .ok m' =>
              if m'.isNullish then arrayLikeBranch inp w
              else if m'.isCallable then
                getIteratorFromMethod inp.items m' w fun _ _ w =>
                  (iterableBranch inp .asyncFromSyncIterator .asyncFromSyncNext w).dev .nextReadTwice
              else sReject .typeError w
        else if m.isCallable then
          getIteratorFromMethod inp.items m w fun it nx w => iterableBranch inp it nx w
        else sReject .typeError w

def specDrive (smiMax : Nat) : Nat → Susp → W → End × W × List Dev
  | 0, _, w => (.outOfFuel, w, [])
  | n + 1, s, w =>
    match w.rs with
    | [] => (.pending, w, [])
    | r :: rs =>
      let res := resume smiMax s r ⟨rs, w.tr⟩
      match res.out with
      | .susp s' =>
        let t := specDrive smiMax n s' res.w
        (t.1, t.2.1, res.devs ++ t.2.2)
      | .stop x => (x.toEnd, res.w, res.devs)

def specRun (smiMax fuel : Nat) (inp : Input) (rs : List Resp) : List Op × End × List Dev :=
  let res := fromAsync inp ⟨rs, []⟩
  match res.out with
  | .susp s =>
    let t := specDrive smiMax fuel s res.w
    (t.2.1.tr.reverse, t.1, res.devs ++ t.2.2)
  | .stop x => (res.w.tr.reverse, x.toEnd, res.devs)

end ArrayFromAsync
