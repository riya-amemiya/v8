import ArrayJoin.Buffer

namespace ArrayJoin

open Torque

inductive Elem where
  | empty
  | val (v : Val)
  deriving DecidableEq, Repr

inductive Loader where
  | fastObj
  | fastDouble
  | generic
  deriving DecidableEq, Repr

structure Env (σ : Type) where
  arr : σ → JSArr
  protector : σ → Bool
  get : Nat → σ → Option (Val × σ)
  conv : Elem → σ → Option (Option Str × σ)

def cannotUseSame {σ : Type} (env : Env σ) (ld : Loader) (kind0 : Kind) (len : Nat) (w : σ) :
    Bool :=
  match ld with
  | .generic => false
  | _ => (env.arr w).kind != kind0 || (env.arr w).length != len || !env.protector w

def loadFast (ld : Loader) (a : JSArr) (k : Nat) : Res Elem :=
  match a.store[k]? with
  | none => .fatal
  | some none => .ok .empty
  | some (some v) =>
    match ld with
    | .fastDouble => if v = .undef ∨ v.isNumber then .ok (.val v) else .ub
    | _ => .ok (.val v)

def load {σ : Type} (env : Env σ) (ld : Loader) (k : Nat) (w : σ) : Res (Elem × σ) :=
  match ld with
  | .generic =>
    match env.get k w with
    | some (v, w') => .ok (.val v, w')
    | none => .throws
  | _ => (loadFast ld (env.arr w) k).bind fun e => .ok (e, w)

def implLoop {σ : Type} (l : Limits) (env : Env σ) (kind0 : Kind) (sep : Str) (len : Nat)
    (k : Nat) (ld : Loader) (b : Buf) (nof : Nat) (w : σ) (log : List (List Nat)) :
    Res (Buf × Nat × σ × List (List Nat)) :=
  if _h : k < len then
    (load env (if cannotUseSame env ld kind0 len w then .generic else ld) k w).bind fun p =>
      match env.conv p.1 p.2 with
      | none => .throws
      | some (none, w2) =>
        implLoop l env kind0 sep len (k + 1) (if cannotUseSame env ld kind0 len w then .generic else ld)
          b (if 0 < k then nof + 1 else nof) w2 (log ++ [[]])
      | some (some s, w2) =>
        if s.chars = [] then
          implLoop l env kind0 sep len (k + 1)
            (if cannotUseSame env ld kind0 len w then .generic else ld) b
            (if 0 < k then nof + 1 else nof) w2 (log ++ [[]])
        else
          (add l b s (if 0 < k then nof + 1 else nof) sep.len).bind fun b' =>
            implLoop l env kind0 sep len (k + 1)
              (if cannotUseSame env ld kind0 len w then .generic else ld) b' 0 w2 (log ++ [s.chars])
  else .ok (b, nof, w, log)
termination_by len - k

def implJoin {σ : Type} (l : Limits) (env : Env σ) (kind0 : Kind) (ld0 : Loader) (sep : Str)
    (len : Nat) (w : σ) : Res (List Nat × σ × List (List Nat)) :=
  (implLoop l env kind0 sep len 0 ld0 (newBuffer l len) 0 w []).bind fun r =>
    (addSeparators l r.1 r.2.1 sep.len true).bind fun b =>
      (bufferJoin b sep).bind fun s => .ok (s, r.2.2.1, r.2.2.2)

inductive Sel where
  | loader (ld : Loader)
  | emptyDict
  deriving DecidableEq, Repr

def select (a : JSArr) (isArray : Bool) (len : Nat) (protoOk protector dictEmpty : Bool) : Sel :=
  if isArray = true ∧ a.length = len ∧ protoOk = true ∧ protector = true then
    match a.kind with
    | .packedSmi => .loader .fastObj
    | .holeySmi => .loader .fastObj
    | .packedElem => .loader .fastObj
    | .holeyElem => .loader .fastObj
    | .packedDouble => .loader .fastDouble
    | .holeyDouble => .loader .fastDouble
    | .slow => if dictEmpty then .emptyDict else .loader .generic
  else .loader .generic

structure Receiver (σ : Type) where
  isArray : σ → Bool
  protoOk : σ → Bool
  dictEmpty : σ → Bool

def arrayJoin {σ : Type} (l : Limits) (env : Env σ) (rc : Receiver σ) (sep : Str) (len : Nat)
    (w : σ) : Res (List Nat × σ × List (List Nat)) :=
  match select (env.arr w) (rc.isArray w) len (rc.protoOk w) (env.protector w) (rc.dictEmpty w) with
  | .emptyDict =>
    if sep.chars = [] then .ok ([], w, List.replicate len [])
    else if len - 1 ≤ l.smiMax then .ok (sepRun sep.chars (len - 1), w, List.replicate len [])
    else .throws
  | .loader ld => implJoin l env (env.arr w).kind ld sep len w

def earlyThrow (l : Limits) (sep : Str) (len : Nat) : Bool :=
  decide (1 ≤ sep.len ∧ (l.smiMax < len ∨ (1 < len ∧ l.strMax < (len - 1) * sep.len)))

end ArrayJoin
