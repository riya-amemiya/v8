import Torque

namespace ArrayCopyCommon

open Torque

structure Limits where
  maxLen : Nat
  maxFast : Nat

inductive Result (σ : Type) where
  | done (src : σ) (res : JSArr)
  | slow
  | throws
  | ub
  | abort
  deriving Repr

def Result.mapSrc {σ τ : Type} (f : σ → τ) : Result σ → Result τ
  | .done s r => .done (f s) r
  | .slow => .slow
  | .throws => .throws
  | .ub => .ub
  | .abort => .abort

inductive Run where
  | ok (buf : List (Option Val))
  | ub
  | abort
  deriving Repr

def holeToUndef : Option Val → Val
  | some v => v
  | none => .undef

def getOrUndef (xs : List (Option Val)) (i : Nat) : Val := holeToUndef (xs.getD i none)

def isFastPacked : Kind → Bool
  | .packedSmi => true
  | .packedDouble => true
  | .packedElem => true
  | _ => false

def newArray (k : Kind) (store : List (Option Val)) : JSArr :=
  ⟨k, true, true, true, false, store.length, store⟩

def relIndex (len : Nat) (rel : Int) : Nat :=
  if rel < 0 then (if (len : Int) + rel < 0 then 0 else ((len : Int) + rel).toNat)
  else min rel.toNat len

def copyElements (dst : List (Option Val)) (di : Nat) (src : List (Option Val)) (si n : Nat) :
    Option (List (Option Val)) :=
  if di + n ≤ dst.length ∧ si + n ≤ src.length then some (blit dst di ((src.drop si).take n))
  else none

def storeChecked (buf : List (Option Val)) (i : Nat) (v : Val) : Option (List (Option Val)) :=
  if i < buf.length then some (buf.set i (some v)) else none

def extractFast (lim : Limits) (a : JSArr) (begin count : Nat) : Result JSArr :=
  if a.fast = false then .ub
  else if count = 0 then .done a (newArray a.kind [])
  else if lim.maxLen < count then .abort
  else match copyElements (List.replicate count none) 0 a.store begin count with
    | some s => .done a (newArray a.kind s)
    | none => .ub

def specSlice (xs : List (Option Val)) (k n : Nat) : List (Option Val) :=
  (List.range n).map fun i => xs.getD (k + i) none

end ArrayCopyCommon
