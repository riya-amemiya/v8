import Torque

namespace InPlace

open Torque

inductive Result (ρ : Type) where
  | done (a : JSArr) (r : ρ)
  | slow
  | throws
  | ub
  | abort
  deriving Repr

inductive Res (α : Type) where
  | ok (x : α)
  | ub
  | abort
  deriving Repr

def Res.bind {α β : Type} : Res α → (α → Res β) → Res β
  | .ok x, f => f x
  | .ub, _ => .ub
  | .abort, _ => .abort

instance : Monad Res where
  pure := .ok
  bind := Res.bind

def Res.then {α ρ : Type} (m : Res α) (f : α → Result ρ) : Result ρ :=
  match m with
  | .ok x => f x
  | .ub => .ub
  | .abort => .abort

structure MapInfo where
  extensible : Bool
  prototypeMap : Bool
  dictionaryMap : Bool
  lengthReadOnly : Bool

def MapInfo.lengthWritable (m : MapInfo) : Bool := !m.dictionaryMap && !m.lengthReadOnly

def MapInfo.pushable (m : MapInfo) : Bool := m.extensible && !m.prototypeMap && m.lengthWritable

def loadSlot (s : List (Option Val)) (i : Int) : Res (Option Val) :=
  if 0 ≤ i ∧ i < s.length then .ok (s.getD i.toNat none) else .abort

def storeSlot (cow : Bool) (s : List (Option Val)) (i : Int) (x : Option Val) :
    Res (List (Option Val)) :=
  if 0 ≤ i ∧ i < s.length then (if cow then .ub else .ok (s.set i.toNat x)) else .abort

def memmove (cow : Bool) (s : List (Option Val)) (dst src n : Nat) : Res (List (Option Val)) :=
  if cow then .ub
  else if dst + n ≤ s.length ∧ src + n ≤ s.length then .ok (moveElements s dst src n)
  else .ub

def memcpy (d : List (Option Val)) (dst : Nat) (s : List (Option Val)) (src n : Nat) :
    Res (List (Option Val)) :=
  if dst + n ≤ d.length ∧ src + n ≤ s.length then .ok (blit d dst ((s.drop src).take n))
  else .ub

def castElements (k : Kind) (s : List (Option Val)) : Res Unit :=
  if k.isDouble ∧ s = [] then .abort else .ok ()

def ensureWritableChecked (c : Config) (a : JSArr) : Res JSArr :=
  if a.cow then
    if c.smiMax < a.length ∨ a.store.length < a.length ∨ c.maxLen < a.length then .abort
    else .ok (ensureWritable a)
  else .ok a

def transitionTo (c : Config) (a : JSArr) (k : Kind) : Res JSArr :=
  let d := a.kind.transitionTarget k
  if a.kind = d then .ok a
  else if a.store = [] then .ok { a with kind := d, cow := false }
  else if a.kind.isDouble = d.isDouble then .ok { a with kind := d }
  else if c.maxLen < a.store.length then .abort
  else .ok { a with kind := d, cow := false }

def newArray (k : Kind) (s : List (Option Val)) : JSArr :=
  ⟨k, true, true, true, false, s.length, s⟩

end InPlace
