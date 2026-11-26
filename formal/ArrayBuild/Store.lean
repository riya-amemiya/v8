import Torque

namespace ArrayBuild

open Torque

inductive StoreResult where
  | done (a : JSArr)
  | slow (a : JSArr)
  | ub
  | fatal
  deriving Repr

structure AppendEnv where
  maxNewSpace : Nat
  undefinedDouble : Bool

structure StoreEnv where
  append : AppendEnv
  pushable : Bool

def newCapacity (n : Nat) : Nat := n + n / 2 + 16

def valueFits (ud : Bool) : Kind → Val → Bool
  | .packedSmi, v => v.isSmi
  | .holeySmi, v => v.isSmi
  | .packedDouble, v => v.isNumber
  | .holeyDouble, v => v.isNumber || (ud && v == .undef)
  | _, _ => true

def growIfNeeded (env : AppendEnv) (a : JSArr) : Option JSArr :=
  if a.store.length < a.length + 1 then
    if env.maxNewSpace ≤ newCapacity (a.length + 1) then none
    else some { a with cow := false, store := growTo a.store (newCapacity (a.length + 1)) }
  else some a

def storeChecked (b : JSArr) (i : Nat) (v : Val) : StoreResult :=
  if b.cow = true then .ub
  else if i < b.store.length then .done { b with store := b.store.set i (some v) }
  else .fatal

def storeUnchecked (b : JSArr) (i : Nat) (v : Val) : StoreResult :=
  if b.cow = true then .ub
  else if i < b.store.length then .done { b with store := b.store.set i (some v) }
  else .ub

def appendElem (env : AppendEnv) (k : Kind) (a : JSArr) (v : Val) : StoreResult :=
  match growIfNeeded env a with
  | none => .slow a
  | some a1 =>
    if valueFits env.undefinedDouble k v = false then .slow a1
    else
      match (if k = .holeyDouble ∧ v = .undef then storeUnchecked a1 a1.length v
          else storeChecked a1 a1.length v) with
      | .done a2 => .done { a2 with length := a2.length + 1 }
      | r => r

def appendKind : Kind → Kind
  | .packedSmi => .holeySmi
  | .holeySmi => .holeySmi
  | .packedDouble => .packedDouble
  | .holeyDouble => .holeyDouble
  | _ => .holeyElem

def overwrite (env : StoreEnv) (b : JSArr) (index : Nat) (v : Val) : StoreResult :=
  if b.kind = .packedSmi ∨ b.kind = .holeySmi then
    if v.isSmi then storeChecked b index v else .slow b
  else if b.kind.isDouble then
    if env.append.undefinedDouble = true ∧ b.kind = .holeyDouble then
      if v.isNumber then storeChecked b index v
      else if v = .undef then storeUnchecked b index v
      else .slow b
    else if v.isNumber then storeChecked b index v
    else .slow b
  else storeChecked b index v

def fastCreateDataProperty (env : StoreEnv) (a : JSArr) (index : Nat) (v : Val) : StoreResult :=
  if a.fast = false then .slow a
  else if a.length < index then .slow a
  else if index = a.length then
    if env.pushable = false then .slow a
    else appendElem env.append (appendKind a.kind) (ensureWritable a) v
  else overwrite env (ensureWritable a) index v

def setElem (xs : List (Option Val)) (i : Nat) (v : Val) : List (Option Val) :=
  if i < xs.length then xs.set i (some v) else xs ++ [some v]

structure CreatesData (a : JSArr) (i : Nat) (v : Val) (a' : JSArr) : Prop where
  wf : a'.WF
  slack : a'.SlackHoles
  elems : a'.elems = setElem a.elems i v
  length : a'.length = max a.length (i + 1)

end ArrayBuild
