import ArrayWitness

namespace ArrayFilter

open Torque ArrayWitness

structure FilterConfig where
  smiMax : Nat
  undefinedDouble : Bool
  growLimit : Kind → Nat

abbrev Callback := Nat → Val → JSArr → Post Bool

structure Stored where
  arr : JSArr
  sameMap : Bool

abbrev SlowStore := JSArr → Nat → Val → Stored

def pushKind (ud : Bool) : Kind → Kind
  | .packedSmi => .holeySmi
  | .holeySmi => .holeySmi
  | .packedDouble => .packedDouble
  | .holeyDouble => if ud then .holeyDouble else .packedDouble
  | _ => .holeyElem

def accepts (ud : Bool) (u : Val) (pk : Kind) (v : Val) : Bool :=
  match pk with
  | .packedSmi => v.isSmi
  | .holeySmi => v.isSmi
  | .packedDouble => v.isNumber
  | .holeyDouble => (ud && v == u) || v.isNumber
  | _ => true

def newCapacity (n : Nat) : Nat := n / 2 + n + 16

def grown (store : List (Option Val)) (cap : Nat) : List (Option Val) :=
  store ++ List.replicate (cap - store.length) none

inductive Append where
  | ok (a : JSArr)
  | failed (a : JSArr)
  | fatal
  | ub

def capacityFor (c : FilterConfig) (pk : Kind) (a : JSArr) : Option JSArr :=
  if a.length + 1 ≤ a.store.length then some a
  else if c.growLimit pk ≤ newCapacity (a.length + 1) then none
  else some { a with store := grown a.store (newCapacity (a.length + 1)) }

def append (c : FilterConfig) (u : Val) (pk : Kind) (a : JSArr) (v : Val) : Append :=
  if pk.isDouble ≠ a.kind.isDouble ∨ a.cow = true then .ub
  else
    match capacityFor c pk a with
    | none => .failed a
    | some b =>
      if accepts c.undefinedDouble u pk v = false then .failed b
      else if b.length < b.store.length then
        .ok { b with store := b.store.set b.length (some v), length := b.length + 1 }
      else if pk.isDouble && v == u then .ub
      else .fatal

structure Out where
  arr : JSArr
  to : Nat
  same : Bool

def slowStore (slow : SlowStore) (a : JSArr) (to : Nat) (v : Val) : Out :=
  let r := slow a to v
  ⟨r.arr, to + 1, r.sameMap⟩

inductive Store where
  | ok (o : Out)
  | fatal
  | ub

def store (c : FilterConfig) (u : Val) (K : Kind) (slow : SlowStore) (o : Out) (v : Val)
    (protector : Bool) : Store :=
  if o.same && protector then
    if o.arr.length ≠ o.to then .ok (slowStore slow o.arr o.to v)
    else
      match append c u (pushKind c.undefinedDouble K) o.arr v with
      | .ok a' => .ok ⟨a', o.to + 1, true⟩
      | .failed a' => .ok (slowStore slow a' o.to v)
      | .fatal => .fatal
      | .ub => .ub
  else .ok (slowStore slow o.arr o.to v)

def body (c : FilterConfig) (u : Val) (K : Kind) (cb : Callback) (slow : SlowStore) :
    Out → Nat → Option Val → JSArr → Body Out JSArr
  | o, _, none, a => .next ⟨o, a, true⟩
  | o, k, some v, a =>
    let p := cb k v a
    if p.res then
      match store c u K slow o v p.protector with
      | .ok o' => .next ⟨o', p.arr, p.recheck⟩
      | .fatal => .fatal
      | .ub => .ub
    else .next ⟨o, p.arr, p.recheck⟩

def newOutput (K : Kind) : Out := ⟨⟨K, true, true, true, false, 0, []⟩, 0, true⟩

inductive Result where
  | done (a : JSArr)
  | species
  | bailout (ks : List Nat) (o : Out) (arr : JSArr)
  | fatal
  | ub

def fastFilter (c : FilterConfig) (u : Val) (cb : Callback) (slow : SlowStore)
    (speciesOk pushable : Bool) (a : JSArr) : Result :=
  if speciesOk = false ∨ a.fast = false then .species
  else if c.smiMax < a.length then .bailout (forward a.length) (newOutput a.kind) a
  else if pushable = false then .bailout (forward a.length) (newOutput a.kind) a
  else
    match loop a.kind.isDouble (body c u a.kind cb slow) (fun s => .done s.acc.arr)
        (forward a.length) ⟨newOutput a.kind, a, true⟩ with
    | .done r => .done r
    | .bailout ks s => .bailout ks s.acc s.arr
    | .fatal => .fatal
    | .ub => .ub

def specBody (cb : Callback) : List Val → Nat → Option Val → JSArr → SBody (List Val) (List Val)
  | sel, _, none, a => .next sel a
  | sel, k, some v, a =>
    let p := cb k v a
    if p.res then .next (sel ++ [v]) p.arr else .next sel p.arr

def specFilter (cb : Callback) (a : JSArr) : List Val :=
  spec (specBody cb) (fun sel _ => sel) (forward a.length) [] a

end ArrayFilter
