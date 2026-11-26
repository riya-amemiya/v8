import ArrayWitness

namespace ArrayMap

open Torque ArrayWitness

abbrev Callback := Nat → Val → JSArr → Post Val

structure Vec where
  store : List (Option Val)
  onlySmis : Bool
  onlyNumbers : Bool
  onlyNumUndef : Bool
  skipped : Bool
  deriving Repr

def newVector (len : Nat) : Vec := ⟨List.replicate len none, true, true, true, false⟩

def noteResult (ud : Bool) (v : Vec) : Val → Vec
  | .smi _ => v
  | .num _ => { v with onlySmis := false }
  | .undef =>
    { v with
      onlySmis := false
      onlyNumbers := false
      onlyNumUndef := v.onlyNumUndef && ud }
  | _ => { v with onlySmis := false, onlyNumbers := false, onlyNumUndef := false }

def storeResult (ud : Bool) (v : Vec) (k : Nat) (r : Val) : Option Vec :=
  if k < v.store.length then some { noteResult ud v r with store := v.store.set k (some r) }
  else none

def body (ud : Bool) (cb : Callback) : Vec → Nat → Option Val → JSArr → Body Vec JSArr
  | v, _, none, a => .next ⟨{ v with skipped := true }, a, true⟩
  | v, k, some x, a =>
    let p := cb k x a
    match storeResult ud v k p.res with
    | some v' => .next ⟨v', p.arr, p.recheck⟩
    | none => .fatal

def baseKind (v : Vec) : Kind :=
  if v.onlySmis then .packedSmi
  else if v.onlyNumbers then .packedDouble
  else if v.onlyNumUndef then .holeyDouble
  else .packedElem

def resultKind (v : Vec) (valid : Nat) : Kind :=
  if v.skipped = true ∨ valid < v.store.length then (baseKind v).toHoley else baseKind v

def doubleOk (ud : Bool) : Option Val → Bool
  | none => true
  | some x => x.isNumber || (ud && x == .undef)

inductive Created where
  | arr (a : JSArr)
  | ub
  deriving Repr

def createJSArray (ud : Bool) (v : Vec) (valid : Nat) : Created :=
  if (resultKind v valid).isDouble then
    if ((v.store.take valid).all (doubleOk ud)) = false then .ub
    else .arr ⟨resultKind v valid, true, true, false, false, v.store.length,
      v.store.take valid ++ List.replicate (v.store.length - valid) none⟩
  else .arr ⟨resultKind v valid, true, true, false, false, v.store.length, v.store⟩

def finish (ud : Bool) (len : Nat) (s : St Vec) : Res Vec JSArr :=
  match createJSArray ud s.acc len with
  | .arr a => .done a
  | .ub => .ub

inductive Result where
  | done (a : JSArr)
  | species
  | bailout (output : JSArr) (ks : List Nat) (arr : JSArr)
  | fatal
  | ub
  deriving Repr

def fastMap (ud : Bool) (smiMax : Nat) (speciesOk : Bool) (cb : Callback) (a : JSArr) : Result :=
  if speciesOk = false ∨ a.forRead = false ∨ smiMax < a.length then .species
  else
    match loop a.kind.isDouble (body ud cb) (finish ud a.length) (forward a.length)
        ⟨newVector a.length, a, true⟩ with
    | .done r => .done r
    | .bailout ks s =>
      match createJSArray ud s.acc (a.length - ks.length) with
      | .arr out => .bailout out ks s.arr
      | .ub => .ub
    | .fatal => .fatal
    | .ub => .ub

def specBody (cb : Callback) :
    List (Option Val) → Nat → Option Val → JSArr → SBody (List (Option Val)) (List (Option Val))
  | out, _, none, a => .next out a
  | out, k, some x, a =>
    let p := cb k x a
    .next (out.set k (some p.res)) p.arr

def specMap (cb : Callback) (a : JSArr) : List (Option Val) :=
  spec (specBody cb) (fun out _ => out) (forward a.length) (List.replicate a.length none) a

end ArrayMap
