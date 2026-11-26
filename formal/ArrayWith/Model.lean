import ArrayCopyCommon

namespace ArrayWith

open Torque ArrayCopyCommon

def convertRelativeIndex (index : Int) (len : Nat) : Option Nat :=
  let rel : Int := if 0 ≤ index then index else (len : Int) + index
  if rel < 0 ∨ (len : Int) ≤ rel then none else some rel.toNat

def runtimeKind (ud : Bool) (k : Kind) (v : Val) : Kind :=
  k.moreGeneral (if k.isHoley then (optimalKind ud v).toHoley else optimalKind ud v)

def runtimeCreate (ud : Bool) (c : JSArr) (i : Nat) (v : Val) : JSArr :=
  { c with kind := runtimeKind ud c.kind v, cow := false, store := c.store.set i (some v) }

def storeInto (c : JSArr) (i : Nat) (v : Val) : Result Unit :=
  match storeChecked c.store i v with
  | some s => .done () { c with store := s }
  | none => .abort

def storeUndefined (c : JSArr) (i : Nat) : Result Unit :=
  if i < c.store.length then .done () { c with store := c.store.set i (some .undef) } else .ub

def fastCreate (ud : Bool) (c : JSArr) (i : Nat) (v : Val) : Result Unit :=
  if c.fast = false ∨ c.length ≤ i then .done () (runtimeCreate ud c i v)
  else
    let c := ensureWritable c
    match c.kind with
    | .packedSmi => if v.isSmi then storeInto c i v else .done () (runtimeCreate ud c i v)
    | .holeySmi => if v.isSmi then storeInto c i v else .done () (runtimeCreate ud c i v)
    | .packedDouble =>
      if ud = true ∧ c.store = [] then .abort
      else if v.isNumber then (if c.store = [] then .abort else storeInto c i v)
      else .done () (runtimeCreate ud c i v)
    | .holeyDouble =>
      if ud = true then
        (if c.store = [] then .abort
         else if v.isNumber then storeInto c i v
         else if v = .undef then storeUndefined c i
         else .done () (runtimeCreate ud c i v))
      else if v.isNumber then (if c.store = [] then .abort else storeInto c i v)
      else .done () (runtimeCreate ud c i v)
    | .packedElem => storeInto c i v
    | .holeyElem => storeInto c i v
    | .slow => .done () (runtimeCreate ud c i v)

def tryFast (r : SmiRepr) (lim : Limits) (ud : Bool) (len idx : Nat) (v : Val) (a : JSArr) :
    Result JSArr :=
  if a.fast = false then .slow
  else if isFastPacked a.kind = false then .slow
  else if r.max < len then .slow
  else if a.length < len then .slow
  else match extractFast lim a 0 len with
    | .done _ c => (fastCreate ud c idx v).mapSrc fun _ => a
    | .slow => .slow
    | .throws => .throws
    | .ub => .ub
    | .abort => .abort

def fastPath (r : SmiRepr) (lim : Limits) (ud : Bool) (len : Nat) (index : Int) (v : Val)
    (a : JSArr) : Result JSArr :=
  match convertRelativeIndex index len with
  | none => .throws
  | some idx => tryFast r lim ud len idx v a

def specWith (xs : List (Option Val)) (len idx : Nat) (v : Val) : List (Option Val) :=
  (List.range len).map fun k => if k = idx then some v else some (getOrUndef xs k)

end ArrayWith
