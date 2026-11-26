import ArrayCopyCommon

namespace ArrayToReversed

open Torque ArrayCopyCommon

inductive Load where
  | val (v : Val) (allocates : Bool)
  | abort

def loadTagged (s : List (Option Val)) (i : Nat) : Load :=
  match s[i]? with
  | some x => .val (holeToUndef x) false
  | none => .abort

def loadPackedDouble (s : List (Option Val)) (i : Nat) : Load :=
  match s[i]? with
  | some (some v) => if v = .undef then .abort else .val v false
  | _ => .abort

def loadHoleyDouble (s : List (Option Val)) (i : Nat) : Load :=
  match s[i]? with
  | some (some v) => if v = .undef then .val .undef false else .val v true
  | some none => .val .undef false
  | none => .abort

def revLoop (load : Nat → Load) (len : Nat) : Nat → Nat → List (Option Val) → Run
  | 0, _, buf => .ok buf
  | n + 1, k, buf =>
    match load (len - k - 1) with
    | .abort => .abort
    | .val v alloc =>
      if alloc = true ∧ none ∈ buf then .ub
      else match storeChecked buf k v with
        | some buf' => revLoop load len n (k + 1) buf'
        | none => .abort

def copyReversed (lim : Limits) (a : JSArr) (kind : Kind) (load : Nat → Load) (init : Bool) :
    Result JSArr :=
  if lim.maxLen < a.length then .abort
  else
    let buf := if init then List.replicate a.length (some (.smi 0))
      else List.replicate a.length none
    match revLoop load a.length a.length 0 buf with
    | .ok buf' => if none ∈ buf' then .ub else .done a (newArray kind buf')
    | .ub => .ub
    | .abort => .abort

def tryFast (lim : Limits) (a : JSArr) : Result JSArr :=
  if a.fast = false then .slow
  else if a.length = 0 then .done a (newArray .packedSmi [])
  else match a.kind with
    | .packedSmi => copyReversed lim a .packedSmi (loadTagged a.store) false
    | .packedElem => copyReversed lim a .packedElem (loadTagged a.store) false
    | .packedDouble => copyReversed lim a .packedDouble (loadPackedDouble a.store) false
    | .holeySmi => copyReversed lim a .packedElem (loadTagged a.store) false
    | .holeyElem => copyReversed lim a .packedElem (loadTagged a.store) false
    | .holeyDouble => copyReversed lim a .packedElem (loadHoleyDouble a.store) true
    | .slow => .slow

def resultKind : Kind → Kind
  | .packedSmi => .packedSmi
  | .packedDouble => .packedDouble
  | _ => .packedElem

def specReversed (xs : List (Option Val)) : List (Option Val) :=
  xs.reverse.map fun x => some (holeToUndef x)

end ArrayToReversed
