import InPlace

namespace ArrayReverse

open Torque InPlace

def revLoop (cow : Bool) (s : List (Option Val)) (lower upper : Int) : Res (List (Option Val)) :=
  if h : lower < upper then do
    let lowerValue ← loadSlot s lower
    let upperValue ← loadSlot s upper
    let s1 ← storeSlot cow s lower upperValue
    let s2 ← storeSlot cow s1 upper lowerValue
    revLoop cow s2 (lower + 1) (upper - 1)
  else .ok s
termination_by (upper - lower).toNat

def fastReverse (b : JSArr) : Result Unit :=
  (revLoop b.cow b.store 0 ((b.length : Int) - 1)).then fun s => .done { b with store := s } ()

def tryFast (c : Config) (a : JSArr) : Result Unit :=
  if a.fast = false then .slow
  else match a.kind with
    | .packedSmi => (ensureWritableChecked c a).then fastReverse
    | .packedElem => (ensureWritableChecked c a).then fastReverse
    | .packedDouble => fastReverse a
    | .holeySmi => (ensureWritableChecked c a).then fastReverse
    | .holeyElem => (ensureWritableChecked c a).then fastReverse
    | .holeyDouble => fastReverse a
    | .slow => .slow

def specReverse (xs : List (Option Val)) : List (Option Val) :=
  (List.range xs.length).map fun lower => xs.getD (xs.length - lower - 1) none

end ArrayReverse
