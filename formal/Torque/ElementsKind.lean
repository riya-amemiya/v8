import Torque.Value

namespace Torque

inductive Kind where
  | packedSmi
  | holeySmi
  | packedDouble
  | holeyDouble
  | packedElem
  | holeyElem
  | slow
  deriving DecidableEq, Repr

def Kind.isFast : Kind → Bool
  | .slow => false
  | _ => true

def Kind.isDouble : Kind → Bool
  | .packedDouble => true
  | .holeyDouble => true
  | _ => false

def kindOk : Kind → Option Val → Bool
  | .packedSmi, some v => v.isSmi
  | .packedSmi, none => false
  | .packedDouble, some v => v.isNumber
  | .packedDouble, none => false
  | .packedElem, some _ => true
  | .packedElem, none => false
  | .holeySmi, some v => v.isSmi
  | .holeySmi, none => true
  | .holeyDouble, some v => v.isNumber || v == .undef
  | .holeyDouble, none => true
  | .holeyElem, _ => true
  | .slow, _ => true

def Kind.isHoley : Kind → Bool
  | .holeySmi => true
  | .holeyDouble => true
  | .holeyElem => true
  | _ => false

def Kind.toHoley : Kind → Kind
  | .packedSmi => .holeySmi
  | .packedDouble => .holeyDouble
  | .packedElem => .holeyElem
  | k => k

def Kind.isMoreGeneral : Kind → Kind → Bool
  | _, .slow => false
  | .packedSmi, d => d != .packedSmi
  | .holeySmi, d => d != .packedSmi && d != .holeySmi
  | .packedDouble, d => d != .packedSmi && d != .holeySmi && d != .packedDouble
  | .holeyDouble, d => d == .packedElem || d == .holeyElem
  | .packedElem, d => d == .holeyElem
  | .holeyElem, _ => false
  | .slow, _ => false

def Kind.moreGeneral (src dst : Kind) : Kind := if src.isMoreGeneral dst then dst else src

def Kind.transitionTarget (src dst : Kind) : Kind := if src.isHoley then dst.toHoley else dst

def optimalKind (undefinedDouble : Bool) : Val → Kind
  | .smi _ => .packedSmi
  | .num _ => .packedDouble
  | .undef => if undefinedDouble then .holeyDouble else .packedElem
  | _ => .packedElem

end Torque
