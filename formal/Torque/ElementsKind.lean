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
  | .holeyDouble, some v => v.isNumber || v == .other
  | .holeyDouble, none => true
  | .holeyElem, _ => true
  | .slow, _ => true

end Torque
