import ArrayFindLastIndex.Safety

namespace ArrayFindLastIndex.Examples

open Torque ArrayWitness

def cfg : Config := ⟨2 ^ 30 - 1, 128 * 1024 * 1024⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def result : Res Unit Int → Option Int
  | .done r => some r
  | _ => none

def resumesAt : Res Unit Int → Option (List Nat)
  | .bailout ks _ => some ks
  | _ => none

def smaller (m : Int) : Callback := fun _ x a =>
  ⟨match x with
    | some (.smi n) => decide (n < m)
    | _ => false, a, true, true⟩

def isUndefined : Callback := fun _ x a => ⟨x.isNone, a, true, true⟩

def breakProtector : Callback := fun _ _ a => ⟨false, a, true, false⟩

#guard result (fastFindLastIndex cfg (smaller 3) (mk .packedSmi (smis [1, 2, 3]))) == some 1

#guard result (fastFindLastIndex cfg (smaller 0) (mk .packedSmi (smis [1, 2, 3]))) == some (-1)

#guard result (fastFindLastIndex cfg isUndefined (mk .holeySmi [none, some (.smi 2)])) == some 0

#guard resumesAt (fastFindLastIndex cfg breakProtector (mk .packedSmi (smis [1, 2, 3]))) ==
  some [1, 0]

#guard specFindLastIndex isUndefined (mk .holeySmi [none, some (.smi 2)]) == 0

end ArrayFindLastIndex.Examples
