import ArrayFindIndex.Safety

namespace ArrayFindIndex.Examples

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

def bigger (m : Int) : Callback := fun _ x a =>
  ⟨match x with
    | some (.smi n) => decide (m < n)
    | _ => false, a, true, true⟩

def isUndefined : Callback := fun _ x a => ⟨x.isNone, a, true, true⟩

def toObjects : Callback := fun _ _ a => ⟨false, { a with kind := .packedElem }, false, true⟩

#guard result (fastFindIndex cfg (bigger 1) (mk .packedSmi (smis [1, 2, 3]))) == some 1

#guard result (fastFindIndex cfg (bigger 5) (mk .packedSmi (smis [1, 2, 3]))) == some (-1)

#guard result (fastFindIndex cfg isUndefined (mk .holeySmi [some (.smi 1), none])) == some 1

#guard resumesAt (fastFindIndex cfg toObjects (mk .packedSmi (smis [1, 2, 3]))) == some [1, 2]

#guard specFindIndex isUndefined (mk .holeySmi [some (.smi 1), none]) == 1

end ArrayFindIndex.Examples
