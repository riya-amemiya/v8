import ArrayEvery.Safety

namespace ArrayEvery.Examples

open Torque ArrayWitness

def cfg : Config := ⟨2 ^ 30 - 1, 128 * 1024 * 1024⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def result : Res Unit Bool → Option Bool
  | .done r => some r
  | _ => none

def resumesAt : Res Unit Bool → Option (List Nat)
  | .bailout ks _ => some ks
  | _ => none

def positive : Callback := fun _ v a =>
  ⟨match v with
    | .smi n => decide (0 < n)
    | _ => false, a, true, true⟩

def shrink : Callback := fun _ _ a => ⟨true, { a with length := 1 }, true, true⟩

def toObjects : Callback := fun _ _ a => ⟨true, { a with kind := .packedElem }, false, true⟩

def breakProtector : Callback := fun _ _ a => ⟨true, a, true, false⟩

def visits : Callback := fun k _ a => ⟨k != 1, a, true, true⟩

#guard result (fastEvery cfg positive (mk .packedSmi (smis [1, 2, 3]))) == some true

#guard result (fastEvery cfg positive (mk .packedSmi (smis [1, -2, 3]))) == some false

#guard specEvery positive (mk .packedSmi (smis [1, -2, 3])) == false

#guard result (fastEvery cfg visits (mk .holeySmi [some (.smi 1), none, some (.smi 3)])) ==
  some true

#guard result (fastEvery cfg positive (mk .packedSmi [])) == some true

#guard resumesAt (fastEvery cfg shrink (mk .packedSmi (smis [1, 2, 3]))) == some [1, 2]

#guard specEvery shrink (mk .packedSmi (smis [1, 2, 3])) == true

#guard resumesAt (fastEvery cfg toObjects (mk .packedSmi (smis [1, 2, 3]))) == some [1, 2]

#guard resumesAt (fastEvery cfg breakProtector (mk .packedSmi (smis [1, 2, 3]))) == some [1, 2]

#guard resumesAt (fastEvery cfg positive { mk .packedSmi (smis [1, 2]) with fast := false }) ==
  some [0, 1]

#guard resumesAt (fastEvery ⟨1, 16⟩ positive (mk .packedSmi (smis [1, 2]))) == some [0, 1]

end ArrayEvery.Examples
