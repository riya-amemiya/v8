import ArraySome.Safety

namespace ArraySome.Examples

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

def negative : Callback := fun _ v a =>
  ⟨match v with
    | .smi n => decide (n < 0)
    | _ => false, a, true, true⟩

def grow : Callback := fun _ _ a =>
  ⟨false, { a with length := a.length + 1, store := a.store ++ [some (.smi (-1))] }, true, true⟩

def toDoubles : Callback := fun _ _ a => ⟨false, { a with kind := .packedDouble }, false, true⟩

#guard result (fastSome cfg negative (mk .packedSmi (smis [1, 2, 3]))) == some false

#guard result (fastSome cfg negative (mk .packedSmi (smis [1, -2, 3]))) == some true

#guard result (fastSome cfg negative (mk .holeySmi [some (.smi 1), none, some (.smi 3)])) ==
  some false

#guard result (fastSome cfg grow (mk .packedSmi (smis [1, 2]))) == some false

#guard specSome grow (mk .packedSmi (smis [1, 2])) == false

#guard resumesAt (fastSome cfg toDoubles (mk .packedSmi (smis [1, 2, 3]))) == some [1, 2]

#guard specSome negative (mk .packedSmi (smis [1, -2, 3])) == true

end ArraySome.Examples
