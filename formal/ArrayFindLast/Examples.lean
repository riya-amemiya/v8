import ArrayFindLast.Safety

namespace ArrayFindLast.Examples

open Torque ArrayWitness

def cfg : Config := ⟨2 ^ 30 - 1, 128 * 1024 * 1024⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def result : Res Unit (Option Val) → Option (Option Val)
  | .done r => some r
  | _ => none

def resumesAt : Res Unit (Option Val) → Option (List Nat)
  | .bailout ks _ => some ks
  | _ => none

def smaller (m : Int) : Callback := fun _ x a =>
  ⟨match x with
    | some (.smi n) => decide (n < m)
    | _ => false, a, true, true⟩

def shrink : Callback := fun _ _ a => ⟨false, { a with length := 1 }, true, true⟩

#guard result (fastFindLast cfg (smaller 3) (mk .packedSmi (smis [1, 2, 3]))) ==
  some (some (.smi 2))

#guard result (fastFindLast cfg (smaller 0) (mk .packedSmi (smis [1, 2, 3]))) == some none

#guard resumesAt (fastFindLast cfg shrink (mk .packedSmi (smis [1, 2, 3, 4]))) == some [2, 1, 0]

#guard specFindLast shrink (mk .packedSmi (smis [1, 2, 3, 4])) == none

#guard resumesAt (fastFindLast cfg shrink { mk .packedSmi (smis [1, 2]) with fast := false }) ==
  some [1, 0]

#guard result (fastFindLast cfg shrink (mk .packedSmi [])) == some none

end ArrayFindLast.Examples
