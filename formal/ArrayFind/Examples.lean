import ArrayFind.Safety

namespace ArrayFind.Examples

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

def bigger (m : Int) : Callback := fun _ x a =>
  ⟨match x with
    | some (.smi n) => decide (m < n)
    | _ => false, a, true, true⟩

def isUndefined : Callback := fun _ x a => ⟨x.isNone, a, true, true⟩

def shrink : Callback := fun _ _ a => ⟨false, { a with length := 1 }, true, true⟩

#guard result (fastFind cfg (bigger 1) (mk .packedSmi (smis [1, 2, 3]))) == some (some (.smi 2))

#guard result (fastFind cfg (bigger 5) (mk .packedSmi (smis [1, 2, 3]))) == some none

#guard result (fastFind cfg isUndefined (mk .holeySmi [some (.smi 1), none, some (.smi 3)])) ==
  some none

#guard specFind isUndefined (mk .holeySmi [some (.smi 1), none, some (.smi 3)]) == none

#guard resumesAt (fastFind cfg shrink (mk .packedSmi (smis [1, 2, 3]))) == some [1, 2]

#guard specFind isUndefined (mk .packedSmi (smis [1, 2, 3])) == none

end ArrayFind.Examples
