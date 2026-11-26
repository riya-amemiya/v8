import ArrayReduceRight.Safety

namespace ArrayReduceRight.Examples

open Torque ArrayWitness

def cfg : Config := ⟨2 ^ 30 - 1, 128 * 1024 * 1024⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def result : Res (Option Val) (Option Val) → Option (Option Val)
  | .done r => some r
  | _ => none

def resumesWith : Res (Option Val) (Option Val) → Option (List Nat × Option Val)
  | .bailout ks s => some (ks, s.acc)
  | _ => none

def sub : Callback := fun _ p a =>
  ⟨match p with
    | (.smi x, .smi y) => .smi (x - y)
    | _ => .other, a, true, true⟩

def subAndShrink : Callback := fun _ p a =>
  ⟨match p with
    | (.smi x, .smi y) => .smi (x - y)
    | _ => .other, { a with length := 1 }, true, true⟩

#guard result (fastReduceRight cfg sub (mk .packedSmi (smis [1, 2, 10])) none) ==
  some (some (.smi 7))

#guard specReduceRight sub (mk .packedSmi (smis [1, 2, 10])) none == some (.smi 7)

#guard result (fastReduceRight cfg sub (mk .holeySmi [some (.smi 1), none]) none) ==
  some (some (.smi 1))

#guard result (fastReduceRight cfg sub (mk .packedSmi []) none) == some none

#guard resumesWith (fastReduceRight cfg subAndShrink (mk .packedSmi (smis [1, 2, 3, 10])) none) ==
  some ([1, 0], some (.smi 7))

#guard specReduceRight subAndShrink (mk .packedSmi (smis [1, 2, 3, 10])) none == some (.smi 6)

end ArrayReduceRight.Examples
