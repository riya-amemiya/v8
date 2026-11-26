import ArrayReduce.Safety

namespace ArrayReduce.Examples

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

def add : Callback := fun _ p a =>
  ⟨match p with
    | (.smi x, .smi y) => .smi (x + y)
    | _ => .other, a, true, true⟩

def addAndFreeze : Callback := fun _ p a =>
  ⟨match p with
    | (.smi x, .smi y) => .smi (x + y)
    | _ => .other, { a with fast := false }, false, true⟩

#guard result (fastReduce cfg add (mk .packedSmi (smis [1, 2, 3])) none) == some (some (.smi 6))

#guard result (fastReduce cfg add (mk .packedSmi (smis [1, 2, 3])) (some (.smi 10))) ==
  some (some (.smi 16))

#guard result (fastReduce cfg add (mk .holeySmi [none, some (.smi 2), none, some (.smi 5)]) none) ==
  some (some (.smi 7))

#guard result (fastReduce cfg add (mk .holeySmi [none, none]) none) == some none

#guard specReduce add (mk .holeySmi [none, none]) none == none

#guard result (fastReduce cfg add (mk .packedSmi []) (some (.smi 4))) == some (some (.smi 4))

#guard resumesWith (fastReduce cfg addAndFreeze (mk .packedSmi (smis [1, 2, 3, 4])) none) ==
  some ([2, 3], some (.smi 3))

#guard specReduce addAndFreeze (mk .packedSmi (smis [1, 2, 3, 4])) none == some (.smi 10)

#guard result (fastReduce cfg add { mk .packedElem (smis [1, 2]) with fast := false } none) ==
  some (some (.smi 3))

end ArrayReduce.Examples
