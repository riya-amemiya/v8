import ArrayConcat.Safety

namespace ArrayConcat.Examples

open Torque ArrayBuild ArrayConcat

def env : Env := ⟨true⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def heap : Heap
  | 0 => mk .holeySmi [some (.smi 1), none, some (.smi 3)]
  | 1 => mk .packedSmi []
  | 2 => { mk .packedSmi (smis [4, 5]) with cow := true }
  | 3 => ⟨.packedSmi, true, true, true, false, 3, []⟩
  | _ => { mk .packedElem [some .other] with forCopy := false }

def view : Result → Option (Kind × Nat × List (Option Val) × Bool)
  | .done a => some (a.kind, a.length, a.elems, a.cow)
  | _ => none

def isUb : Result → Bool
  | .ub => true
  | _ => false

def isGeneric : Result → Bool
  | .generic => true
  | _ => false

#guard view (fastPath env heap (.arr 0) []) ==
  some (.holeySmi, 3, [some (.smi 1), none, some (.smi 3)], false)

#guard view (fastPath env heap (.arr 1) [.arr 0]) ==
  some (.holeySmi, 3, [some (.smi 1), none, some (.smi 3)], false)

#guard view (fastPath env heap (.arr 2) []) == some (.packedSmi, 2, smis [4, 5], true)

#guard isGeneric (fastPath ⟨false⟩ heap (.arr 0) [])

#guard isGeneric (fastPath env heap (.arr 0) [.arr 1])

#guard isGeneric (fastPath env heap (.arr 1) [.arr 4])

#guard isGeneric (fastPath env heap (.arr 1) [.arr 0, .arr 0])

#guard isUb (fastPath env heap (.arr 3) [])

end ArrayConcat.Examples
