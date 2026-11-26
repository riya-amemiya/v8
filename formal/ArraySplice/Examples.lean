import ArraySplice.Safety

namespace ArraySplice.Examples

open Torque InPlace ArraySplice

def cfg : Config := ⟨1073741823, 134217728⟩

def pushable : MapInfo := ⟨true, false, false, false⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def view : Result JSArr → Option (Kind × Nat × List (Option Val) × List (Option Val))
  | .done a d => some (a.kind, a.length, a.elems, d.elems)
  | _ => none

def isSlow : Result JSArr → Bool
  | .slow => true
  | _ => false

#guard view (fastPath cfg pushable (mk .packedSmi (smis [1, 2, 3, 4])) 4 (.full 1 2 [])) ==
  some (.packedSmi, 2, smis [1, 4], smis [2, 3])

#guard view (fastPath cfg pushable (mk .packedSmi (smis [1, 2, 3])) 3 (.full 1 0 [.smi 9, .smi 8])) ==
  some (.packedSmi, 5, smis [1, 9, 8, 2, 3], [])

#guard view (fastPath cfg pushable (mk .packedSmi (smis [1, 2, 3])) 3 (.full 1 1 [.num 5])) ==
  some (.packedDouble, 3, [some (.smi 1), some (.num 5), some (.smi 3)], smis [2])

#guard view (fastPath cfg pushable (mk .packedSmi (smis [1, 2, 3])) 3 (.full 0 3 [])) ==
  some (.packedSmi, 0, [], smis [1, 2, 3])

#guard view (fastPath cfg pushable (mk .holeySmi [some (.smi 1), none, some (.smi 3)]) 3
    (.full 0 1 [.other])) ==
  some (.holeyElem, 3, [some .other, none, some (.smi 3)], smis [1])

#guard view (fastPath cfg pushable (mk .packedSmi (smis [1, 2, 3])) 3 (.start (-1))) ==
  some (.packedSmi, 2, smis [1, 2], smis [3])

#guard isSlow (fastPath cfg pushable (mk .packedSmi (smis [1])) 3 (.full 0 1 []))

#guard isSlow (fastPath cfg ⟨false, false, false, false⟩ (mk .packedSmi (smis [1])) 1 (.full 0 1 []))

#guard (match fastPath cfg pushable { mk .packedSmi (smis [1, 2]) with cow := true } 2
    (.full 0 1 [.smi 7]) with
  | .done a d => a.elems == smis [7, 2] && !a.cow && d.elems == smis [1]
  | _ => false)

#guard (match insertLoop false .packedDouble [none] 0 [.other] with
  | .ub => true
  | _ => false)

#guard (match memmove false [none] 0 1 1 with
  | .ub => true
  | _ => false)

end ArraySplice.Examples
