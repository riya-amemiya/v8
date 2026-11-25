import ArrayCopyWithin.Model

namespace ArrayCopyWithin.Examples

open Torque

def r : SmiRepr := SmiRepr.compressed

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def elemsOf : Result → Option (List (Option Val))
  | .done a => some a.elems
  | _ => none

def isUb : Result → Bool
  | .ub => true
  | _ => false

#guard elemsOf (fastPath r (mk .packedSmi (smis [1, 2, 3, 4, 5])) 5 ⟨0, 3, none⟩) ==
  some (smis [4, 5, 3, 4, 5])

#guard elemsOf (fastPath r (mk .packedSmi (smis [1, 2, 3, 4, 5])) 5 ⟨1, 0, none⟩) ==
  some (smis [1, 1, 2, 3, 4])

#guard elemsOf (fastPath r (mk .packedSmi (smis [1, 2, 3, 4, 5])) 5 ⟨-2, 0, some 1⟩) ==
  some (smis [1, 2, 3, 1, 5])

#guard specCopy (smis [1, 2, 3, 4, 5]) 1 0 4 == smis [1, 1, 2, 3, 4]

#guard elemsOf (fastPath r (mk .holeySmi [some (.smi 1), none, some (.smi 3)]) 3 ⟨0, 1, none⟩) ==
  some [none, some (.smi 3), some (.smi 3)]

#guard elemsOf (fastPath r { mk .packedSmi (smis [1, 2, 3]) with cow := true } 3 ⟨0, 1, none⟩) ==
  some (smis [2, 3, 3])

#guard isUb (tryFast r (mk .packedSmi (smis [1, 2, 3, 4, 5])) (-1) 0 1)

#guard isUb (fastPath r ⟨.packedSmi, true, true, true, false, 3, []⟩ 3 ⟨0, 1, none⟩)

#guard SmiRepr.above (r.add (2 ^ 30 - 1) (2 ^ 30 - 1)) (r.word 5) &&
  !r.greaterThan (r.add (2 ^ 30 - 1) (2 ^ 30 - 1)) (r.word 5)

end ArrayCopyWithin.Examples
