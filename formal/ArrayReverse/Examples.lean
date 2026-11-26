import ArrayReverse.Safety

namespace ArrayReverse.Examples

open Torque InPlace

def cfg : Config := ⟨2 ^ 30 - 1, 128 * 1024 * 1024⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def view : Result Unit → Option (Kind × Nat × List (Option Val) × List (Option Val))
  | .done a _ => some (a.kind, a.length, a.elems, a.store)
  | _ => none

def isUb : Result Unit → Bool
  | .ub => true
  | _ => false

def isAbort : Result Unit → Bool
  | .abort => true
  | _ => false

def isSlow : Result Unit → Bool
  | .slow => true
  | _ => false

#guard view (tryFast cfg (mk .packedSmi (smis [1, 2, 3, 4, 5]))) ==
  some (.packedSmi, 5, smis [5, 4, 3, 2, 1], smis [5, 4, 3, 2, 1])

#guard view (tryFast cfg (mk .packedSmi (smis [1, 2, 3, 4]))) ==
  some (.packedSmi, 4, smis [4, 3, 2, 1], smis [4, 3, 2, 1])

#guard view (tryFast cfg (mk .packedSmi [])) == some (.packedSmi, 0, [], [])

#guard view (tryFast cfg (mk .holeyDouble [some (.num 1), none, some .undef])) ==
  some (.holeyDouble, 3, [some .undef, none, some (.num 1)], [some .undef, none, some (.num 1)])

#guard view (tryFast cfg { mk .packedSmi (smis [1, 2, 3]) with cow := true }) ==
  some (.packedSmi, 3, smis [3, 2, 1], smis [3, 2, 1])

#guard view (tryFast cfg { mk .holeySmi (smis [1, 2, 3] ++ [none, none]) with length := 3 }) ==
  some (.holeySmi, 3, smis [3, 2, 1], smis [3, 2, 1] ++ [none, none])

#guard isSlow (tryFast cfg { mk .holeyElem (smis [1, 2]) with fast := false })

#guard isAbort (fastReverse ⟨.packedSmi, true, true, true, false, 3, []⟩)

#guard isUb (fastReverse { mk .packedSmi (smis [1, 2]) with cow := true })

#guard specReverse (smis [1, 2, 3]) == smis [3, 2, 1]

end ArrayReverse.Examples
