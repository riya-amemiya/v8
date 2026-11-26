import ArrayShift.Safety

namespace ArrayShift.Examples

open Torque InPlace

def cfg : Config := ⟨2 ^ 30 - 1, 128 * 1024 * 1024⟩

def pushable : MapInfo := ⟨true, false, false, false⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def view : Result Val → Option (Kind × Nat × List (Option Val) × List (Option Val) × Val)
  | .done a r => some (a.kind, a.length, a.elems, a.store, r)
  | _ => none

def isSlow : Result Val → Bool
  | .slow => true
  | _ => false

def isAbort : Res (Option Val × List (Option Val)) → Bool
  | .abort => true
  | _ => false

#guard view (tryFast cfg pushable (mk .packedSmi (smis [1, 2, 3]))) ==
  some (.packedSmi, 2, smis [2, 3], smis [2, 3] ++ [none], .smi 1)

#guard view (tryFast cfg pushable (mk .holeySmi [none, some (.smi 2)])) ==
  some (.holeySmi, 1, smis [2], smis [2] ++ [none], .undef)

#guard view (tryFast cfg pushable (mk .packedSmi [])) == some (.packedSmi, 0, [], [], .undef)

#guard view (tryFast cfg pushable { mk .packedSmi (smis [7, 8]) with cow := true }) ==
  some (.packedSmi, 1, smis [8], smis [8] ++ [none], .smi 7)

#guard view (tryFast cfg pushable (mk .packedDouble [some (.num 1), some (.num 2)])) ==
  some (.packedDouble, 1, [some (.num 2)], [some (.num 2), none], .num 1)

#guard isSlow (tryFast cfg ⟨true, false, false, true⟩ (mk .packedSmi (smis [1, 2])))

#guard isSlow (tryFast cfg pushable (mk .packedSmi (smis (List.range 102 |>.map Int.ofNat))))

#guard isSlow (tryFast cfg pushable
  { mk .packedSmi (smis [1, 2] ++ List.replicate 30 none) with length := 2 })

#guard isAbort (shiftElements ⟨.packedDouble, true, true, true, false, 1, []⟩)

#guard specShift (smis [1, 2, 3]) == (smis [2, 3], .smi 1)

end ArrayShift.Examples
