import ArrayWith.Safety

namespace ArrayWith.Examples

open Torque ArrayCopyCommon

def r : SmiRepr := SmiRepr.compressed

def lim : Limits := ⟨16, 8⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def view : Result JSArr → Option (Kind × Nat × List (Option Val))
  | .done _ a => some (a.kind, a.length, a.elems)
  | _ => none

def isSlow : Result JSArr → Bool
  | .slow => true
  | _ => false

def isThrow : Result JSArr → Bool
  | .throws => true
  | _ => false

def isAbort : Result Unit → Bool
  | .abort => true
  | _ => false

def isUb : Result Unit → Bool
  | .ub => true
  | _ => false

#guard view (fastPath r lim true 3 1 (.smi 9) (mk .packedSmi (smis [1, 2, 3]))) ==
  some (.packedSmi, 3, smis [1, 9, 3])

#guard view (fastPath r lim true 3 (-1) (.smi 9) (mk .packedSmi (smis [1, 2, 3]))) ==
  some (.packedSmi, 3, smis [1, 2, 9])

#guard view (fastPath r lim true 3 0 (.num 5) (mk .packedSmi (smis [1, 2, 3]))) ==
  some (.packedDouble, 3, [some (.num 5), some (.smi 2), some (.smi 3)])

#guard view (fastPath r lim true 2 0 .undef (mk .packedDouble [some (.num 1), some (.num 2)])) ==
  some (.holeyDouble, 2, [some .undef, some (.num 2)])

#guard view (fastPath r lim false 2 0 .undef (mk .packedDouble [some (.num 1), some (.num 2)])) ==
  some (.packedElem, 2, [some .undef, some (.num 2)])

#guard view (fastPath r lim true 2 1 .other (mk .packedSmi (smis [1, 2, 3, 4]))) ==
  some (.packedElem, 2, [some (.smi 1), some .other])

#guard isSlow (fastPath r lim true 4 1 (.smi 0) (mk .packedSmi (smis [1, 2, 3])))

#guard isSlow (fastPath r lim true 3 1 (.smi 0) (mk .holeySmi [some (.smi 1), none, some (.smi 3)]))

#guard isThrow (fastPath r lim true 3 3 (.smi 0) (mk .packedSmi (smis [1, 2, 3])))

#guard isThrow (fastPath r lim true 3 (-4) (.smi 0) (mk .packedSmi (smis [1, 2, 3])))

#guard specWith [some (.smi 1), none] 3 0 (.smi 7) == [some (.smi 7), some .undef, some .undef]

#guard isAbort (fastCreate true ⟨.packedDouble, true, true, true, false, 1, []⟩ 0 (.num 1))

#guard isUb (fastCreate true ⟨.holeyDouble, true, true, true, false, 2, [some (.num 1)]⟩ 1 .undef)

end ArrayWith.Examples
