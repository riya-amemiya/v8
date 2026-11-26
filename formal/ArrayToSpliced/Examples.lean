import ArrayToSpliced.Safety

namespace ArrayToSpliced.Examples

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

def runUb : Run → Bool
  | .ub => true
  | _ => false

#guard view (fastPath r lim 4 (.full 1 2 [.smi 9]) (mk .packedSmi (smis [1, 2, 3, 4]))) ==
  some (.packedSmi, 3, smis [1, 9, 4])

#guard view (fastPath r lim 3 (.full (-1) 0 [.smi 7, .smi 8]) (mk .packedSmi (smis [1, 2, 3]))) ==
  some (.packedSmi, 5, smis [1, 2, 7, 8, 3])

#guard view (fastPath r lim 3 (.full 1 1 [.num 5]) (mk .packedSmi (smis [1, 2, 3]))) ==
  some (.packedDouble, 3, [some (.smi 1), some (.num 5), some (.smi 3)])

#guard view (fastPath r lim 2 (.full 0 0 [.num 5, .other]) (mk .packedSmi (smis [1, 2]))) ==
  some (.packedElem, 4, [some (.num 5), some .other, some (.smi 1), some (.smi 2)])

#guard view (fastPath r lim 2 (.full 2 0 [.undef]) (mk .packedDouble [some (.num 1), some (.num 2)])) ==
  some (.packedElem, 3, [some (.num 1), some (.num 2), some .undef])

#guard view (fastPath r lim 3 (.start 1) (mk .packedElem [some .other, some .proxy, some .undef])) ==
  some (.packedElem, 1, [some .other])

#guard view (fastPath r lim 2 .none (mk .packedSmi (smis [1, 2]))) ==
  some (.packedSmi, 2, smis [1, 2])

#guard view (fastPath r lim 2 (.start 0) (mk .packedSmi (smis [1, 2]))) == some (.packedSmi, 0, [])

#guard view (fastPath r lim 2 (.full 1 1 []) (mk .packedSmi (smis [1, 2, 3, 4]))) ==
  some (.packedSmi, 1, smis [1])

#guard isSlow (fastPath r lim 4 (.full 1 1 []) (mk .packedSmi (smis [1, 2, 3])))

#guard isSlow (fastPath r lim 3 (.full 1 1 []) (mk .holeySmi [some (.smi 1), none, some (.smi 3)]))

#guard isSlow (fastPath r lim 9 (.full 0 0 []) (mk .packedSmi (smis [1, 2, 3, 4, 5, 6, 7, 8, 9])))

#guard isThrow (fastPath r lim (2 ^ 53 - 1) (.full 0 0 [.smi 1]) (mk .packedSmi (smis [1])))

#guard specSpliced (smis [1, 2, 3, 4]) 4 1 2 [.smi 9] == smis [1, 9, 4]

#guard insertKind .packedSmi [.smi 1, .num 2, .other] == .packedElem

#guard insertKind .packedSmi [.smi 1, .num 2] == .packedDouble

#guard runUb (insertLoop true [some (.num 0)] 0 [.other])

#guard runUb (copyForToSpliced lim (smis [1, 2]) 4 1 1 0)

end ArrayToSpliced.Examples
