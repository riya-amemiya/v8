import ArrayUnshift.Safety

namespace ArrayUnshift.Examples

open Torque InPlace

def cfg : Config := ⟨2 ^ 30 - 1, 64⟩

def plain : MapInfo := ⟨true, false, false, false⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def view : Result Nat → Option (Kind × Nat × List (Option Val) × Nat × Nat)
  | .done a r => some (a.kind, a.length, a.elems, a.store.length, r)
  | _ => none

def isSlow : Result Nat → Bool
  | .slow => true
  | _ => false

def isThrows : Result Nat → Bool
  | .throws => true
  | _ => false

def isUb : Result Nat → Bool
  | .ub => true
  | _ => false

#guard view (unshift cfg plain (mk .packedSmi (smis [3, 4])) [.smi 1, .smi 2]) ==
  some (.packedSmi, 4, smis [1, 2, 3, 4], 22, 4)

#guard view (unshift cfg plain { mk .packedSmi (smis [3, 4] ++ List.replicate 3 none) with
    length := 2 } [.smi 1, .smi 2]) ==
  some (.packedSmi, 4, smis [1, 2, 3, 4], 5, 4)

#guard view (unshift cfg plain (mk .packedSmi (smis [3])) [.num 5]) ==
  some (.packedDouble, 2, [some (.num 5), some (.smi 3)], 19, 2)

#guard view (unshift cfg plain (mk .holeySmi [none, some (.smi 3)]) [.num 5, .other]) ==
  some (.holeyElem, 4, [some (.num 5), some .other, none, some (.smi 3)], 22, 4)

#guard view (unshift cfg plain (mk .packedDouble [some (.num 1)]) [.undef]) ==
  some (.packedElem, 2, [some .undef, some (.num 1)], 19, 2)

#guard view (unshift cfg plain (mk .packedSmi (smis [1, 2])) []) ==
  some (.packedSmi, 2, smis [1, 2], 2, 2)

#guard view (unshift cfg plain { mk .packedSmi (smis [1, 2]) with cow := true } [.smi 0]) ==
  some (.packedSmi, 3, smis [0, 1, 2], 20, 3)

#guard isSlow (unshift cfg ⟨true, false, false, true⟩ (mk .packedSmi (smis [1])) [.smi 0])

#guard isThrows (unshift cfg plain (mk .packedSmi (smis (List.replicate 48 0))) [.smi 0])

#guard isUb (addArguments cfg { mk .packedDouble [some (.num 1), none] with length := 1 } [.undef])

#guard newElementsCapacity 64 40 = 64 && newElementsCapacity 64 50 = 91

end ArrayUnshift.Examples
