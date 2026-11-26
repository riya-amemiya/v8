import ArrayToReversed.Safety

namespace ArrayToReversed.Examples

open Torque ArrayCopyCommon

def lim : Limits := ⟨16, 8⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def view : Result JSArr → Option (Kind × Nat × List (Option Val))
  | .done _ r => some (r.kind, r.length, r.elems)
  | _ => none

def isUb : Result JSArr → Bool
  | .ub => true
  | _ => false

def isAbort : Result JSArr → Bool
  | .abort => true
  | _ => false

#guard view (tryFast lim (mk .packedSmi (smis [1, 2, 3]))) == some (.packedSmi, 3, smis [3, 2, 1])

#guard view (tryFast lim (mk .holeySmi [some (.smi 1), none, some (.smi 3)])) ==
  some (.packedElem, 3, [some (.smi 3), some .undef, some (.smi 1)])

#guard view (tryFast lim (mk .packedDouble [some (.num 1), some (.smi 2)])) ==
  some (.packedDouble, 2, [some (.smi 2), some (.num 1)])

#guard view (tryFast lim (mk .holeyDouble [some (.num 1), none, some .undef])) ==
  some (.packedElem, 3, [some .undef, some .undef, some (.num 1)])

#guard view (tryFast lim { mk .packedElem [some .other, some .proxy] with cow := true }) ==
  some (.packedElem, 2, [some .proxy, some .other])

#guard view (tryFast lim ⟨.holeyElem, true, true, true, false, 2, [some .other, none, some .other]⟩) ==
  some (.packedElem, 2, [some .undef, some .other])

#guard view (tryFast lim (mk .packedDouble [])) == some (.packedSmi, 0, [])

#guard isAbort (tryFast ⟨2, 2⟩ (mk .packedSmi (smis [1, 2, 3])))

#guard isUb (copyReversed lim (mk .holeyDouble [some (.num 1), some (.num 2)]) .packedElem
  (loadHoleyDouble [some (.num 1), some (.num 2)]) false)

#guard isAbort (copyReversed lim (mk .packedDouble [some (.num 1), none]) .packedDouble
  (loadPackedDouble [some (.num 1), none]) false)

#guard isAbort (copyReversed lim (mk .packedDouble [some (.num 1), some .undef]) .packedDouble
  (loadPackedDouble [some (.num 1), some .undef]) false)

#guard specReversed [some (.smi 1), none] == [some .undef, some (.smi 1)]

end ArrayToReversed.Examples
