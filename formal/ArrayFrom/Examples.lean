import ArrayFrom.Safety

namespace ArrayFrom.Examples

open Torque ArrayBuild ArrayFrom

def cfg : Config := ⟨4, true, ⟨⟨64, true⟩, true⟩⟩

def runtime (b : JSArr) (k : Nat) (v : Val) : JSArr :=
  let s := ensureWritable b
  { s with
    kind := .holeyElem
    store := if k < s.store.length then s.store.set k (some v) else s.store ++ [some v]
    length := max s.length (k + 1) }

def create (n : Nat) : JSArr := ⟨.slow, false, false, false, false, n, List.replicate n none⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def view : Result → Option (Kind × Nat × List (Option Val))
  | .done a => some (a.kind, a.length, a.elems)
  | _ => none

def isUb : Result → Bool
  | .ub => true
  | _ => false

#guard view (fromFastArray (mk .holeySmi [some (.smi 1), none, some (.smi 3)])) ==
  some (.packedElem, 3, [some (.smi 1), some .undef, some (.smi 3)])

#guard view (fromFastArray (mk .holeyDouble [some (.num 1), some .undef])) ==
  some (.holeyDouble, 2, [some (.num 1), some .undef])

#guard view (fromFastArray { mk .packedElem [some .other] with fast := false }) ==
  some (.packedElem, 1, [some .other])

#guard isUb (fromFastArray ⟨.holeySmi, true, true, true, false, 2, []⟩)

#guard (stringToList cfg [0x61, 0xD83D, 0xDE00, 0x62]).2 == [[0x61], [0xD83D, 0xDE00], [0x62]]

#guard view (stringToList cfg [0x61, 0xD83D, 0xDE00, 0x62]).1 ==
  some (.packedElem, 3, List.replicate 3 (some .other))

#guard (stringToList cfg [0xD83D, 0x61, 0xDE00]).2 == [[0xD83D], [0x61], [0xDE00]]

#guard (match (stringToList cfg [0xD83D, 0xDE00]).1 with
  | .done a => a.store == [some .other, none]
  | _ => false)

#guard view (fromArrayLike cfg runtime .arrayFunction create [.smi 1, .num 2, .smi 3]) ==
  some (.holeyElem, 3, [some (.smi 1), some (.num 2), some (.smi 3)])

#guard view (fromArrayLike cfg runtime .arrayFunction create (List.replicate 5 (.smi 0))) ==
  some (.holeyElem, 5, List.replicate 5 (some (.smi 0)))

#guard view (fromIterable cfg runtime .arrayFunction (mk .packedSmi []) [.smi 4, .smi 5]) ==
  some (.packedSmi, 2, [some (.smi 4), some (.smi 5)])

end ArrayFrom.Examples
