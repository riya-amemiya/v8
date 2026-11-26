import ArraySlice.Safety

namespace ArraySlice.Examples

open Torque ArrayCopyCommon ArraySlice

def cfg : Config := ⟨⟨128, 32⟩, 1073741823, 64⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def view : Out → Option (Kind × Nat × List (Option Val) × Bool)
  | .done a => some (a.kind, a.length, a.elems, a.cow)
  | _ => none

def isSlow : Out → Bool
  | .slow => true
  | _ => false

#guard sliceIndices 5 1 (some (-1)) == (1, 3)

#guard sliceIndices 5 (-2) none == (3, 2)

#guard sliceIndices 5 4 (some 2) == (4, 0)

#guard view (handleFastSlice cfg (.array (mk .packedSmi (smis [1, 2, 3, 4]))) 1 2) ==
  some (.packedSmi, 2, smis [2, 3], false)

#guard view (handleFastSlice cfg (.array (mk .holeySmi [some (.smi 1), none, some (.smi 3)])) 0 3) ==
  some (.holeySmi, 3, [some (.smi 1), none, some (.smi 3)], false)

#guard isSlow (handleFastSlice cfg (.array ⟨.packedSmi, true, true, true, false, 2,
  [some (.smi 1), some (.smi 2), none, none]⟩) 1 2)

#guard view (slice cfg 2 (.array { mk .packedSmi (smis [1, 2]) with cow := true }) .undef none
  (.array { mk .packedSmi (smis [1, 2]) with cow := true })) == some (.packedSmi, 2, smis [1, 2], true)

#guard view (handleFastSlice cfg (.strictArgs (some (smis [1, 2, 3]))) 1 2) ==
  some (.holeyElem, 2, smis [2, 3], false)

#guard isSlow (handleFastSlice cfg (.strictArgs (some (smis [1]))) 0 2)

#guard isSlow (handleFastSlice cfg (.sloppyArgs none) 0 1)

def aliased : Aliased := ⟨[some 0, none], [.smi 10], some [none, some (.smi 2), some (.smi 3)]⟩

#guard view (handleFastSlice cfg (.aliasedArgs aliased) 0 3) ==
  some (.holeyElem, 3, [some (.smi 10), some (.smi 2), some (.smi 3)], false)

#guard view (handleFastSlice cfg (.aliasedArgs aliased) 1 2) ==
  some (.holeyElem, 2, [some (.smi 2), some (.smi 3)], false)

#guard aliasedSpec aliased [none, some (.smi 2), some (.smi 3)] 0 3 ==
  [some (.smi 10), some (.smi 2), some (.smi 3)]

#guard (match handleFastSlice cfg (.aliasedArgs ⟨[some 5], [.smi 10], some [none]⟩) 0 1 with
  | .fatal => true
  | _ => false)

#guard (match extractFast cfg.lim ⟨.packedSmi, true, true, true, false, 3, []⟩ 0 3 with
  | .ub => true
  | _ => false)

end ArraySlice.Examples
