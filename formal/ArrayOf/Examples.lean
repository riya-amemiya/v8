import ArrayOf.Safety

namespace ArrayOf.Examples

open Torque ArrayBuild ArrayOf

def cfg : Config := ⟨4, true, ⟨⟨64, true⟩, true⟩⟩

def runtime (b : JSArr) (k : Nat) (v : Val) : JSArr :=
  let s := ensureWritable b
  { s with
    kind := .holeyElem
    store := if k < s.store.length then s.store.set k (some v) else s.store ++ [some v]
    length := max s.length (k + 1) }

def create (n : Nat) : JSArr := ⟨.slow, false, false, false, false, n, List.replicate n none⟩

def view : Result → Option (Kind × Nat × List (Option Val))
  | .done a => some (a.kind, a.length, a.elems)
  | _ => none

def isGeneric : Result → Bool
  | .generic => true
  | _ => false

#guard view (arrayOf cfg runtime .arrayFunction create [.smi 1, .smi 2, .smi 3]) ==
  some (.packedSmi, 3, [some (.smi 1), some (.smi 2), some (.smi 3)])

#guard view (arrayOf cfg runtime .arrayFunction create [.smi 1, .num 2]) ==
  some (.holeyElem, 2, [some (.smi 1), some (.num 2)])

#guard view (arrayOf cfg runtime .arrayFunction create []) == some (.packedSmi, 0, [])

#guard view (arrayOf cfg runtime .arrayFunction create (List.replicate 5 (.smi 7))) ==
  some (.holeyElem, 5, List.replicate 5 (some (.smi 7)))

#guard view (arrayOf cfg runtime .notConstructor create [.other]) == some (.holeyElem, 1, [some .other])

#guard isGeneric (arrayOf cfg runtime .otherConstructor create [.smi 1])

#guard fastCreateDataProperty cfg.store (filledWithZero cfg 2) 1 (.smi 9) matches .done _

#guard fastCreateDataProperty cfg.store (filledWithZero cfg 2) 1 (.num 9) matches .slow _

#guard storeUnchecked ⟨.holeyDouble, true, true, false, false, 2, [none]⟩ 1 .undef matches .ub

end ArrayOf.Examples
