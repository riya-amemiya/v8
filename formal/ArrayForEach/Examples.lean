import ArrayForEach.Safety

namespace ArrayForEach.Examples

open Torque ArrayWitness

def cfg : Config := ⟨2 ^ 30 - 1, 128 * 1024 * 1024⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def finalElems : Res Unit JSArr → Option (List (Option Val))
  | .done a => some a.elems
  | _ => none

def resumesAt : Res Unit JSArr → Option (List Nat)
  | .bailout ks _ => some ks
  | _ => none

def double : Callback := fun k v a =>
  ⟨(), { a with store := a.store.set k (some (match v with
    | .smi n => .smi (2 * n)
    | w => w)) }, true, true⟩

def clear : Callback := fun _ _ a => ⟨(), { a with length := 0 }, true, true⟩

def toHoley : Callback := fun _ _ a => ⟨(), { a with kind := .holeySmi }, false, true⟩

#guard finalElems (fastForEach cfg double (mk .packedSmi (smis [1, 2, 3]))) == some (smis [2, 4, 6])

#guard (specForEach double (mk .packedSmi (smis [1, 2, 3]))).elems == smis [2, 4, 6]

#guard finalElems (fastForEach cfg double (mk .holeySmi [some (.smi 1), none, some (.smi 3)])) ==
  some [some (.smi 2), none, some (.smi 6)]

#guard resumesAt (fastForEach cfg clear (mk .packedSmi (smis [1, 2, 3]))) == some [1, 2]

#guard resumesAt (fastForEach cfg toHoley (mk .packedSmi (smis [1, 2, 3]))) == some [1, 2]

end ArrayForEach.Examples
