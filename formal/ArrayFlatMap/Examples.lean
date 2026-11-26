import ArrayFlatMap.Safety

namespace ArrayFlatMap.Examples

open Torque ArrayWitness ArrayFlatMap

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def pairUp : Callback := fun _ v a =>
  ⟨.array (mk .packedSmi [some v, some v]), a, true, true⟩

def keep : Callback := fun _ v a => ⟨.value v, a, true, true⟩

def holeyInner : Callback := fun _ v a =>
  ⟨.array (mk .holeySmi [some v, none]), a, true, true⟩

def shrink : Callback := fun _ v a => ⟨.value v, { a with length := 1 }, true, true⟩

def result : Result → Option (List Val)
  | .done r => some r
  | _ => none

#guard result (fastFlatMap 1073741823 pairUp (mk .packedSmi (smis [1, 2]))) ==
  some [.smi 1, .smi 1, .smi 2, .smi 2]

#guard result (fastFlatMap 1073741823 keep (mk .holeySmi [some (.smi 1), none, some (.smi 3)])) ==
  some [.smi 1, .smi 3]

#guard result (fastFlatMap 1073741823 holeyInner (mk .packedSmi (smis [5]))) == some [.smi 5]

#guard specFlatMap pairUp (mk .packedSmi (smis [1, 2])) == [.smi 1, .smi 1, .smi 2, .smi 2]

#guard (match fastFlatMap 1073741823 shrink (mk .packedSmi (smis [1, 2, 3])) with
  | .bailout ks out _ => ks == [1, 2] && out == [.smi 1]
  | _ => false)

#guard innerLoop ⟨.packedSmi, true, true, true, false, 2, [some (.smi 1)]⟩ [0, 1] == none

end ArrayFlatMap.Examples
