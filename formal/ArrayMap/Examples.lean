import ArrayMap.Safety

namespace ArrayMap.Examples

open Torque ArrayWitness ArrayMap

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def view : Result → Option (Kind × Nat × List (Option Val))
  | .done a => some (a.kind, a.length, a.elems)
  | _ => none

def bailoutView : Result → Option (Kind × Nat × List (Option Val) × List Nat)
  | .bailout out ks _ => some (out.kind, out.length, out.elems, ks)
  | _ => none

def double : Callback := fun _ v a =>
  ⟨match v with
    | .smi n => .smi (2 * n)
    | x => x, a, true, true⟩

def toNum : Callback := fun _ _ a => ⟨.num 1, a, true, true⟩

def toUndef : Callback := fun k _ a => ⟨if k = 0 then .undef else .num 1, a, true, true⟩

def shrinkAt1 : Callback := fun k v a =>
  ⟨v, if k = 1 then { a with length := 1 } else a, true, true⟩

def run (ud : Bool) (cb : Callback) (a : JSArr) : Result := fastMap ud 1073741823 true cb a

#guard view (run true double (mk .packedSmi (smis [1, 2, 3]))) ==
  some (.packedSmi, 3, smis [2, 4, 6])

#guard view (run true double (mk .holeySmi [some (.smi 1), none, some (.smi 3)])) ==
  some (.holeySmi, 3, [some (.smi 2), none, some (.smi 6)])

#guard view (run true toNum (mk .packedSmi (smis [1, 2]))) ==
  some (.packedDouble, 2, [some (.num 1), some (.num 1)])

#guard view (run true toUndef (mk .packedSmi (smis [1, 2]))) ==
  some (.holeyDouble, 2, [some .undef, some (.num 1)])

#guard view (run false toUndef (mk .packedSmi (smis [1, 2]))) ==
  some (.packedElem, 2, [some .undef, some (.num 1)])

#guard bailoutView (run true shrinkAt1 (mk .packedSmi (smis [1, 2, 3]))) ==
  some (.holeySmi, 3, [some (.smi 1), some (.smi 2), none], [2])

#guard specMap double (mk .holeySmi [some (.smi 1), none]) == [some (.smi 2), none]

#guard (match createJSArray true ⟨[some .other], false, true, true, false⟩ 1 with
  | .ub => true
  | _ => false)

#guard (match run true double { mk .packedSmi (smis [1]) with forRead := false } with
  | .species => true
  | _ => false)

end ArrayMap.Examples
