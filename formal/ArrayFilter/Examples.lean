import ArrayFilter.Safety

namespace ArrayFilter.Examples

open Torque ArrayWitness ArrayFilter

def cfg : FilterConfig := ⟨1073741823, true, fun _ => 64⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def slow : SlowStore := fun a k v =>
  ⟨{ a with
    kind := .holeyElem
    store := if k < a.store.length then a.store.set k (some v) else a.store ++ [some v]
    length := max a.length (k + 1) }, false⟩

def view : Result → Option (Kind × Nat × List (Option Val))
  | .done a => some (a.kind, a.length, a.elems)
  | _ => none

def odd : Callback := fun _ v a =>
  ⟨match v with
    | .smi n => n % 2 == 1
    | _ => true, a, true, true⟩

def keepAll : Callback := fun _ _ a => ⟨true, a, true, true⟩

def breakOutput : Callback := fun _ _ a => ⟨true, a, true, false⟩

def run (cb : Callback) (a : JSArr) : Result := fastFilter cfg .undef cb slow true true a

#guard view (run odd (mk .packedSmi (smis [1, 2, 3]))) == some (.packedSmi, 2, smis [1, 3])

#guard specFilter odd (mk .packedSmi (smis [1, 2, 3])) == [.smi 1, .smi 3]

#guard view (run keepAll (mk .holeySmi [some (.smi 1), none, some (.smi 3)])) ==
  some (.holeySmi, 2, smis [1, 3])

#guard view (run keepAll (mk .packedDouble [some (.num 1), some (.num 2)])) ==
  some (.packedDouble, 2, [some (.num 1), some (.num 2)])

#guard (match run breakOutput (mk .packedSmi (smis [1, 2])) with
  | .bailout ks o _ => ks == [1] && o.to == 1 && o.arr.elems == smis [1] && !o.same
  | _ => false)

#guard (match fastFilter cfg .undef keepAll slow false true (mk .packedSmi (smis [1])) with
  | .species => true
  | _ => false)

#guard (match append cfg .undef .packedDouble (mk .packedSmi []) (.num 1) with
  | .ub => true
  | _ => false)

#guard (match append cfg .undef .holeySmi { mk .packedSmi (smis [1]) with cow := true } (.smi 2) with
  | .ub => true
  | _ => false)

end ArrayFilter.Examples
