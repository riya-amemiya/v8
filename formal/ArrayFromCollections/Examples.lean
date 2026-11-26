import ArrayFromCollections.Safety

namespace ArrayFromCollections.Examples

open Torque ArrayFromCollections

def live (n : Int) : Entry := ⟨.key (.smi n), .smi (10 * n)⟩

def dead : Entry := ⟨.hole, .undef⟩

def withDeleted : Table := ⟨2, 2, 1, [live 1, dead, live 3, dead]⟩

def overcounted : Table := ⟨2, 1, 1, [live 1, live 2, dead]⟩

def iter (index : Nat) (t : Table) : Iter := ⟨true, [], t, index⟩

def env : Env := ⟨false, false, true, true, true, true⟩

def elems : Outcome (JSArr × Iterable) → Option (List (Option Val))
  | .ok (a, _) => some a.elems
  | _ => none

def isBailout : Outcome (JSArr × Iterable) → Bool
  | .bailout => true
  | _ => false

def isUb : Outcome (JSArr × Iter) → Bool
  | .ub => true
  | _ => false

#guard liveCount (withDeleted.data.take withDeleted.used) == withDeleted.nof

#guard elems (fastIterableToList env (.mapIter .keys (iter 0 withDeleted))) ==
  some [some (.smi 1), some (.smi 3)]

#guard elems (fastIterableToList env (.mapIter .values (iter 0 withDeleted))) ==
  some [some (.smi 10), some (.smi 30)]

#guard elems (fastIterableToList env (.set ⟨true, withDeleted⟩)) ==
  some [some (.smi 1), some (.smi 3)]

#guard elems (fastIterableToList env (.setIter .values (iter 0 withDeleted))) ==
  some [some (.smi 1), some (.smi 3)]

#guard (Iterable.mapIter .keys (iter 0 withDeleted)).spec == [.smi 1, .smi 3]

#guard isBailout (fastIterableToList env (.mapIter .entries (iter 0 withDeleted)))

#guard isBailout (fastIterableToList env (.mapIter .keys (iter 1 withDeleted)))

#guard isBailout (fastIterableToList env (.setIter .values (iter 1 withDeleted)))

#guard (match mapIteratorToList .keys (iter 1 withDeleted) with
  | .ok (a, _) => a.kind == .packedElem && a.elems == [some (.smi 3), none]
  | _ => false)

#guard liveCount (overcounted.data.take overcounted.used) != overcounted.nof

#guard isUb (mapIteratorToList .keys (iter 0 overcounted))

end ArrayFromCollections.Examples
