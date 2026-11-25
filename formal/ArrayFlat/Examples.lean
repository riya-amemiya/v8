import ArrayFlat.Machine

namespace ArrayFlat.Examples

open Torque

def v8Config : Config := ⟨2 ^ 30 - 1, 128 * 1024 * 1024⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def heapOf (arrays : List JSArr) : Heap := fun p =>
  arrays.getD p ⟨.slow, false, false, false, false, 0, []⟩

def result : Outcome JSArr → Option (Kind × List (Option Val))
  | .ok a => some (a.kind, a.store)
  | _ => none

def isBailout : Outcome JSArr → Bool
  | .bailout => true
  | _ => false

def isUb : Outcome JSArr → Bool
  | .ub => true
  | _ => false

def nested : Heap := heapOf [
  mk .packedElem [some (.smi 1), some (.arr 1)],
  mk .packedElem [some (.smi 2), some (.arr 2)],
  mk .packedSmi [some (.smi 3)]]

#guard result (tryFastFlat v8Config nested 0 2 1) ==
  some (.packedElem, [some (.smi 1), some (.smi 2), some (.arr 2)])

#guard result (tryFastFlat v8Config nested 0 2 2) ==
  some (.packedSmi, [some (.smi 1), some (.smi 2), some (.smi 3)])

def doubles : Heap := heapOf [
  mk .packedElem [some (.arr 1), some (.arr 2)],
  mk .packedDouble [some (.num 15)],
  mk .packedSmi [some (.smi 2)]]

#guard result (tryFastFlat v8Config doubles 0 2 1) ==
  some (.packedDouble, [some (.num 15), some (.smi 2)])

def holey : Heap := heapOf [mk .holeySmi [some (.smi 1), none, some (.smi 3)]]

#guard result (tryFastFlat v8Config holey 0 3 1) ==
  some (.packedSmi, [some (.smi 1), some (.smi 3)])

def cyclic : Heap := heapOf [mk .packedElem [some (.arr 0)]]

#guard isBailout (tryFastFlat v8Config cyclic 0 1 v8Config.smiMax)

#guard result (tryFastFlat v8Config cyclic 0 1 3) == some (.packedElem, [some (.arr 0)])

def withProxy : Heap := heapOf [mk .packedElem [some (.smi 1), some .proxy]]

#guard isBailout (tryFastFlat v8Config withProxy 0 2 1)

#guard result (tryFastFlat v8Config withProxy 0 2 0) ==
  some (.packedElem, [some (.smi 1), some .proxy])

def shrunk : Heap := heapOf [mk .packedSmi [some (.smi 1)]]

#guard isBailout (tryFastFlat v8Config shrunk 0 5 1)

def longerThanStore : Heap := heapOf [
  mk .packedElem [some (.arr 1)],
  ⟨.packedSmi, true, true, true, false, 3, []⟩]

#guard isUb (tryFastFlat v8Config longerThanStore 0 1 1)

end ArrayFlat.Examples
