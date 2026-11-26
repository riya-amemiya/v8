import ArrayWitness.Safety

namespace ArrayWitness.Examples

open Torque ArrayWitness

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

#guard load false (mk .holeySmi [some (.smi 1), none]) 0 == some (some (.smi 1))

#guard load false (mk .holeySmi [some (.smi 1), none]) 1 == some none

#guard load true (mk .packedSmi [some (.smi 1)]) 0 == none

#guard load false (mk .packedDouble [some (.num 1)]) 0 == none

#guard load false ⟨.packedSmi, true, true, true, false, 3, []⟩ 0 == none

#guard get (mk .holeySmi [some (.smi 1), none]) 1 == none

#guard get (mk .holeySmi [some (.smi 1), none]) 5 == none

#guard get { mk .packedSmi [some (.smi 1), some (.smi 2)] with length := 1 } 1 == none

#guard forward 3 == [0, 1, 2]

#guard backward 3 == [2, 1, 0]

end ArrayWitness.Examples
