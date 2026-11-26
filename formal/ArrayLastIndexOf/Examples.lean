import ArrayLastIndexOf.Safety

namespace ArrayLastIndexOf.Examples

open Torque ArrayLastIndexOf

def nan : Val := .num 999

def cmp : Cmp := ⟨fun s e => s == e && !(s == nan), fun s => s == nan⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def run (len : Nat) (arg : Option ExtInt) (a : JSArr) (s : Val) : Result :=
  lastIndexOf cmp 1073741823 len arg a s

def isDone (r : Int) : Result → Bool
  | .done r' => r' == r
  | _ => false

def isGeneric : Result → Bool
  | .generic _ => true
  | _ => false

#guard isDone 3 (run 4 none (mk .packedSmi (smis [1, 2, 3, 2])) (.smi 2))

#guard isDone 1 (run 4 (some (.fin (-2))) (mk .packedSmi (smis [1, 2, 3, 2])) (.smi 2))

#guard isDone (-1) (run 4 (some (.fin (-5))) (mk .packedSmi (smis [1, 2, 3, 2])) (.smi 2))

#guard isDone 0 (run 4 none ⟨.packedSmi, true, true, true, false, 1, [some (.smi 1), none, none]⟩
  (.smi 1))

#guard specLastIndexOf cmp (.smi 1) 4 none [some (.smi 1)] == 0

#guard isDone (-1) (run 4 none ⟨.packedSmi, true, true, true, false, 1, [some (.smi 1), none]⟩
  (.smi 2))

#guard scanStore (present cmp (.smi 1)) [some (.smi 1), none] 3 matches .fatal

#guard isDone 1 (run 2 none ⟨.packedSmi, true, true, true, false, 1, [some (.smi 1), some (.smi 2)]⟩
  (.smi 2))

#guard specLastIndexOf cmp (.smi 2) 2 none [some (.smi 1)] == -1

#guard isDone 1 (run 3 none (mk .holeyDouble [some (.num 1), some .undef, none]) .undef)

#guard isDone (-1) (run 3 none (mk .holeyDouble [some (.num 1), some .undef, none]) .other)

#guard isDone (-1) (run 2 none (mk .packedElem [some nan, some nan]) nan)

#guard isGeneric (run 2 (some .negInf) (mk .packedSmi (smis [1, 2])) (.smi 1))

#guard specLastIndexOf cmp (.smi 1) 2 (some .negInf) (smis [1, 2]) == -1

#guard isGeneric (run 2 none { mk .packedSmi (smis [1, 2]) with forRead := false } (.smi 1))

end ArrayLastIndexOf.Examples
