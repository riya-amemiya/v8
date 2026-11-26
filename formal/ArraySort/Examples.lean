import ArraySort.Safety

namespace ArraySort.Examples

open Torque ArraySort

def cfg : Cfg := ⟨1073741823, 33554432, false⟩

def smis (l : List Int) : List (Option Val) := l.map (fun n => some (.smi n))

def fastArr (kind : Kind) (store : List (Option Val)) : JSArr :=
  ⟨kind, true, true, false, false, store.length, store⟩

def slowArr (store : List (Option Val)) : JSArr :=
  ⟨.slow, false, false, false, false, store.length, store⟩

def recvOf (a : JSArr) : Recv := ⟨1, true, true, a⟩

def setAt (r : Recv) (i : Nat) (x : Option Val) : Recv :=
  let s := if i < r.arr.store.length then r.arr.store
    else r.arr.store ++ List.replicate (i + 1 - r.arr.store.length) none
  { r with arr := { r.arr with store := s.set i x, length := max r.arr.length (i + 1) } }

def keyOf : Val → Int
  | .smi a => a
  | _ => 0

def withCall (call : Nat → Recv → Val → Val → Option (Num × Recv)) : Env where
  call := call
  str := fun _ r _ _ => some (0, r)
  load := fun _ _ r i => some (r.arr.store.getD i none, r)
  set := fun _ r i v => some (setAt r i (some v))
  del := fun _ r i => some (setAt r i none)
  toNum := fun _ r _ => some r

def numEnv : Env := withCall fun _ r x y => some (.fin (keyOf x - keyOf y), r)

def bucketEnv : Env := withCall fun _ r x y => some (.fin (keyOf x / 100 - keyOf y / 100), r)

def chaosEnv : Env := withCall fun t r _ _ => some (if t % 5 = 0 then .nan else .fin ((t * 7919 % 11 : Nat) - 5), r)

def throwEnv : Env := withCall fun t r x y => if t = 10 then none else some (.fin (keyOf x - keyOf y), r)

def shrinkEnv : Env := withCall fun t r x y =>
  if t = 0 then some (.fin (keyOf x - keyOf y), { r with arr := { r.arr with length := 0, store := [] } })
  else some (.fin (keyOf x - keyOf y), r)

def remapEnv : Env := withCall fun t r x y =>
  if t = 3 then some (.fin (keyOf x - keyOf y), { r with map := 2 }) else some (.fin (keyOf x - keyOf y), r)

def isSafe {ρ : Type} : Result ρ → Bool
  | .ub => false
  | .abort => false
  | _ => true

def isThrow {ρ : Type} : Result ρ → Bool
  | .throws _ => true
  | _ => false

def store? : Result Unit → Option (List (Option Val))
  | .done _ e => some e.recv.arr.store
  | _ => none

def log? : Result Unit → Option (List WB)
  | .done _ e => some e.log
  | _ => none

def ticks? {ρ : Type} : Result ρ → Option Nat
  | .done _ e => some e.tick
  | _ => none

def copy? : Result JSArr → Option (Kind × List (Option Val))
  | .done a _ => some (a.kind, a.store)
  | _ => none

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

def rnd (n s : Nat) : List Int := (List.range n).map fun i => ((lcg (s + i * 7919) % 1000 : Nat) : Int)

def sortFast (env : Env) (arg : CmpArg) (l : List Int) : Result Unit :=
  arraySort cfg env arg (recvOf (fastArr .packedSmi (smis l))) l.length

def sortSlow (env : Env) (arg : CmpArg) (l : List Int) : Result Unit :=
  arraySort cfg env arg (recvOf (slowArr (smis l))) l.length

def msort (l : List Int) : List Int := l.mergeSort fun a b => a ≤ b

def keys (s : List (Option Val)) : List Int := s.filterMap fun x => x.map keyOf

#guard store? (sortFast numEnv .fn [5, 3, 1, 4, 2]) == some (smis [1, 2, 3, 4, 5])

#guard store? (sortFast numEnv .undef [10, 9, 1, 100]) == some (smis [1, 10, 100, 9])

#guard store? (sortSlow numEnv .fn [5, 3, 1, 4, 2]) == some (smis [1, 2, 3, 4, 5])

#guard log? (sortSlow numEnv .fn [2, 1]) == some [.store 0 (.smi 1), .store 1 (.smi 2)]

#guard store? (arraySort cfg numEnv .fn
    (recvOf (fastArr .holeyElem [some (.smi 3), none, some .undef, some (.smi 1), none])) 5) ==
  some [some (.smi 1), some (.smi 3), some .undef, none, none]

#guard log? (arraySort cfg numEnv .fn
    (recvOf (fastArr .holeyElem [some (.smi 3), none, some .undef, some (.smi 1), none])) 5) ==
  some (writeLog [.smi 1, .smi 3] 1 5)

#guard store? (arraySort cfg numEnv .fn
    (recvOf (slowArr [some (.smi 3), none, some .undef, some (.smi 1), none])) 5) ==
  some [some (.smi 1), some (.smi 3), some .undef, none, none]

#guard store? (sortFast numEnv .fn (rnd 15 2)) == some (smis (msort (rnd 15 2)))

#guard store? (sortFast numEnv .fn (rnd 300 7)) == some (smis (msort (rnd 300 7)))

#guard store? (sortFast numEnv .fn (rnd 1000 11)) == some (smis (msort (rnd 1000 11)))

def iota (n : Nat) : List Int := (List.range n).map fun i : Nat => (i : Int)

def runs2 : List Int := (iota 64).map (· + 64) ++ iota 64

#guard store? (sortFast numEnv .fn runs2) == some (smis (msort runs2))

#guard (ticks? (sortFast numEnv .fn runs2)).all (· < 160)

def runs2Big : List Int := (iota 256).map (· + 256) ++ iota 256

#guard store? (sortFast numEnv .fn runs2Big) == some (smis (msort runs2Big))

#guard (ticks? (sortFast numEnv .fn runs2Big)).all (· < 600)

def zipped : List Int := (iota 64).map (· * 2) ++ (iota 64).map (· * 2 + 1)

#guard store? (sortFast numEnv .fn zipped) == some (smis (msort zipped))

#guard (ticks? (sortFast numEnv .fn zipped)).all (· ≥ 250)

def interleaved : List Int :=
  iota 40 ++ (iota 40).map (· * 3 + 1000) ++ (iota 40).map (· + 40) ++ (iota 40).map (· * 3 + 1001)

#guard store? (sortFast numEnv .fn interleaved) == some (smis (msort interleaved))

#guard store? (sortFast bucketEnv .fn (rnd 400 3)) ==
  some (smis ((rnd 400 3).mergeSort fun a b => a / 100 ≤ b / 100))

#guard isSafe (sortFast chaosEnv .fn (rnd 500 5))

#guard (store? (sortFast chaosEnv .fn (rnd 500 5))).map (fun s => msort (keys s)) == some (msort (rnd 500 5))

#guard isSafe (sortSlow chaosEnv .fn (rnd 200 9))

#guard (store? (sortSlow chaosEnv .fn (rnd 200 9))).map (fun s => msort (keys s)) == some (msort (rnd 200 9))

#guard isThrow (sortFast throwEnv .fn (rnd 100 1))

#guard isSafe (sortFast throwEnv .fn (rnd 100 1))

#guard store? (sortFast shrinkEnv .fn [5, 3, 1, 4, 2]) == some (smis [1, 2, 3, 4, 5])

#guard log? (sortFast shrinkEnv .fn [5, 3, 1, 4, 2]) == some (writeLog [.smi 1, .smi 2, .smi 3, .smi 4, .smi 5] 0 5)

#guard store? (sortFast shrinkEnv .fn (rnd 100 4)) == some (smis (msort (rnd 100 4)))

#guard store? (sortFast remapEnv .fn (rnd 50 6)) == some (smis (msort (rnd 50 6)))

#guard isSafe (arraySort cfg numEnv .other (recvOf (fastArr .packedSmi (smis [2, 1]))) 2)

#guard copy? (arrayToSorted cfg numEnv .fn (recvOf (fastArr .packedSmi (smis [3, 1, 2]))) 3) ==
  some (.packedSmi, smis [1, 2, 3])

#guard copy? (arrayToSorted cfg numEnv .fn
    (recvOf (fastArr .holeyElem [some (.smi 2), none, some .undef, some (.smi 1)])) 4) ==
  some (.packedElem, [some (.smi 1), some (.smi 2), some .undef, some .undef])

#guard copy? (arrayToSorted cfg numEnv .fn (recvOf (fastArr .packedElem [some (.smi 2), some .other])) 2) ==
  some (.packedElem, [some .other, some (.smi 2)])

#guard copy? (arrayToSorted cfg numEnv .fn (recvOf (slowArr (smis (rnd 200 8)))) 200) ==
  some (.packedSmi, smis (msort (rnd 200 8)))

#guard copy? (arrayToSorted ⟨1073741823, 4, false⟩ numEnv .fn (recvOf (fastArr .packedSmi (smis [3, 1, 2, 5, 4]))) 5) ==
  some (.slow, smis [1, 2, 3, 4, 5])

#guard isSafe (arrayToSorted cfg chaosEnv .fn (recvOf (fastArr .packedSmi (smis (rnd 300 2)))) 300)

def snapRecv : Ext := ⟨recvOf (fastArr .packedSmi (smis [9, 9, 9])), 0, []⟩

#guard log? (continueFromSnapshot cfg numEnv true snapRecv (smis [3, 1, 2]) 3) ==
  some (writeLog [.smi 1, .smi 2, .smi 3] 0 3)

#guard store? (continueFromSnapshot cfg numEnv true snapRecv (smis [3, 1, 2]) 3) == some (smis [1, 2, 3])

#guard store? (continueFromSnapshot cfg numEnv true snapRecv (smis (rnd 16 3) ++ [none, none]) 16) ==
  some (smis (msort (rnd 16 3)))

#guard isSafe (continueFromSnapshot cfg chaosEnv true snapRecv (smis (rnd 16 5)) 16)

#guard log? (continueAfterCallback cfg numEnv true (recvOf (fastArr .packedSmi (smis [9, 9, 9])))
    (smis [3, 1, 2]) 3 .undef) == some (writeLog [.smi 1, .smi 2, .smi 3] 0 3)

#guard ((List.range 40).all fun n => (List.range n).all fun s1 => (List.range n).all fun n1 =>
  (List.range n).all fun n2 =>
    !(0 < n1 && 0 < n2 && s1 + n1 + n2 ≤ n) ||
      nodePower32 s1 n1 n2 n == nodePowerValue s1 n1 n2 n)

#guard (List.range 200).all fun k =>
  let n := 1000003 + k * 4099
  let s1 := k * 31
  let n1 := 1 + k * 17
  let n2 := 1 + k * 13
  nodePower32 s1 n1 n2 n == nodePowerValue s1 n1 n2 n

end ArraySort.Examples
