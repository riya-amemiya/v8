import ArrayBuild

namespace ArrayOf

open Torque ArrayBuild

structure Config where
  maxFast : Nat
  noElements : Bool
  store : StoreEnv

inductive Ctor where
  | arrayFunction
  | otherConstructor
  | notConstructor
  deriving DecidableEq, Repr

inductive Result where
  | done (a : JSArr)
  | generic
  | ub
  | fatal
  deriving Repr

def ofLoop : LoopResult → Result
  | .done a => .done a
  | .ub => .ub
  | .fatal => .fatal

def filledWithZero (c : Config) (n : Nat) : JSArr :=
  if n = 0 then ⟨.packedSmi, c.noElements, c.noElements, false, false, 0, []⟩
  else ⟨.packedSmi, c.noElements, c.noElements, false, false, n, List.replicate n (some (.smi 0))⟩

def initial (c : Config) (ctor : Ctor) (create : Nat → JSArr) (n : Nat) : JSArr :=
  if ctor = .arrayFunction ∧ n ≤ c.maxFast then filledWithZero c n else create n

def arrayOf (c : Config) (rt : JSArr → Nat → Val → JSArr) (ctor : Ctor) (create : Nat → JSArr)
    (items : List Val) : Result :=
  if ctor = .otherConstructor then .generic
  else ofLoop (createLoop c.store rt (initial c ctor create items.length) 0 items)

end ArrayOf
