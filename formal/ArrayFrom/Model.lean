import ArrayBuild

namespace ArrayFrom

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

def ofClone : CloneResult → Result
  | .done a => .done a
  | .ub => .ub

def fromFastArray (a : JSArr) : Result := ofClone (cloneFastJSArray true a)

def isLead (u : Nat) : Bool := 0xD800 ≤ u && u ≤ 0xDBFF

def isTrail (u : Nat) : Bool := 0xDC00 ≤ u && u ≤ 0xDFFF

def codePoints : List Nat → List (List Nat)
  | [] => []
  | [u] => [[u]]
  | u :: w :: rest => if isLead u && isTrail w then [u, w] :: codePoints rest
    else [u] :: codePoints (w :: rest)

def writeAt (store : List (Option Val)) (n : Nat) : Option (List (Option Val)) :=
  if n < store.length then some (store.set n (some .other)) else none

def stringLoop : List Nat → Nat → List (Option Val) → List (List Nat) →
    Option (Nat × List (Option Val) × List (List Nat))
  | [], n, store, out => some (n, store, out)
  | [u], n, store, out => (writeAt store n).map fun s => (n + 1, s, out ++ [[u]])
  | u :: w :: rest, n, store, out =>
    match writeAt store n with
    | none => none
    | some s =>
      if isLead u && isTrail w then stringLoop rest (n + 1) s (out ++ [[u, w]])
      else stringLoop (w :: rest) (n + 1) s (out ++ [[u]])

def stringToList (c : Config) (units : List Nat) : Result × List (List Nat) :=
  match stringLoop units 0 (List.replicate units.length none) [] with
  | none => (.fatal, [])
  | some (n, store, out) => (.done ⟨.packedElem, c.noElements, c.noElements, false, false, n, store⟩, out)

def allocated (c : Config) (n : Nat) : JSArr :=
  ⟨.packedSmi, c.noElements, c.noElements, false, false, 0, List.replicate n none⟩

def fromIterable (c : Config) (rt : JSArr → Nat → Val → JSArr) (ctor : Ctor) (a0 : JSArr)
    (values : List Val) : Result :=
  if ctor = .otherConstructor then .generic else ofLoop (createLoop c.store rt a0 0 values)

def fromArrayLike (c : Config) (rt : JSArr → Nat → Val → JSArr) (ctor : Ctor)
    (create : Nat → JSArr) (values : List Val) : Result :=
  if ctor = .otherConstructor then .generic
  else
    ofLoop (createLoop c.store rt
      (if ctor = .arrayFunction ∧ values.length ≤ c.maxFast then allocated c values.length
        else create values.length) 0 values)

def iterated (a : JSArr) : List (Option Val) := a.elems.map holeToUndef

end ArrayFrom
