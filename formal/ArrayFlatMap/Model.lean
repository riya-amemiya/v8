import ArrayWitness

namespace ArrayFlatMap

open Torque ArrayWitness

inductive Mapped where
  | value (v : Val)
  | array (e : JSArr)
  | proxy (vals : List Val)
  deriving Repr

abbrev Callback := Nat → Val → JSArr → Post Mapped

def innerLoad (e : JSArr) : Nat → Option (Option Val)
  | k => if k < e.length then e.store[k]? else none

def innerLoop (e : JSArr) : List Nat → Option (List Val)
  | [] => some []
  | k :: ks =>
    match innerLoad e k with
    | none => none
    | some x =>
      match innerLoop e ks with
      | none => none
      | some rest => some (x.toList ++ rest)

def innerFlatten (e : JSArr) : Option (List Val) :=
  if e.fast = true then innerLoop e (forward e.length) else some (e.elems.filterMap id)

def appended : Mapped → Option (List Val)
  | .value v => some [v]
  | .array e => innerFlatten e
  | .proxy vals => some vals

def body (cb : Callback) : List Val → Nat → Option Val → JSArr → Body (List Val) (List Val)
  | out, _, none, a => .next ⟨out, a, true⟩
  | out, k, some v, a =>
    let p := cb k v a
    match appended p.res with
    | some xs => .next ⟨out ++ xs, p.arr, p.recheck⟩
    | none => .fatal

inductive Result where
  | done (out : List Val)
  | bailout (ks : List Nat) (out : List Val) (arr : JSArr)
  | fatal
  | ub
  deriving Repr

def fastFlatMap (smiMax : Nat) (cb : Callback) (a : JSArr) : Result :=
  if a.fast = false ∨ smiMax < a.length then .bailout (forward a.length) [] a
  else
    match loop a.kind.isDouble (body cb) (fun s => .done s.acc) (forward a.length)
        ⟨[], a, true⟩ with
    | .done r => .done r
    | .bailout ks s => .bailout ks s.acc s.arr
    | .fatal => .fatal
    | .ub => .ub

def specAppended : Mapped → List Val
  | .value v => [v]
  | .array e => e.elems.filterMap id
  | .proxy vals => vals

def specBody (cb : Callback) : List Val → Nat → Option Val → JSArr → SBody (List Val) (List Val)
  | out, _, none, a => .next out a
  | out, k, some v, a =>
    let p := cb k v a
    .next (out ++ specAppended p.res) p.arr

def specFlatMap (cb : Callback) (a : JSArr) : List Val :=
  spec (specBody cb) (fun out _ => out) (forward a.length) [] a

def MappedOK : Mapped → Prop
  | .array e => e.WF
  | _ => True

end ArrayFlatMap
