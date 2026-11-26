import ArrayWitness

namespace ArrayReduceRight

open Torque ArrayWitness

abbrev Callback := Nat → Val × Val → JSArr → Post Val

def body (cb : Callback) : Option Val → Nat → Option Val → JSArr → Body (Option Val) (Option Val)
  | acc, _, none, a => .next ⟨acc, a, true⟩
  | none, _, some v, a => .next ⟨some v, a, true⟩
  | some c, k, some v, a =>
    let p := cb k (c, v) a
    .next ⟨some p.res, p.arr, p.recheck⟩

def fastReduceRight (cfg : Config) (cb : Callback) (a : JSArr) (init : Option Val) :
    Res (Option Val) (Option Val) :=
  if cfg.smiMax < a.length then .bailout (backward a.length) ⟨init, a, true⟩
  else if a.forRead = false then .bailout (backward a.length) ⟨init, a, true⟩
  else loop a.kind.isDouble (body cb) (fun s => .done s.acc) (backward a.length) ⟨init, a, true⟩

def specBody (cb : Callback) :
    Option Val → Nat → Option Val → JSArr → SBody (Option Val) (Option Val)
  | acc, _, none, a => .next acc a
  | none, _, some v, a => .next (some v) a
  | some c, k, some v, a =>
    let p := cb k (c, v) a
    .next (some p.res) p.arr

def accumulate (cb : Callback) : List Nat → Val → JSArr → Val
  | [], c, _ => c
  | k :: ks, c, a =>
    match get a k with
    | none => accumulate cb ks c a
    | some v => accumulate cb ks (cb k (c, v) a).res (cb k (c, v) a).arr

def search (cb : Callback) : List Nat → JSArr → Option Val
  | [], _ => none
  | k :: ks, a =>
    match get a k with
    | none => search cb ks a
    | some v => some (accumulate cb ks v a)

def specReduceRight (cb : Callback) (a : JSArr) (init : Option Val) : Option Val :=
  match init with
  | some c => some (accumulate cb (backward a.length) c a)
  | none => search cb (backward a.length) a

end ArrayReduceRight
