import ArrayWitness

namespace ArrayFindLastIndex

open Torque ArrayWitness

abbrev Callback := Nat → Option Val → JSArr → Post Bool

def body (cb : Callback) : Unit → Nat → Option Val → JSArr → Body Unit Int
  | _, k, x, a =>
    let p := cb k x a
    if p.res then .stop k else .next ⟨(), p.arr, p.recheck⟩

def fastFindLastIndex (cfg : Config) (cb : Callback) (a : JSArr) : Res Unit Int :=
  if cfg.smiMax < a.length then .bailout (backward a.length) ⟨(), a, true⟩
  else if a.fast = false then .bailout (backward a.length) ⟨(), a, true⟩
  else loop a.kind.isDouble (body cb) (fun _ => .done (-1)) (backward a.length) ⟨(), a, true⟩

def specBody (cb : Callback) : Unit → Nat → Option Val → JSArr → SBody Unit Int
  | _, k, x, a =>
    let p := cb k x a
    if p.res then .stop k else .next () p.arr

def specFindLastIndex (cb : Callback) (a : JSArr) : Int :=
  spec (specBody cb) (fun _ _ => -1) (backward a.length) () a

end ArrayFindLastIndex
