import ArrayWitness

namespace ArrayFindLast

open Torque ArrayWitness

abbrev Callback := Nat → Option Val → JSArr → Post Bool

def body (cb : Callback) : Unit → Nat → Option Val → JSArr → Body Unit (Option Val)
  | _, k, x, a =>
    let p := cb k x a
    if p.res then .stop x else .next ⟨(), p.arr, p.recheck⟩

def fastFindLast (cfg : Config) (cb : Callback) (a : JSArr) : Res Unit (Option Val) :=
  if cfg.smiMax < a.length then .bailout (backward a.length) ⟨(), a, true⟩
  else if a.fast = false then .bailout (backward a.length) ⟨(), a, true⟩
  else loop a.kind.isDouble (body cb) (fun _ => .done none) (backward a.length) ⟨(), a, true⟩

def specBody (cb : Callback) : Unit → Nat → Option Val → JSArr → SBody Unit (Option Val)
  | _, k, x, a =>
    let p := cb k x a
    if p.res then .stop x else .next () p.arr

def specFindLast (cb : Callback) (a : JSArr) : Option Val :=
  spec (specBody cb) (fun _ _ => none) (backward a.length) () a

end ArrayFindLast
