import ArrayWitness

namespace ArrayFind

open Torque ArrayWitness

abbrev Callback := Nat → Option Val → JSArr → Post Bool

def body (cb : Callback) : Unit → Nat → Option Val → JSArr → Body Unit (Option Val)
  | _, k, x, a =>
    let p := cb k x a
    if p.res then .stop x else .next ⟨(), p.arr, p.recheck⟩

def fastFind (cfg : Config) (cb : Callback) (a : JSArr) : Res Unit (Option Val) :=
  if cfg.smiMax < a.length then .bailout (forward a.length) ⟨(), a, true⟩
  else if a.fast = false then .bailout (forward a.length) ⟨(), a, true⟩
  else loop a.kind.isDouble (body cb) (fun _ => .done none) (forward a.length) ⟨(), a, true⟩

def specBody (cb : Callback) : Unit → Nat → Option Val → JSArr → SBody Unit (Option Val)
  | _, k, x, a =>
    let p := cb k x a
    if p.res then .stop x else .next () p.arr

def specFind (cb : Callback) (a : JSArr) : Option Val :=
  spec (specBody cb) (fun _ _ => none) (forward a.length) () a

end ArrayFind
