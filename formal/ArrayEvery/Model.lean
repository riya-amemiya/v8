import ArrayWitness

namespace ArrayEvery

open Torque ArrayWitness

abbrev Callback := Nat → Val → JSArr → Post Bool

def body (cb : Callback) : Unit → Nat → Option Val → JSArr → Body Unit Bool
  | _, _, none, a => .next ⟨(), a, true⟩
  | _, k, some v, a =>
    let p := cb k v a
    if p.res then .next ⟨(), p.arr, p.recheck⟩ else .stop false

def fastEvery (cfg : Config) (cb : Callback) (a : JSArr) : Res Unit Bool :=
  if cfg.smiMax < a.length then .bailout (forward a.length) ⟨(), a, true⟩
  else if a.fast = false then .bailout (forward a.length) ⟨(), a, true⟩
  else loop a.kind.isDouble (body cb) (fun _ => .done true) (forward a.length) ⟨(), a, true⟩

def specBody (cb : Callback) : Unit → Nat → Option Val → JSArr → SBody Unit Bool
  | _, _, none, a => .next () a
  | _, k, some v, a =>
    let p := cb k v a
    if p.res then .next () p.arr else .stop false

def specEvery (cb : Callback) (a : JSArr) : Bool :=
  spec (specBody cb) (fun _ _ => true) (forward a.length) () a

end ArrayEvery
