import ArrayWitness

namespace ArrayForEach

open Torque ArrayWitness

abbrev Callback := Nat → Val → JSArr → Post Unit

def body (cb : Callback) : Unit → Nat → Option Val → JSArr → Body Unit JSArr
  | _, _, none, a => .next ⟨(), a, true⟩
  | _, k, some v, a =>
    let p := cb k v a
    .next ⟨(), p.arr, p.recheck⟩

def fastForEach (cfg : Config) (cb : Callback) (a : JSArr) : Res Unit JSArr :=
  if cfg.smiMax < a.length then .bailout (forward a.length) ⟨(), a, true⟩
  else if a.fast = false then .bailout (forward a.length) ⟨(), a, true⟩
  else loop a.kind.isDouble (body cb) (fun s => .done s.arr) (forward a.length) ⟨(), a, true⟩

def specBody (cb : Callback) : Unit → Nat → Option Val → JSArr → SBody Unit JSArr
  | _, _, none, a => .next () a
  | _, k, some v, a => .next () (cb k v a).arr

def specForEach (cb : Callback) (a : JSArr) : JSArr :=
  spec (specBody cb) (fun _ a => a) (forward a.length) () a

end ArrayForEach
