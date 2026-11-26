import InPlace

namespace ArrayUnshift

open Torque InPlace

def argsKind : Kind → List Val → Kind
  | target, [] => target
  | target, .smi _ :: rest => argsKind target rest
  | _, .num _ :: rest => argsKind .packedDouble rest
  | _, _ :: _ => .packedElem

def isObjectKind : Kind → Bool
  | .packedElem => true
  | .holeyElem => true
  | _ => false

def matchKind (c : Config) (a : JSArr) (xs : List Val) : Res JSArr :=
  if xs = [] then .ok a
  else if isObjectKind a.kind then .ok a
  else if argsKind a.kind xs = a.kind then .ok a
  else transitionTo c a (argsKind a.kind xs)

def newElementsCapacity (maxLen n : Nat) : Nat :=
  if maxLen < n + n / 2 + 16 ∧ n + 16 ≤ maxLen then maxLen else n + n / 2 + 16

def copyArguments (cow : Bool) (k : Kind) (s : List (Option Val)) (xs : List Val) :
    Res (List (Option Val)) :=
  if cow = true ∨ s.length < xs.length ∨ (k.isDouble = true ∧ xs.any (fun v => !v.isNumber)) then
    .ub
  else .ok (blit s 0 (xs.map some))

def grownStore (b : JSArr) (n cap : Nat) : List (Option Val) :=
  growTo (List.replicate n none ++ b.store.take (cap - n)) cap

def addArguments (c : Config) (b : JSArr) (xs : List Val) : Result Nat :=
  if b.store.length < b.length + xs.length then
    if c.maxLen < newElementsCapacity c.maxLen (b.length + xs.length) then .throws
    else
      let cap := newElementsCapacity c.maxLen (b.length + xs.length)
      (copyArguments false b.kind (grownStore b xs.length cap) xs).then fun s =>
        .done { b with store := s, length := b.length + xs.length, cow := false }
          (b.length + xs.length)
  else
    ((do
      let s ← memmove b.cow b.store xs.length 0 b.length
      copyArguments b.cow b.kind s xs) : Res _).then fun s =>
      .done { b with store := s, length := b.length + xs.length } (b.length + xs.length)

def unshift (c : Config) (m : MapInfo) (a : JSArr) (xs : List Val) : Result Nat :=
  if a.fast = false then .slow
  else (ensureWritableChecked c a).then fun b =>
    if m.extensible = false ∨ m.lengthWritable = false then .slow
    else (matchKind c b xs).then fun d =>
      if xs = [] then .done d d.length else addArguments c d xs

def specUnshift (xs : List (Option Val)) (items : List Val) : List (Option Val) :=
  items.map some ++ xs

end ArrayUnshift
