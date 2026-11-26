import Torque

namespace ArrayWitness

open Torque

structure Post (ρ : Type) where
  res : ρ
  arr : JSArr
  sameMap : Bool
  protector : Bool

def Post.recheck {ρ : Type} (p : Post ρ) : Bool := p.sameMap && p.protector

def CallbackOk {ι ρ : Type} (kind : Kind) (cb : Nat → ι → JSArr → Post ρ) : Prop :=
  ∀ k x a, (cb k x a).arr.WF ∧ ((cb k x a).sameMap = true → (cb k x a).arr.kind = kind)

def get (a : JSArr) (k : Nat) : Option Val := a.elems.getD k none

def load (hasDoubles : Bool) (a : JSArr) (k : Nat) : Option (Option Val) :=
  if hasDoubles = a.kind.isDouble then a.store[k]? else none

structure St (α : Type) where
  acc : α
  arr : JSArr
  ok : Bool

inductive Body (α ρ : Type) where
  | next (s : St α)
  | stop (r : ρ)
  | fatal
  | ub

inductive Res (α ρ : Type) where
  | done (r : ρ)
  | bailout (ks : List Nat) (s : St α)
  | fatal
  | ub

abbrev BodyFn (α ρ : Type) := α → Nat → Option Val → JSArr → Body α ρ

abbrev FinFn (α ρ : Type) := St α → Res α ρ

def loop {α ρ : Type} (hd : Bool) (body : BodyFn α ρ) (fin : FinFn α ρ) :
    List Nat → St α → Res α ρ
  | [], s => fin s
  | k :: ks, s =>
    if s.ok = false then .bailout (k :: ks) s
    else if s.arr.length ≤ k then .bailout (k :: ks) s
    else match load hd s.arr k with
      | none => .fatal
      | some x =>
        match body s.acc k x s.arr with
        | .next s' => loop hd body fin ks s'
        | .stop r => .done r
        | .fatal => .fatal
        | .ub => .ub

def forward (len : Nat) : List Nat := List.range' 0 len

def backward (len : Nat) : List Nat := (List.range len).reverse

inductive SBody (β σ : Type) where
  | next (b : β) (arr : JSArr)
  | stop (r : σ)

abbrev SBodyFn (β σ : Type) := β → Nat → Option Val → JSArr → SBody β σ

abbrev SFinFn (β σ : Type) := β → JSArr → σ

def spec {β σ : Type} (sbody : SBodyFn β σ) (sfin : SFinFn β σ) : List Nat → β → JSArr → σ
  | [], b, a => sfin b a
  | k :: ks, b, a =>
    match sbody b k (get a k) a with
    | .next b' a' => spec sbody sfin ks b' a'
    | .stop r => r

inductive Reaches {β σ : Type} (sbody : SBodyFn β σ) :
    List Nat → β → JSArr → List Nat → β → JSArr → Prop
  | refl (ks : List Nat) (b : β) (a : JSArr) : Reaches sbody ks b a ks b a
  | step {k : Nat} {ks ks' : List Nat} {b b' b'' : β} {a a' a'' : JSArr} :
      sbody b k (get a k) a = .next b' a' → Reaches sbody ks b' a' ks' b'' a'' →
      Reaches sbody (k :: ks) b a ks' b'' a''

end ArrayWitness
