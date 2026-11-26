import ArrayJoin.GenericSafety
import ArrayJoin.Stack

namespace ArrayJoin

open Torque

def joinImpl {σ : Type} (l : Limits) (conv : Val → Option (Option Str)) (fastCast : σ → Option JSArr)
    (fallback : σ → Res (List Nat × σ)) (sep : Str) (len : Nat) (w : σ) : Res (List Nat × σ) :=
  if len ≤ l.smiMax ∧ len ≤ l.strMax then
    match fastCast w with
    | some a =>
      match fastArrayJoin l conv a sep len with
      | .ok s => .ok (s, w)
      | .bailout => fallback w
      | .throws => .throws
      | .ub => .ub
      | .fatal => .fatal
    | none => fallback w
  else fallback w

def cycleProtected {σ R : Type} (l : Limits) (L : Lens σ) (r : Nat) (sep : Str) (len : Nat)
    (empty : R) (inner : σ → Out σ R) (w : σ) : Out σ R :=
  if earlyThrow l sep len then .thrown w else cycleJoin L r len empty inner w

def arrayPrototypeJoin {σ : Type} (l : Limits) (getLen : σ → Option (Nat × σ))
    (toSep : σ → Option (Str × σ)) (impl : Str → Nat → σ → Res (List Nat × σ)) (w : σ) :
    Res (List Nat × σ) :=
  match getLen w with
  | none => .throws
  | some (len, w1) =>
    if l.maxArray < len then .throws
    else
      match toSep w1 with
      | none => .throws
      | some (sep, w2) => if len = 0 then .ok ([], w2) else impl sep len w2

def comma : Str := ⟨0, [44]⟩

def toStringInline {σ : Type} (l : Limits) (len : Nat) (impl : Str → Nat → σ → Res (List Nat × σ))
    (w : σ) : Res (List Nat × σ) :=
  if len = 0 then .ok ([], w) else if l.maxArray < len then .throws else impl comma len w

def arrayPrototypeToString {σ : Type} (getJoin : σ → Option (Option (σ → Res (List Nat × σ)) × σ))
    (objectToString : σ → Res (List Nat × σ)) (w : σ) : Res (List Nat × σ) :=
  match getJoin w with
  | none => .throws
  | some (some f, w1) => f w1
  | some (none, w1) => objectToString w1

def arrayPrototypeToLocaleString {σ : Type} (l : Limits) (getLen : σ → Option (Nat × σ))
    (cycle : Str → Nat → σ → Out σ (List Nat)) (w : σ) : Out σ (List Nat) :=
  match getLen w with
  | none => .thrown w
  | some (len, w1) => if l.maxArray < len then .thrown w1 else cycle comma len w1

theorem earlyThrow_false {l : Limits} {sep : Str} {len : Nat} (h : earlyThrow l sep len = false) :
    sep.len * (len - 1) ≤ l.strMax := by
  unfold earlyThrow at h
  simp only [decide_eq_false_iff_not, not_and, not_or] at h
  by_cases hs : 1 ≤ sep.len
  · obtain ⟨_, h2⟩ := h hs
    by_cases h1 : 1 < len
    · rw [Nat.mul_comm]
      exact Nat.le_of_not_lt (h2 h1)
    · have : len - 1 = 0 := by omega
      rw [this, Nat.mul_zero]
      exact Nat.zero_le _
  · have : sep.len = 0 := by omega
    rw [this, Nat.zero_mul]
    exact Nat.zero_le _

theorem cycleProtected_preserves {σ R : Type} (l : Limits) (L : Lens σ) {act : List Nat}
    {r : Nat} (sep : Str) (len : Nat) (empty : R) {inner : σ → Out σ R}
    (hin : r ∉ act → Preserves L (act ++ [r]) inner) :
    Preserves L act (cycleProtected l L r sep len empty inner) := by
  intro w hw
  unfold cycleProtected
  split
  · exact Or.inr ⟨w, rfl, hw⟩
  · exact cycleJoin_preserves L empty hin w hw

theorem joinImpl_spec {σ : Type} {l : Limits} (hl : l.OK) (conv : Val → Option (Option Str))
    {fastCast : σ → Option JSArr} (hcast : ∀ w a, fastCast w = some a → a.WF ∧ a.kind.isFast = true)
    {fallback : σ → Res (List Nat × σ)} (sep : Str) (len : Nat) (w : σ) :
    joinImpl l conv fastCast fallback sep len w = .throws ∨
      joinImpl l conv fastCast fallback sep len w = fallback w ∨
      ∃ a, fastCast w = some a ∧
        joinImpl l conv fastCast fallback sep len w = .ok (fastSpec conv a sep.chars len, w) := by
  unfold joinImpl
  split
  · rename_i hlen
    split
    · rename_i a ha
      obtain ⟨hw, hf⟩ := hcast w a ha
      rcases fastArrayJoin_spec hl conv hw hf sep hlen.2 with h | h | h
      · rw [h]
        exact Or.inl rfl
      · rw [h]
        exact Or.inr (Or.inl rfl)
      · rw [h]
        exact Or.inr (Or.inr ⟨a, ha, rfl⟩)
    · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)

theorem joinImpl_safe {σ : Type} {l : Limits} (hl : l.OK) (conv : Val → Option (Option Str))
    {fastCast : σ → Option JSArr} (hcast : ∀ w a, fastCast w = some a → a.WF ∧ a.kind.isFast = true)
    {fallback : σ → Res (List Nat × σ)} (hfb : ∀ w, (fallback w).Safe) (sep : Str) (len : Nat)
    (w : σ) : (joinImpl l conv fastCast fallback sep len w).Safe := by
  rcases joinImpl_spec hl conv hcast (fallback := fallback) sep len w with h | h | ⟨a, _, h⟩
  · rw [h]
    trivial
  · rw [h]
    exact hfb w
  · rw [h]
    trivial

theorem arrayPrototypeJoin_safe {σ : Type} (l : Limits) (getLen : σ → Option (Nat × σ))
    (toSep : σ → Option (Str × σ)) {impl : Str → Nat → σ → Res (List Nat × σ)}
    (himpl : ∀ sep len w, 0 < len → len ≤ l.maxArray → (impl sep len w).Safe) (w : σ) :
    (arrayPrototypeJoin l getLen toSep impl w).Safe := by
  unfold arrayPrototypeJoin
  split
  · trivial
  · rename_i len w1 _
    split
    · trivial
    · rename_i hmax
      split
      · trivial
      · rename_i sep w2 _
        split
        · trivial
        · rename_i h0
          exact himpl sep len w2 (by omega) (by omega)

theorem toStringInline_eq {σ : Type} (l : Limits) (len : Nat)
    (impl : Str → Nat → σ → Res (List Nat × σ)) (w : σ) :
    toStringInline l len impl w =
      arrayPrototypeJoin l (fun w => some (len, w)) (fun w => some (comma, w)) impl w := by
  unfold toStringInline arrayPrototypeJoin
  dsimp only
  by_cases h0 : len = 0
  · rw [ite_eq_left h0, ite_eq_right (by omega), ite_eq_left h0]
  · rw [ite_eq_right h0]
    by_cases hm : l.maxArray < len
    · rw [ite_eq_left hm, ite_eq_left hm]
    · rw [ite_eq_right hm, ite_eq_right hm, ite_eq_right h0]

theorem inner_spec {σ : Type} {l : Limits} (hl : l.OK) {env : Env σ}
    (hwf : ∀ w, (env.arr w).WF) (rc : Receiver σ) {sep : Str} {len : Nat} (w : σ)
    (h : earlyThrow l sep len = false) :
    arrayJoin l env rc sep len w = .throws ∨
      ∃ s w' log, arrayJoin l env rc sep len w = .ok (s, w', log) ∧
        s = joinPieces sep.chars log ∧ log.length = len :=
  arrayJoin_spec hl hwf rc w (earlyThrow_false h)

end ArrayJoin
