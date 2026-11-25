namespace Torque

inductive Step (σ ρ : Type) where
  | cont (s : σ)
  | done (r : ρ)
  | bailout
  | throwRange
  | ub

inductive Outcome (ρ : Type) where
  | ok (r : ρ)
  | bailout
  | throwRange
  | ub
  | fatal
  deriving Repr

def Step.result {σ ρ : Type} : Step σ ρ → Option (Outcome ρ)
  | .cont _ => none
  | .done r => some (.ok r)
  | .bailout => some .bailout
  | .throwRange => some .throwRange
  | .ub => some .ub

def run {σ ρ : Type} (step : σ → Step σ ρ) (μ : σ → Nat)
    (hdec : ∀ s s', step s = .cont s' → μ s' < μ s) (s : σ) : Outcome ρ :=
  match h : step s with
  | .cont s' =>
    have : μ s' < μ s := hdec s s' h
    run step μ hdec s'
  | .done r => .ok r
  | .bailout => .bailout
  | .throwRange => .throwRange
  | .ub => .ub
termination_by μ s

inductive Reach {σ ρ : Type} (step : σ → Step σ ρ) : σ → σ → Prop
  | refl (s : σ) : Reach step s s
  | next {s t u : σ} : step s = .cont t → Reach step t u → Reach step s u

theorem Reach.invariant {σ ρ : Type} {step : σ → Step σ ρ} {P : σ → Prop}
    (hpres : ∀ s t, P s → step s = .cont t → P t) {s u : σ} (hr : Reach step s u)
    (hs : P s) : P u := by
  induction hr with
  | refl => exact hs
  | next hst _ ih => exact ih (hpres _ _ hs hst)

theorem Reach.backward {σ ρ : Type} {step : σ → Step σ ρ} {P : σ → Prop}
    (hback : ∀ s t, step s = .cont t → P t → P s) {s u : σ} (hr : Reach step s u)
    (hu : P u) : P s := by
  induction hr with
  | refl => exact hu
  | next hst _ ih => exact hback _ _ hst (ih hu)

theorem run_spec {σ ρ : Type} (step : σ → Step σ ρ) (μ : σ → Nat)
    (hdec : ∀ s s', step s = .cont s' → μ s' < μ s) (s : σ) :
    ∃ t, Reach step s t ∧ (step t).result = some (run step μ hdec s) := by
  rw [run]
  split
  next s' h =>
    have : μ s' < μ s := hdec s s' h
    obtain ⟨t, ht, hr⟩ := run_spec step μ hdec s'
    exact ⟨t, .next h ht, hr⟩
  next r h => exact ⟨s, .refl s, by simp [h, Step.result]⟩
  next h => exact ⟨s, .refl s, by simp [h, Step.result]⟩
  next h => exact ⟨s, .refl s, by simp [h, Step.result]⟩
  next h => exact ⟨s, .refl s, by simp [h, Step.result]⟩
termination_by μ s

theorem run_ok {σ ρ : Type} {step : σ → Step σ ρ} {μ : σ → Nat}
    {hdec : ∀ s s', step s = .cont s' → μ s' < μ s} {s : σ} {r : ρ}
    (h : run step μ hdec s = .ok r) : ∃ t, Reach step s t ∧ step t = .done r := by
  obtain ⟨t, ht, hr⟩ := run_spec step μ hdec s
  rw [h] at hr
  refine ⟨t, ht, ?_⟩
  cases hs : step t <;> simp_all [Step.result]

theorem run_ub {σ ρ : Type} {step : σ → Step σ ρ} {μ : σ → Nat}
    {hdec : ∀ s s', step s = .cont s' → μ s' < μ s} {s : σ}
    (h : run step μ hdec s = .ub) : ∃ t, Reach step s t ∧ step t = .ub := by
  obtain ⟨t, ht, hr⟩ := run_spec step μ hdec s
  rw [h] at hr
  refine ⟨t, ht, ?_⟩
  cases hs : step t <;> simp_all [Step.result]

theorem run_ne_fatal {σ ρ : Type} (step : σ → Step σ ρ) (μ : σ → Nat)
    (hdec : ∀ s s', step s = .cont s' → μ s' < μ s) (s : σ) :
    run step μ hdec s ≠ .fatal := by
  intro h
  obtain ⟨t, _, hr⟩ := run_spec step μ hdec s
  rw [h] at hr
  cases hs : step t <;> simp_all [Step.result]

end Torque
