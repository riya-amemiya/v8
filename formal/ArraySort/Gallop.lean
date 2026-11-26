import ArraySort.Insertion

namespace ArraySort

open Torque

section

variable {ε : Type} (cmp : Cmp ε) (smiMax : Nat)

theorem gallopPhase_good {a : Arr} {key : Val} {keyFirst plus breakNeg : Bool} {base hint length : Nat}
    {c : Core} (hv : Vals (c.get a) base (base + length)) (hh : hint < length) :
    ∀ d (lastOfs offset : Nat), lastOfs < offset →
      (lastOfs : Int) < (if plus then (length : Int) - hint else (hint : Int) + 1) →
      ((if plus then (length : Int) - hint else (hint : Int) + 1) - offset).toNat = d → ∀ e,
      ((gallopPhase cmp smiMax a key keyFirst plus breakNeg (base : Int) (hint : Int)
        (if plus then (length : Int) - hint else (hint : Int) + 1) lastOfs offset) e c).Good
        (fun r _ c' => c' = c ∧ r.1 < r.2 ∧
          (r.1 : Int) < (if plus then (length : Int) - hint else (hint : Int) + 1))
  | d, lastOfs, offset, h1, h2, hd, e => by
    by_cases ho : (offset : Int) < (if plus then (length : Int) - hint else (hint : Int) + 1)
    · rw [gallopPhase, dite_eq_left ho]
      simp only [good_bind, good_ld, good_jsAny]
      have hidx : ∃ i : Nat, (if plus then (base : Int) + hint + offset else (base : Int) + hint - offset) =
          (i : Int) ∧ base ≤ i ∧ i < base + length := by
        cases plus
        · simp only [Bool.false_eq_true, ite_false] at ho ⊢
          exact ⟨base + hint - offset, by omega, by omega, by omega⟩
        · simp only [ite_true] at ho ⊢
          exact ⟨base + hint + offset, by omega, by omega, by omega⟩
      obtain ⟨i, hi, hi1, hi2⟩ := hidx
      rw [hi]
      obtain ⟨v, hv'⟩ := hv.2 i hi1 hi2
      have hl := hv.1
      refine ⟨⟨by omega, by omega⟩, v, by rw [Int.toNat_natCast]; exact hv', ?_⟩
      have hn : offset < gallopNext smiMax (if plus then (length : Int) - hint else (hint : Int) + 1) offset := by
        unfold gallopNext
        split <;> omega
      rw [good_compareKey]
      intro o e' _
      rw [good_ite]
      by_cases hb : (if breakNeg = true then decide (o < 0) else decide (0 ≤ o)) = true
      · rw [ite_eq_left hb]
        exact ⟨rfl, h1, h2⟩
      · rw [ite_eq_right hb]
        exact gallopPhase_good hv hh _ offset _ hn ho rfl e'
    · rw [gallopPhase, dite_eq_right ho]
      exact ⟨rfl, h1, h2⟩
termination_by _ _ offset => ((if plus then (length : Int) - hint else (hint : Int) + 1) - offset).toNat
decreasing_by all_goals omega

theorem gallopSearch_good {a : Arr} {key : Val} {keyFirst : Bool} {base length : Nat} {c : Core}
    (hv : Vals (c.get a) base (base + length)) :
    ∀ (lo hi : Nat), lo ≤ hi → hi ≤ length → ∀ e,
      ((gallopSearch cmp a key keyFirst (base : Int) (lo : Int) (hi : Int)) e c).Good
        (fun r _ c' => c' = c ∧ ∃ k : Nat, r = ((k : Int), (k : Int)) ∧ lo ≤ k ∧ k ≤ hi)
  | lo, hi, h1, h2, e => by
    by_cases hlh : lo < hi
    · rw [gallopSearch, dite_eq_left (by omega)]
      have hm : ((lo : Int) + ((hi : Int) - (lo : Int)) / 2) = ((lo + (hi - lo) / 2 : Nat) : Int) := by
        omega
      simp only [hm, good_bind, good_ld, good_jsAny, good_compareKey]
      obtain ⟨v, hv'⟩ := hv.2 (base + (lo + (hi - lo) / 2)) (by omega) (by omega)
      have hl := hv.1
      refine ⟨⟨by omega, by omega⟩, v, by rw [show ((base : Int) + ((lo + (hi - lo) / 2 : Nat) : Int)).toNat =
        base + (lo + (hi - lo) / 2) by omega]; exact hv', fun o e' _ => ?_⟩
      rw [good_ite]
      split
      · exact (gallopSearch_good hv lo (lo + (hi - lo) / 2) (by omega) (by omega) e').mono
          fun r _ c' ⟨hc, k, hk, hk1, hk2⟩ => ⟨hc, k, hk, hk1, by omega⟩
      · have := gallopSearch_good (key := key) (keyFirst := keyFirst) hv (lo + (hi - lo) / 2 + 1) hi
          (by omega) h2 e'
        rw [show ((lo + (hi - lo) / 2 : Nat) : Int) + 1 = ((lo + (hi - lo) / 2 + 1 : Nat) : Int) by omega]
        exact this.mono fun r _ c' ⟨hc, k, hk, hk1, hk2⟩ => ⟨hc, k, hk, by omega, hk2⟩
    · rw [gallopSearch, dite_eq_right (by omega)]
      exact ⟨rfl, lo, by rw [show hi = lo by omega], Nat.le_refl _, h1⟩
termination_by lo hi => hi - lo

theorem gallop_good {isRight : Bool} {a : Arr} {key : Val} {base length hint : Nat} {c : Core} {e : ε}
    (hv : Vals (c.get a) base (base + length)) (hh : hint < length) :
    ((gallop cmp smiMax isRight a key (base : Int) (length : Int) (hint : Int)) e c).Good
      (fun r _ c' => c' = c ∧ ∃ k : Nat, r = (k : Int) ∧ k ≤ length) := by
  unfold gallop
  simp only [good_bind, good_dcheck, good_ld, good_jsAny, good_compareKey]
  have hl := hv.1
  obtain ⟨v, hv'⟩ := hv.2 (base + hint) (by omega) (by omega)
  refine ⟨by omega, by omega, ⟨by omega, by omega⟩, v, ?_⟩
  rw [show ((base : Int) + (hint : Int)).toNat = base + hint by omega]
  refine ⟨hv', fun o e' _ => ?_⟩
  have hph := gallopPhase_good cmp smiMax (key := key) (keyFirst := isRight)
    (plus := decide (o < 0) != isRight) (breakNeg := !decide (o < 0)) hv hh _ 0 1 (by omega)
    (by split <;> omega) rfl e'
  refine hph.mono ?_
  rintro r e2 c2 ⟨hc2, hr1, hr2⟩
  subst c2
  have hsearch : ∀ (lo hi : Nat), lo ≤ hi → hi ≤ length →
      ((gallopSearch cmp a key isRight (base : Int) (lo : Int) (hi : Int)) e2 c).Good
        (fun s e' c' => s.1 = s.2 ∧ (0 ≤ s.2 ∧ s.2 ≤ (length : Int)) ∧
          ((pure s.2 : M ε Int) e' c').Good (fun r _ c' => c' = c ∧ ∃ k : Nat, r = (k : Int) ∧ k ≤ length)) := by
    intro lo hi h1 h2
    refine (gallopSearch_good cmp (key := key) (keyFirst := isRight) hv lo hi h1 h2 e2).mono ?_
    rintro s e3 c3 ⟨hc3, k, hk, hk1, hk2⟩
    subst hk
    exact ⟨rfl, ⟨by omega, by omega⟩, hc3, k, rfl, by omega⟩
  generalize (decide (o < 0) != isRight) = plus at hr2 ⊢
  cases plus
  · simp only [Bool.false_eq_true, ite_false] at hr2 ⊢
    by_cases hc : (hint : Int) + 1 < (r.2 : Int)
    · rw [ite_eq_left hc]
      refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
      rw [show (hint : Int) - ((hint : Int) + 1) + 1 = ((0 : Nat) : Int) by omega,
        show (hint : Int) - (r.1 : Int) = ((hint - r.1 : Nat) : Int) by omega]
      exact hsearch 0 (hint - r.1) (by omega) (by omega)
    · rw [ite_eq_right hc]
      refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
      rw [show (hint : Int) - (r.2 : Int) + 1 = ((hint + 1 - r.2 : Nat) : Int) by omega,
        show (hint : Int) - (r.1 : Int) = ((hint - r.1 : Nat) : Int) by omega]
      exact hsearch _ _ (by omega) (by omega)
  · simp only [ite_true] at hr2 ⊢
    by_cases hc : (length : Int) - (hint : Int) < (r.2 : Int)
    · rw [ite_eq_left hc]
      refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
      rw [show (r.1 : Int) + (hint : Int) + 1 = ((r.1 + hint + 1 : Nat) : Int) by omega,
        show (length : Int) - (hint : Int) + (hint : Int) = ((length : Nat) : Int) by omega]
      exact hsearch _ _ (by omega) (by omega)
    · rw [ite_eq_right hc]
      refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
      rw [show (r.1 : Int) + (hint : Int) + 1 = ((r.1 + hint + 1 : Nat) : Int) by omega,
        show (r.2 : Int) + (hint : Int) = ((r.2 + hint : Nat) : Int) by omega]
      exact hsearch _ _ (by omega) (by omega)

end

end ArraySort
