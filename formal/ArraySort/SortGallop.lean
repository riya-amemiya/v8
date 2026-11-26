import ArraySort.Post

namespace ArraySort

open Torque

def gp (le : Val → Val → Bool) (kf : Bool) (key : Val) (x : Option Val) : Bool :=
  if kf then oleq le x (some key) else !oleq le (some key) x

section

variable {ε : Type} (cmp : Cmp ε) (smiMax : Nat) {le : Val → Val → Bool}

theorem gp_cmp (hc : CmpOK le cmp) {kf : Bool} {key el : Val} {e e' : ε} {o : Int}
    (h : cmp e (if kf then key else el) (if kf then el else key) = some (o, e')) :
    decide (o < 0) = kf ↔ gp le kf key (some el) = false := by
  cases kf with
  | true =>
    simp only [ite_true] at h
    have := hc _ _ _ _ _ h
    simp only [gp, ite_true, oleq, decide_eq_true_eq]
    exact this
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    have := hc _ _ _ _ _ h
    simp only [gp, Bool.false_eq_true, ite_false, oleq, decide_eq_false_iff_not, Bool.not_eq_false']
    constructor
    · intro h1
      cases h2 : le key el
      · exact absurd (this.2 h2) h1
      · rfl
    · intro h1 h2
      rw [this.1 h2] at h1
      cases h1

theorem gp_mono (hle : TotalPreorder le) {kf : Bool} {key : Val} {l : List (Option Val)} {lo hi i j : Nat}
    (hs : SrtAt le l lo hi) (h1 : lo ≤ i) (h2 : i ≤ j) (h3 : j < hi)
    (hj : gp le kf key (l.getD j none) = true) : gp le kf key (l.getD i none) = true := by
  have hij := hs i j h1 h2 h3
  cases kf with
  | true =>
    simp only [gp, ite_true] at hj ⊢
    exact oleq_trans hle _ _ _ hij hj
  | false =>
    simp only [gp, Bool.false_eq_true, ite_false, Bool.not_eq_true'] at hj ⊢
    exact oleq_false_of_le' hle hj hij

theorem gp_mono' (hle : TotalPreorder le) {kf : Bool} {key : Val} {l : List (Option Val)} {lo hi i j : Nat}
    (hs : SrtAt le l lo hi) (h1 : lo ≤ i) (h2 : i ≤ j) (h3 : j < hi)
    (hi' : gp le kf key (l.getD i none) = false) : gp le kf key (l.getD j none) = false := by
  cases h : gp le kf key (l.getD j none)
  · rfl
  · rw [gp_mono hle hs h1 h2 h3 h] at hi'
    cases hi'

theorem gallopSearch_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {a : Arr} {key : Val} {kf : Bool}
    {base length : Nat} {c : Core} (hs : SrtAt le (c.get a) base (base + length)) :
    ∀ d (lo hi : Int) (e : ε), (hi - lo).toNat = d → 0 ≤ lo → hi ≤ length →
      (∀ i : Nat, (i : Int) < lo → gp le kf key ((c.get a).getD (base + i) none) = true) →
      (∀ i : Nat, hi ≤ (i : Int) → i < length → gp le kf key ((c.get a).getD (base + i) none) = false) →
      ((gallopSearch cmp a key kf (base : Int) lo hi) e c).Post (fun (r : Int × Int) _ c' => c' = c ∧
        (∀ i : Nat, (i : Int) < r.1 → gp le kf key ((c.get a).getD (base + i) none) = true) ∧
        (∀ i : Nat, r.2 ≤ (i : Int) → i < length → gp le kf key ((c.get a).getD (base + i) none) = false) ∧
        r.2 ≤ r.1) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
  intro lo hi e hd h0 hl h1 h2
  rw [gallopSearch, post_dite]
  split
  · next hlt =>
    obtain ⟨m, hm⟩ : ∃ m : Nat, lo + (hi - lo) / 2 = m := ⟨(lo + (hi - lo) / 2).toNat, by omega⟩
    simp only [post_bind, post_ld, post_jsAny, post_compareKey, hm]
    intro _ v hv o e' ho
    rw [show ((base : Int) + (m : Int)).toNat = base + m by omega] at hv
    have hg := gp_cmp cmp hc ho
    rw [post_ite]
    split
    · next hk =>
      have hf : gp le kf key ((c.get a).getD (base + m) none) = false := by rw [hv]; exact hg.1 hk
      exact ih ((m - lo).toNat) (by omega) lo m e' rfl h0 (by omega) h1 fun i hi1 hi2 =>
        gp_mono' hle hs (by omega) (show base + m ≤ base + i by omega) (by omega) hf
    · next hk =>
      have ht : gp le kf key ((c.get a).getD (base + m) none) = true := by
        rw [hv]
        cases h : gp le kf key (some v)
        · exact absurd (hg.2 h) hk
        · rfl
      exact ih ((hi - (m + 1)).toNat) (by omega) (m + 1) hi e' rfl (by omega) hl (fun i hi1 =>
        gp_mono hle hs (by omega) (show base + i ≤ base + m by omega) (by omega) ht) h2
  · next hlt =>
    rw [post_pure]
    exact ⟨rfl, h1, h2, by omega⟩

theorem gallopPhase_post {a : Arr} {key : Val} {kf plus breakNeg : Bool}
    {base length hint : Nat} {maxOfs : Int} {c : Core}
    (hmax : maxOfs = if plus then (length : Int) - hint else hint + 1)
    (hbr : ∀ el o (e e' : ε), cmp e (if kf then key else el) (if kf then el else key) = some (o, e') →
      ((if breakNeg then decide (o < 0) else decide (0 ≤ o)) = true ↔ gp le kf key (some el) ≠ plus)) :
    ∀ d (lastOfs offset : Nat) (e : ε), (maxOfs - offset).toNat = d → (lastOfs : Int) < maxOfs →
      lastOfs < offset →
      gp le kf key ((c.get a).getD (if plus then base + hint + lastOfs else base + hint - lastOfs) none) = plus →
      ((gallopPhase cmp smiMax a key kf plus breakNeg (base : Int) (hint : Int) maxOfs lastOfs offset) e c).Post
        (fun r _ c' => c' = c ∧ (r.1 : Int) < maxOfs ∧ r.1 < r.2 ∧
          gp le kf key ((c.get a).getD (if plus then base + hint + r.1 else base + hint - r.1) none) = plus ∧
          ((r.2 : Int) < maxOfs →
            gp le kf key ((c.get a).getD (if plus then base + hint + r.2 else base + hint - r.2) none) ≠ plus)) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
  intro lastOfs offset e hd hl hlt hpr
  rw [gallopPhase, post_dite]
  split
  · next hoff =>
    have hidx : (if plus then (base : Int) + hint + offset else (base : Int) + hint - offset).toNat =
        (if plus then base + hint + offset else base + hint - offset) := by
      cases plus <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hmax ⊢ <;> omega
    simp only [post_bind, post_ld, post_jsAny, post_compareKey]
    intro _ v hv o e' ho
    rw [hidx] at hv
    have hb := hbr v o e e' ho
    rw [post_ite]
    by_cases hbk : (if breakNeg then decide (o < 0) else decide (0 ≤ o)) = true
    · rw [ite_eq_left hbk, post_pure]
      refine ⟨rfl, hl, hlt, hpr, fun _ => ?_⟩
      rw [hv]
      exact hb.1 hbk
    · rw [ite_eq_right hbk]
      have hnext : offset < gallopNext smiMax maxOfs offset := by
        unfold gallopNext
        split <;> omega
      have hpr' : gp le kf key ((c.get a).getD (if plus then base + hint + offset else base + hint - offset) none) =
          plus := by
        rw [hv]
        cases h : gp le kf key (some v) == plus
        · exact absurd (hb.2 (by simpa using h)) hbk
        · simpa using h
      exact ih ((maxOfs - gallopNext smiMax maxOfs offset).toNat) (by omega) offset _ e' rfl hoff hnext hpr'
  · next hoff =>
    rw [post_pure]
    exact ⟨rfl, hl, hlt, hpr, fun h => absurd h hoff⟩

theorem breakNeg_iff (b : Bool) (o : Int) :
    (if b then decide (o < 0) else decide (0 ≤ o)) = true ↔ decide (o < 0) = b := by
  cases b <;> simp <;> omega

theorem gallop_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {isRight : Bool} {a : Arr} {key : Val}
    {base length hint : Nat} {c : Core} {e : ε} (hs : SrtAt le (c.get a) base (base + length)) :
    ((gallop cmp smiMax isRight a key (base : Int) (length : Int) (hint : Int)) e c).Post (fun (r : Int) _ c' =>
      c' = c ∧ ∃ k : Nat, r = (k : Int) ∧ k ≤ length ∧
        (∀ i, i < k → gp le isRight key ((c.get a).getD (base + i) none) = true) ∧
        (∀ i, k ≤ i → i < length → gp le isRight key ((c.get a).getD (base + i) none) = false)) := by
  unfold gallop
  simp only [post_bind, post_dcheck, post_ld, post_jsAny, post_compareKey]
  intro h1 h2 _ bh hbh o e1 ho
  rw [show ((base : Int) + (hint : Int)).toNat = base + hint by omega] at hbh
  have hg0 := gp_cmp cmp hc ho
  have hhl : hint < length := by omega
  generalize hneg : decide (o < 0) = neg at hg0
  generalize hpl : (neg != isRight) = plus
  have hpr0 : gp le isRight key ((c.get a).getD (if plus then base + hint + 0 else base + hint - 0) none) = plus := by
    rw [show (if plus then base + hint + 0 else base + hint - 0) = base + hint by split <;> omega, hbh, ← hpl]
    revert hg0
    cases neg <;> cases isRight <;> cases gp le _ key (some bh) <;> simp
  have hbr : ∀ el o' (e e' : ε), cmp e (if isRight then key else el) (if isRight then el else key) = some (o', e') →
      ((if !neg then decide (o' < 0) else decide (0 ≤ o')) = true ↔ gp le isRight key (some el) ≠ plus) := by
    intro el o' e2 e3 h'
    have hg := gp_cmp cmp hc h'
    rw [breakNeg_iff, ← hpl]
    revert hg
    generalize decide (o' < 0) = t
    cases t <;> cases neg <;> cases isRight <;> cases gp le _ key (some el) <;> simp
  refine (gallopPhase_post cmp smiMax (length := length) rfl hbr _ 0 1 e1 rfl (by split <;> omega) (by omega)
    hpr0).mono ?_
  rintro r e2 c2 ⟨hc2, hr1, hr12, hpr1, hpr2⟩
  subst c2
  simp only [post_pure]
  intro h3
  refine (gallopSearch_post cmp hle hc hs _ _ _ e2 rfl (by omega) (by omega) ?_ ?_).mono ?_
  · intro i hi
    cases plus with
    | true =>
      simp only [ite_true] at hr1 hpr1 hi
      exact gp_mono hle hs (by omega) (show base + i ≤ base + hint + r.1 by omega) (by omega) hpr1
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hr1 hpr1 hpr2 hi
      by_cases hlt : (r.2 : Int) < (hint : Int) + 1
      · have hlt' : ¬ (hint : Int) + 1 < r.2 := by omega
        simp only [hlt', ite_false] at hi
        have := hpr2 hlt
        have ht : gp le isRight key ((c.get a).getD (base + hint - r.2) none) = true := by
          cases h : gp le isRight key ((c.get a).getD (base + hint - r.2) none)
          · exact absurd h this
          · rfl
        exact gp_mono hle hs (by omega) (show base + i ≤ base + hint - r.2 by omega) (by omega) ht
      · split at hi <;> omega
  · intro i hi hil
    cases plus with
    | true =>
      simp only [ite_true] at hr1 hpr1 hpr2 hi
      by_cases hlt : (r.2 : Int) < (length : Int) - hint
      · have hlt' : ¬ (length : Int) - hint < r.2 := by omega
        simp only [hlt', ite_false] at hi
        have := hpr2 hlt
        have hf : gp le isRight key ((c.get a).getD (base + hint + r.2) none) = false := by
          cases h : gp le isRight key ((c.get a).getD (base + hint + r.2) none)
          · rfl
          · exact absurd h this
        exact gp_mono' hle hs (by omega) (show base + hint + r.2 ≤ base + i by omega) (by omega) hf
      · split at hi <;> omega
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hr1 hpr1 hi
      exact gp_mono' hle hs (by omega) (show base + hint - r.1 ≤ base + i by omega) (by omega) hpr1
  · rintro s e3 c3 ⟨hc3, hs1, hs2, hs12⟩
    subst c3
    intro h4 h5
    refine ⟨rfl, s.2.toNat, by omega, by omega, fun i hi => hs1 i (by omega), fun i hi hil => hs2 i (by omega) hil⟩

end

end ArraySort
