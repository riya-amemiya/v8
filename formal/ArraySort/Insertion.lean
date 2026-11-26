import ArraySort.Copy

namespace ArraySort

open Torque

section

variable {ε : Type} (cmp : Cmp ε)

theorem bisSearch_good {pivot : Val} {lo hi : Nat} {c : Core} (hv : Vals c.work lo hi) :
    ∀ (left right : Nat), lo ≤ left → left ≤ right → right ≤ hi → ∀ e,
      ((bisSearch cmp pivot (left : Int) (right : Int)) e c).Good
        (fun r _ c' => c' = c ∧ ∃ k : Nat, r = ((k : Int), (k : Int)) ∧ left ≤ k ∧ k ≤ right)
  | left, right, h1, h2, h3, e => by
    by_cases hlr : left < right
    · rw [bisSearch, dite_eq_left (by omega)]
      have hm : ((left : Int) + ((right : Int) - (left : Int)) / 2) =
          ((left + (right - left) / 2 : Nat) : Int) := by omega
      simp only [hm, good_bind, good_ld, good_jsAny, good_compare, Core.get_work, Int.toNat_natCast]
      obtain ⟨v, hv'⟩ := hv.2 (left + (right - left) / 2) (by omega) (by omega)
      refine ⟨⟨by omega, by have := hv.1; omega⟩, v, hv', fun o e' _ => ?_⟩
      rw [good_ite]
      split
      · exact (bisSearch_good hv left (left + (right - left) / 2) h1 (by omega) (by omega) e').mono
          fun r _ c' ⟨hc, k, hk, hk1, hk2⟩ => ⟨hc, k, hk, hk1, by omega⟩
      · have := bisSearch_good (pivot := pivot) hv (left + (right - left) / 2 + 1) right (by omega)
          (by omega) h3 e'
        rw [show ((left + (right - left) / 2 : Nat) : Int) + 1 = ((left + (right - left) / 2 + 1 : Nat) : Int)
          by omega]
        exact this.mono fun r _ c' ⟨hc, k, hk, hk1, hk2⟩ => ⟨hc, k, hk, by omega, hk2⟩
    · rw [bisSearch, dite_eq_right (by omega)]
      exact ⟨rfl, left, by rw [show right = left by omega], Nat.le_refl _, h2⟩
termination_by left right => right - left

theorem bisShift_good {left p0 : Nat} {c0 : Core} {e : ε} (hp : p0 < c0.work.length) :
    ∀ d q, q = left + d → q ≤ p0 → ∀ c, c = { c0 with work := over c0.work (q + 1) (seg c0.work q p0) } →
      ((bisShift (left : Int) (q : Int)) e c).Good
        (fun _ e' c' => e' = e ∧ c' = { c0 with work := over c0.work (left + 1) (seg c0.work left p0) })
  | 0, q, hq, _, c, hc => by
    rw [bisShift, dite_eq_right (by omega)]
    have : q = left := by omega
    subst this
    exact ⟨rfl, hc⟩
  | d + 1, q, hq, hq0, c, hc => by
    have hlen : (seg c0.work q p0).length = p0 - q := by
      rw [length_seg (by omega)]
    subst hc
    have hwl : (over c0.work (q + 1) (seg c0.work q p0)).length = c0.work.length :=
      length_over (by rw [hlen]; omega)
    rw [bisShift, dite_eq_left (by omega), good_seq, good_mv]
    simp only [Core.get_work, Core.put_work, hwl]
    refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
    rw [show ((q : Int) - 1).toNat = q - 1 by omega, show (q : Int).toNat = q by omega,
      getD_over_out (by rw [hlen]; omega) (by omega)]
    have hx : (over c0.work (q + 1) (seg c0.work q p0)).set q (c0.work.getD (q - 1) none) =
        over c0.work (q - 1 + 1) (seg c0.work (q - 1) p0) := by
      have h1 := over_cons (l := c0.work) (s := seg c0.work q p0) (pos := q + 1)
        (x := c0.work.getD (q - 1) none) (by omega) (by rw [hlen]; omega)
      rw [Nat.add_sub_cancel] at h1
      rw [h1, show q - 1 + 1 = q by omega,
        seg_cons_getD (l := c0.work) (lo := q - 1) (hi := p0) (by omega) (by omega),
        show q - 1 + 1 = q by omega]
    have := bisShift_good (left := left) (e := e) hp d (q - 1) (by omega) (by omega)
      { c0 with work := over c0.work (q - 1 + 1) (seg c0.work (q - 1) p0) } rfl
    rw [show (q : Int) - 1 = ((q - 1 : Nat) : Int) by omega, hx]
    exact this

theorem perm_cons_snoc {α : Type} (a : α) (l : List α) : (a :: l).Perm (l ++ [a]) := by
  simpa using (List.perm_middle (a := a) (l₁ := l) (l₂ := [])).symm

theorem bisLoop_good {low high : Nat} {c0 : Core} (hh : high ≤ c0.work.length) :
    ∀ d start, high - start = d → low < start → ∀ e c, c = { c0 with work := c.work } →
      PermOn c0.work c.work low high → Vals c.work low high →
      ((bisLoop cmp (low : Int) (high : Int) (start : Int)) e c).Good
        (fun _ _ c' => c' = { c0 with work := c'.work } ∧ PermOn c0.work c'.work low high)
  | d, start, hd, hls, e, c, hc, hp, hv => by
    by_cases hsh : start < high
    · rw [bisLoop, dite_eq_left (by omega)]
      simp only [good_bind, good_ld, good_jsAny, good_dcheck, Core.get_work, Int.toNat_natCast]
      obtain ⟨pv, hpv⟩ := hv.2 start (by omega) hsh
      refine ⟨⟨by omega, by have := hv.1; omega⟩, pv, hpv, by omega, ?_⟩
      refine (bisSearch_good cmp (lo := low) (hi := start)
        (Vals.mono (a := low) (b := start) hv (Nat.le_refl _) (Nat.le_of_lt hsh)) low start
        (Nat.le_refl _) (Nat.le_of_lt hls) (Nat.le_refl _) e).mono ?_
      rintro r e1 c1 ⟨hc1, k, hr, hk1, hk2⟩
      subst c1
      subst hr
      simp only [good_st, Core.get_work, Core.put_work, true_and]
      have hwl : c.work.length = c0.work.length := hp.len
      have hsh' := bisShift_good (left := k) (p0 := start) (c0 := c) (e := e1) (by omega) (start - k)
        start (by omega) (Nat.le_refl _) c (by rw [seg_self, over_nil])
      refine hsh'.mono ?_
      rintro _ e2 c2 ⟨he2, hc2⟩
      subst he2
      subst hc2
      have hlen : (seg c.work k start).length = start - k := by rw [length_seg (by omega)]
      refine ⟨⟨by omega, by simp only; rw [length_over (by rw [hlen]; omega)]; omega⟩, ?_⟩
      simp only [Int.toNat_natCast]
      have hw2 : (over c.work (k + 1) (seg c.work k start)).set k (some pv) =
          over c.work k (some pv :: seg c.work k start) :=
        over_cons' (by rw [hlen]; omega)
      rw [hw2]
      have hs : (some pv :: seg c.work k start).length = start + 1 - k := by
        simp [hlen]
        omega
      have hpo : PermOn c.work (over c.work k (some pv :: seg c.work k start)) k (start + 1) := by
        have := PermOn.of_over (l := c.work) (p := k) (s := some pv :: seg c.work k start)
          (by rw [hs]; omega) (by
            rw [hs, show k + (start + 1 - k) = start + 1 by omega, seg_snoc_getD (by omega) (by omega), hpv]
            exact perm_cons_snoc _ _)
        rwa [hs, show k + (start + 1 - k) = start + 1 by omega] at this
      have hpo' := hpo.widen (lo' := low) (hi' := high) hk1 (by omega) (by omega)
      have hp2 := hp.trans hpo'
      have := bisLoop_good hh (high - (start + 1)) (start + 1) rfl (by omega) e2
        { c0 with work := over c.work k (some pv :: seg c.work k start) } rfl hp2
        (Vals.of_permOn hpo' hv)
      rw [show (start : Int) + 1 = ((start + 1 : Nat) : Int) by omega]
      have hc' : { c with work := over c.work k (some pv :: seg c.work k start) } =
          { c0 with work := over c.work k (some pv :: seg c.work k start) } := by
        rw [hc]
      rw [hc']
      exact this
    · rw [bisLoop, dite_eq_right (by omega)]
      exact ⟨hc, hp⟩
termination_by d => d

theorem binaryInsertionSort_good {low start high : Nat} {c : Core} {e : ε} (h1 : low ≤ start)
    (h2 : start ≤ high) (hv : Vals c.work low high) :
    ((binaryInsertionSort cmp (low : Int) (start : Int) (high : Int)) e c).Good
      (fun _ _ c' => c' = { c with work := c'.work } ∧ PermOn c.work c'.work low high) := by
  unfold binaryInsertionSort
  simp only [good_bind, good_dcheck]
  refine ⟨by omega, ?_⟩
  by_cases hls : low = start
  · rw [ite_eq_left (by omega), show (start : Int) + 1 = ((start + 1 : Nat) : Int) by omega]
    exact bisLoop_good cmp hv.1 _ (start + 1) rfl (by omega) e c rfl (PermOn.refl _ _ _) hv
  · rw [ite_eq_right (by omega)]
    exact bisLoop_good cmp hv.1 _ start rfl (by omega) e c rfl (PermOn.refl _ _ _) hv

theorem countRunLoop_good {isDesc : Bool} {lowArg high : Nat} {c : Core} (hv : Vals c.work lowArg high) :
    ∀ d (prev : Val) (idx : Nat), high - idx = d → lowArg + 2 ≤ idx → idx ≤ high → ∀ e,
      ((countRunLoop cmp isDesc (high : Int) prev (idx : Int) ((idx - lowArg : Nat) : Int)) e c).Good
        (fun r _ c' => c' = c ∧ ∃ k : Nat, r = (k : Int) ∧ 2 ≤ k ∧ lowArg + k ≤ high)
  | d, prev, idx, hd, h1, h2, e => by
    by_cases hih : idx < high
    · rw [countRunLoop, dite_eq_left (by omega)]
      simp only [good_bind, good_ld, good_jsAny, good_compare, Core.get_work, Int.toNat_natCast]
      obtain ⟨v, hv'⟩ := hv.2 idx (by omega) hih
      refine ⟨⟨by omega, by have := hv.1; omega⟩, v, hv', fun o e' _ => ?_⟩
      rw [good_ite]
      by_cases hb : (if isDesc = true then decide (0 ≤ o) else decide (o < 0)) = true
      · rw [ite_eq_left hb]
        exact ⟨rfl, idx - lowArg, rfl, by omega, by omega⟩
      · rw [ite_eq_right hb]
        have := countRunLoop_good (isDesc := isDesc) hv (high - (idx + 1)) v (idx + 1) rfl (by omega)
          (by omega) e'
        rw [show ((idx : Nat) : Int) + 1 = ((idx + 1 : Nat) : Int) by omega,
          show ((idx - lowArg : Nat) : Int) + 1 = ((idx + 1 - lowArg : Nat) : Int) by omega]
        exact this
    · rw [countRunLoop, dite_eq_right (by omega)]
      exact ⟨rfl, idx - lowArg, rfl, by omega, by omega⟩
termination_by d => d

theorem swap_perm {α : Type} (x y : α) (m : List α) : (y :: (m ++ [x])).Perm (x :: (m ++ [y])) := by
  have h1 : (y :: (m ++ [x])).Perm (y :: x :: m) := List.Perm.cons _ (perm_cons_snoc x m).symm
  have h2 : (y :: x :: m).Perm (x :: y :: m) := List.Perm.swap _ _ _
  have h3 : (x :: y :: m).Perm (x :: (m ++ [y])) := List.Perm.cons _ (perm_cons_snoc y m)
  exact h1.trans (h2.trans h3)

theorem permOn_swap {w : List (Option Val)} {lo hi : Nat} (h1 : lo < hi) (h2 : hi < w.length) :
    PermOn w ((w.set lo (w.getD hi none)).set hi (w.getD lo none)) lo (hi + 1) := by
  refine ⟨by simp, fun i hi' => ?_, ?_⟩
  · rw [List.getElem?_set, List.getElem?_set]
    simp only [List.length_set]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [seg_set_snoc (by omega) (by simp; omega), seg_set_cons h1 (by omega),
      seg_cons_getD (l := w) (lo := lo) (hi := hi + 1) (by omega) (by omega),
      seg_snoc_getD (l := w) (lo := lo + 1) (hi := hi) (by omega) h2]
    exact swap_perm _ _ _

theorem reverseLoop_good {frm to : Nat} {c0 : Core} (hto : to ≤ c0.work.length) :
    ∀ d (low high : Nat), high - low = d → frm ≤ low → high < to → ∀ (e : ε) c,
      c = { c0 with work := c.work } → PermOn c0.work c.work frm to →
      ((reverseLoop (low : Int) (high : Int)) e c).Good
        (fun _ e' c' => e' = e ∧ c' = { c0 with work := c'.work } ∧ PermOn c0.work c'.work frm to)
  | d, low, high, hd, h1, h2, e, c, hc, hp => by
    by_cases hlh : low < high
    · rw [reverseLoop, dite_eq_left (by omega)]
      simp only [good_bind, good_ld, good_st, Core.get_work, Core.put_work, Int.toNat_natCast,
        List.length_set]
      have hl : c.work.length = c0.work.length := hp.len
      refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
      have hs := permOn_swap (w := c.work) hlh (by omega)
      have hp2 := hp.trans (hs.widen (lo' := frm) (hi' := to) h1 (by omega) (by omega))
      have := reverseLoop_good hto (high - 1 - (low + 1)) (low + 1) (high - 1) rfl (by omega) (by omega) e
        { c0 with work := (c.work.set low (c.work.getD high none)).set high (c.work.getD low none) } rfl hp2
      rw [show (low : Int) + 1 = ((low + 1 : Nat) : Int) by omega,
        show (high : Int) - 1 = ((high - 1 : Nat) : Int) by omega]
      have hc' : { { c with work := c.work.set low (c.work.getD high none) } with work := (c.work.set low (c.work.getD high none)).set high (c.work.getD low none) } =
          { c0 with work := (c.work.set low (c.work.getD high none)).set high (c.work.getD low none) } := by
        rw [hc]
      rw [hc']
      exact this
    · rw [reverseLoop, dite_eq_right (by omega)]
      exact ⟨rfl, hc, hp⟩
termination_by d => d

theorem countAndMakeRun_good {lowArg high : Nat} {c : Core} {e : ε} (h : lowArg < high)
    (hv : Vals c.work lowArg high) :
    ((countAndMakeRun cmp (lowArg : Int) (high : Int)) e c).Good
      (fun r _ c' => c' = { c with work := c'.work } ∧ PermOn c.work c'.work lowArg high ∧
        ∃ k : Nat, r = (k : Int) ∧ 1 ≤ k ∧ lowArg + k ≤ high) := by
  unfold countAndMakeRun
  simp only [good_bind, good_dcheck]
  refine ⟨by omega, ?_⟩
  rw [good_ite]
  split
  · exact ⟨rfl, PermOn.refl _ _ _, 1, rfl, by omega, by omega⟩
  · simp only [good_bind, good_ld, good_jsAny, good_compare, Core.get_work, Int.toNat_natCast]
    obtain ⟨v1, hv1⟩ := hv.2 (lowArg + 1) (by omega) (by omega)
    obtain ⟨v0, hv0⟩ := hv.2 lowArg (by omega) (by omega)
    have hl := hv.1
    refine ⟨⟨by omega, by omega⟩, v1, by rw [show ((lowArg : Int) + 1).toNat = lowArg + 1 by omega]; exact hv1,
      ⟨by omega, by omega⟩, v0, hv0, fun o e' _ => ?_⟩
    have hrun := countRunLoop_good cmp (isDesc := decide (o < 0)) hv (high - (lowArg + 2)) v1 (lowArg + 2) rfl
      (Nat.le_refl _) (by omega) e'
    rw [show (lowArg : Int) + 2 = ((lowArg + 2 : Nat) : Int) by omega,
      show (2 : Int) = ((lowArg + 2 - lowArg : Nat) : Int) by omega]
    refine hrun.mono ?_
    rintro r e2 c2 ⟨hc2, k, hk, hk1, hk2⟩
    subst c2
    subst hk
    rw [good_doIf]
    split
    · unfold reverseRange
      rw [show (lowArg : Int) + (k : Int) - 1 = ((lowArg + k - 1 : Nat) : Int) by omega]
      refine (reverseLoop_good (frm := lowArg) (to := high) (c0 := c) hl (lowArg + k - 1 - lowArg) lowArg
        (lowArg + k - 1) rfl (Nat.le_refl _) (by omega) e2 c rfl (PermOn.refl _ _ _)).mono ?_
      rintro _ e3 c3 ⟨_, hc3, hp3⟩
      exact ⟨hc3, hp3, k, rfl, by omega, hk2⟩
    · exact ⟨rfl, PermOn.refl _ _ _, k, rfl, by omega, hk2⟩

end

end ArraySort
