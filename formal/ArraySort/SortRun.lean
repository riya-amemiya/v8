import ArraySort.SortGallop

namespace ArraySort

open Torque

theorem post_and {ε α : Type} {Q1 Q2 : α → ε → Core → Prop} {r : Res ε α} (h1 : r.Post Q1) (h2 : r.Post Q2) :
    r.Post (fun a e c => Q1 a e c ∧ Q2 a e c) := by
  cases r <;> simp_all [Res.Post]

theorem msort_idem {le : Val → Val → Bool} (hle : TotalPreorder le) (l : List (Option Val)) :
    msort le (msort le l) = msort le l :=
  msort_sorted (pairwise_msort hle l)

theorem msort_cat {le : Val → Val → Bool} (hle : TotalPreorder le) (A B : List (Option Val)) :
    msort le (msort le A ++ B) = msort le (A ++ B) := by
  rw [msort_append hle, msort_idem hle, ← msort_append hle]

theorem oleq_strict_trans {le : Val → Val → Bool} (hle : TotalPreorder le) {x y z : Option Val}
    (h1 : oleq le x y = false) (h2 : oleq le y z = false) : oleq le x z = false := by
  cases h : oleq le x z
  · rfl
  · have hzy := oleq_of_not hle h2
    rw [oleq_trans hle x z y h hzy] at h1
    cases h1

theorem getElem?_eq_some_getD {l : List (Option Val)} {i : Nat} (h : i < l.length) :
    l[i]? = some (l.getD i none) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem pairwise_seg_of {R : Option Val → Option Val → Prop} {l : List (Option Val)} {lo hi : Nat}
    (hh : hi ≤ l.length) (h : ∀ i j, lo ≤ i → i < j → j < hi → R (l.getD i none) (l.getD j none)) :
    (seg l lo hi).Pairwise R := by
  rw [List.pairwise_iff_getElem]
  intro i j hi' hj hij
  have hlen : (seg l lo hi).length = hi - lo := length_seg hh
  have ei := getElem?_seg l lo hi i
  have ej := getElem?_seg l lo hi j
  rw [ite_eq_left (by omega), List.getElem?_eq_getElem (by omega)] at ei
  rw [ite_eq_left (by omega), List.getElem?_eq_getElem (by omega)] at ej
  have := h (lo + i) (lo + j) (by omega) (by omega) (by omega)
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, ← ei, ← ej] at this
  exact this

theorem seg_ins {w : List (Option Val)} {low k start : Nat} {x : Option Val} (h1 : low ≤ k) (h2 : k ≤ start)
    (h3 : start < w.length) :
    seg ((over w (k + 1) (seg w k start)).set k x) low (start + 1) = seg w low k ++ x :: seg w k start := by
  have hlen : (seg w k start).length = start - k := length_seg (by omega)
  have hl : (k + 1) + (seg w k start).length ≤ w.length := by rw [hlen]; omega
  rw [seg_split _ h1 (show k ≤ start + 1 by omega), seg_set_out (Or.inr (Nat.le_refl k)),
    seg_over_out hl (Or.inl (by omega)), seg_set_cons (by omega) (by rw [length_over hl]; omega)]
  congr 2
  rw [show start + 1 = (k + 1) + (seg w k start).length by rw [hlen]; omega, seg_over_in hl]

theorem rev_seg {w w' : List (Option Val)} {lo hi : Nat} (hh : hi < w.length)
    (hlo : lo ≤ hi + 1)
    (hspec : ∀ i, w'[i]? = if lo ≤ i ∧ i ≤ hi then w[lo + hi - i]? else w[i]?) :
    seg w' lo (hi + 1) = (seg w lo (hi + 1)).reverse := by
  apply List.ext_getElem?
  intro n
  rw [getElem?_seg]
  have hl : (seg w lo (hi + 1)).length = hi + 1 - lo := length_seg (by omega)
  by_cases hn : n < hi + 1 - lo
  · rw [ite_eq_left hn, List.getElem?_reverse (by omega), hl, getElem?_seg, ite_eq_left (by omega), hspec,
      ite_eq_left (by omega)]
    congr 1
    omega
  · rw [ite_eq_right hn, List.getElem?_eq_none (by rw [List.length_reverse, hl]; omega)]

section

variable {ε : Type} (cmp : Cmp ε) {le : Val → Val → Bool}

theorem bisSearch_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {pivot : Val} {low start : Nat} {c : Core}
    (hs : SrtAt le c.work low start) :
    ∀ d (left right : Int) (e : ε), (right - left).toNat = d → (low : Int) ≤ left → right ≤ start →
      (∀ i : Nat, low ≤ i → (i : Int) < left → oleq le (c.work.getD i none) (some pivot) = true) →
      (∀ i : Nat, right ≤ (i : Int) → i < start → oleq le (c.work.getD i none) (some pivot) = false) →
      ((bisSearch cmp pivot left right) e c).Post (fun (r : Int × Int) _ c' => c' = c ∧
        (∀ i : Nat, low ≤ i → (i : Int) < r.1 → oleq le (c.work.getD i none) (some pivot) = true) ∧
        (∀ i : Nat, r.2 ≤ (i : Int) → i < start → oleq le (c.work.getD i none) (some pivot) = false) ∧
        r.2 ≤ r.1 ∧ (low : Int) ≤ r.1 ∧ r.2 ≤ start) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
  intro left right e hd h0 hl h1 h2
  rw [bisSearch, post_dite]
  split
  · next hlt =>
    obtain ⟨m, hm⟩ : ∃ m : Nat, left + (right - left) / 2 = m := ⟨(left + (right - left) / 2).toNat, by omega⟩
    simp only [post_bind, post_ld, post_jsAny, post_compare, hm, Core.get_work, Int.toNat_natCast]
    intro _ v hv o e' ho
    have hg := hc _ _ _ _ _ ho
    rw [post_ite]
    by_cases hk : o < 0
    · rw [ite_eq_left hk]
      have hf : oleq le (c.work.getD m none) (some pivot) = false := by
        rw [hv]
        exact hg.1 hk
      exact ih ((m - left).toNat) (by omega) left m e' rfl h0 (by omega) h1 fun i hi1 hi2 =>
        oleq_false_of_le hle hf (hs m i (by omega) (by omega) hi2)
    · rw [ite_eq_right hk]
      have ht : oleq le (c.work.getD m none) (some pivot) = true := by
        rw [hv]
        cases h : le v pivot
        · exact absurd (hg.2 h) hk
        · exact h
      exact ih ((right - (m + 1)).toNat) (by omega) (m + 1) right e' rfl (by omega) hl (fun i hi1 hi2 => by
        rcases Nat.lt_or_ge i m with him | him
        · exact oleq_trans hle _ _ _ (hs i m hi1 (by omega) (by omega)) ht
        · have : i = m := by omega
          subst this
          exact ht) h2
  · next hlt =>
    rw [post_pure]
    exact ⟨rfl, h1, h2, by omega, h0, hl⟩

theorem bisLoop_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {low high : Nat} {c0 : Core}
    (hh : high ≤ c0.work.length) :
    ∀ d start (e : ε) (c : Core), high - start = d → low < start → start ≤ high →
      c.work.length = c0.work.length → seg c.work low start = msort le (seg c0.work low start) →
      (∀ i, start ≤ i → c.work[i]? = c0.work[i]?) →
      ((bisLoop cmp (low : Int) (high : Int) (start : Int)) e c).Post
        (fun _ _ c' => seg c'.work low high = msort le (seg c0.work low high))
  | 0, start, e, c, hd, hls, hsh, hlen, hseg, hun => by
    rw [bisLoop, dite_eq_right (by omega), post_pure, show high = start by omega]
    exact hseg
  | d + 1, start, e, c, hd, hls, hsh, hlen, hseg, hun => by
    rw [bisLoop, dite_eq_left (by omega)]
    simp only [post_bind, post_ld, post_jsAny, post_dcheck, Core.get_work, Int.toNat_natCast]
    intro hb pivot hp _
    have hsrt : SrtAt le c.work low start :=
      srtAt_of_srt hle (by omega) (by rw [hseg]; exact pairwise_msort hle _)
    refine (bisSearch_post cmp hle hc hsrt _ (low : Int) (start : Int) e rfl (by omega) (by omega)
      (fun i h1 h2 => absurd h2 (by omega)) (fun i h1 h2 => absurd h2 (by omega))).mono ?_
    rintro lr e1 c1 ⟨hc1, hl1, hl2, hl12, hl0, hls'⟩
    subst c1
    intro heq
    obtain ⟨k, hk⟩ : ∃ k : Nat, lr.1 = k := ⟨lr.1.toNat, by omega⟩
    rw [hk]
    rw [hk] at heq hl1 hl0
    refine (post_of_good (bisShift_good (left := k) (p0 := start) (c0 := c) (e := e1) (by omega) (start - k) start
      (by omega) (by omega) c (by rw [seg_self, over_nil]))).mono ?_
    rintro _ e2 c2 ⟨-, hc2⟩
    subst c2
    simp only [post_st, Core.get_work, Core.put_work, Int.toNat_natCast]
    intro _
    rw [show (start : Int) + 1 = ((start + 1 : Nat) : Int) by omega]
    have hlo : (seg c.work k start).length = start - k := length_seg (by omega)
    have hol : (k + 1) + (seg c.work k start).length ≤ c.work.length := by rw [hlo]; omega
    refine bisLoop_post hle hc hh d (start + 1) e2 _ (by omega) (by omega) (by omega) ?_ ?_ ?_
    · simp only [List.length_set]
      rw [length_over hol, hlen]
    · simp only
      rw [seg_ins (by omega) (by omega) (by omega)]
      have hsplit : seg c.work low start = seg c.work low k ++ seg c.work k start :=
        seg_split _ (by omega) (by omega)
      rw [← merge_insert (fun s hs => by
          obtain ⟨i, hi1, hi2, hi⟩ := mem_seg.1 hs
          rw [← getD_of_getElem? hi]
          exact hl1 i hi1 (by omega))
        (fun s hs => by
          obtain ⟨i, hi1, hi2, hi⟩ := mem_seg.1 hs
          rw [← getD_of_getElem? hi]
          exact hl2 i (by omega) hi2),
        ← hsplit, hseg, ← msort_single (le := le) (some pivot), ← msort_append hle,
        seg_snoc_getD (by omega) (by omega)]
      congr 3
      rw [← hp, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hun start (Nat.le_refl _)]
    · intro i hi
      simp only
      rw [List.getElem?_set, ite_eq_right (by omega), getElem?_over_out hol (Or.inr (by rw [hlo]; omega)),
        hun i (by omega)]

theorem binaryInsertionSort_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {low start high : Nat} {c : Core}
    {e : ε} (hh : high ≤ c.work.length) (hs : Srt le (seg c.work low start)) :
    ((binaryInsertionSort cmp (low : Int) (start : Int) (high : Int)) e c).Post
      (fun _ _ c' => seg c'.work low high = msort le (seg c.work low high)) := by
  unfold binaryInsertionSort
  simp only [post_bind, post_dcheck]
  intro h
  by_cases h0 : (low : Int) = start
  · simp only [h0, ite_true]
    have hls : low = start := by omega
    subst hls
    by_cases hlh : low < high
    · rw [show (low : Int) + 1 = ((low + 1 : Nat) : Int) by omega]
      refine bisLoop_post cmp hle hc hh (high - (low + 1)) (low + 1) e c rfl (by omega) (by omega) rfl ?_
        fun _ _ => rfl
      rw [seg_single (by omega), msort_single]
    · rw [bisLoop, dite_eq_right (by omega), post_pure, show high = low by omega, seg_self]
      simp [msort]
  · simp only [h0, ite_false]
    refine bisLoop_post cmp hle hc hh (high - start) start e c rfl (by omega) (by omega) rfl
      (msort_sorted hs).symm fun _ _ => rfl

theorem countRunLoop_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {isDesc : Bool} {lowArg high : Nat}
    {c : Core} :
    ∀ d (prev : Val) (idx : Nat) (e : ε), high - idx = d → lowArg + 2 ≤ idx → idx ≤ high →
      c.work.getD (idx - 1) none = some prev →
      (∀ i j, lowArg ≤ i → i < j → j < idx → oleq le (c.work.getD i none) (c.work.getD j none) = !isDesc) →
      ((countRunLoop cmp isDesc (high : Int) prev (idx : Int) ((idx - lowArg : Nat) : Int)) e c).Post
        (fun (r : Int) _ c' => c' = c ∧ ∃ k : Nat, r = (k : Int) ∧ 2 ≤ k ∧ lowArg + k ≤ high ∧
          ∀ i j, lowArg ≤ i → i < j → j < lowArg + k →
            oleq le (c.work.getD i none) (c.work.getD j none) = !isDesc)
  | 0, prev, idx, e, hd, h1, h2, hp, hr => by
    rw [countRunLoop, dite_eq_right (by omega), post_pure]
    exact ⟨rfl, idx - lowArg, rfl, by omega, by omega, fun i j hi hij hj => hr i j hi hij (by omega)⟩
  | d + 1, prev, idx, e, hd, h1, h2, hp, hr => by
    rw [countRunLoop, dite_eq_left (by omega)]
    simp only [post_bind, post_ld, post_jsAny, post_compare, Core.get_work, Int.toNat_natCast]
    intro _ cur hcur o e' ho
    have hg := hc _ _ _ _ _ ho
    have hrel : (if isDesc then decide (0 ≤ o) else decide (o < 0)) = true ∨
        oleq le (c.work.getD (idx - 1) none) (c.work.getD idx none) = !isDesc := by
      rw [hp, hcur]
      cases isDesc with
      | true =>
        by_cases ho' : 0 ≤ o
        · exact Or.inl (by simp [ho'])
        · exact Or.inr (by simp only [oleq, Bool.not_true]; exact hg.1 (by omega))
      | false =>
        by_cases ho' : o < 0
        · exact Or.inl (by simp [ho'])
        · right
          simp only [oleq, Bool.not_false]
          cases h : le prev cur
          · exact absurd (hg.2 h) ho'
          · rfl
    rw [post_ite]
    by_cases hb : (if isDesc then decide (0 ≤ o) else decide (o < 0)) = true
    · rw [ite_eq_left hb, post_pure]
      exact ⟨rfl, idx - lowArg, rfl, by omega, by omega, fun i j hi hij hj => hr i j hi hij (by omega)⟩
    · rw [ite_eq_right hb, show ((idx - lowArg : Nat) : Int) + 1 = ((idx + 1 - lowArg : Nat) : Int) by omega,
        show (idx : Int) + 1 = ((idx + 1 : Nat) : Int) by omega]
      have hlast := hrel.resolve_left hb
      refine countRunLoop_post hle hc d cur (idx + 1) e' (by omega) (by omega) (by omega) (by simpa using hcur) ?_
      intro i j hi hij hj
      by_cases hji : j < idx
      · exact hr i j hi hij hji
      · have : j = idx := by omega
        subst this
        by_cases hii : i = j - 1
        · rw [hii]
          exact hlast
        · have h1' := hr i (j - 1) hi (by omega) (by omega)
          cases isDesc with
          | true =>
            simp only [Bool.not_true] at h1' hlast ⊢
            exact oleq_strict_trans hle h1' hlast
          | false =>
            simp only [Bool.not_false] at h1' hlast ⊢
            exact oleq_trans hle _ _ _ h1' hlast

theorem reverseLoop_post :
    ∀ d (lo hi : Nat) (e : ε) (c : Core), hi - lo = d → hi < c.work.length →
      ((reverseLoop (lo : Int) (hi : Int)) e c).Post (fun _ _ c' => c'.work.length = c.work.length ∧
        ∀ i, c'.work[i]? = if lo ≤ i ∧ i ≤ hi then c.work[lo + hi - i]? else c.work[i]?) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
  intro lo hi e c hd hh
  rw [reverseLoop, post_dite]
  split
  · next hlt =>
    simp only [post_bind, post_ld, post_st, Core.get_work, Core.put_work, Int.toNat_natCast]
    intro _ _ _ _
    rw [show (lo : Int) + 1 = ((lo + 1 : Nat) : Int) by omega, show (hi : Int) - 1 = ((hi - 1 : Nat) : Int) by omega]
    refine (ih (hi - 1 - (lo + 1)) (by omega) (lo + 1) (hi - 1) e _ rfl (by simp; omega)).mono ?_
    rintro _ e' c' ⟨hl', hs'⟩
    simp only [List.length_set] at hl'
    refine ⟨hl', fun i => ?_⟩
    rw [hs' i]
    simp only [List.getElem?_set, List.length_set]
    by_cases h1 : lo + 1 ≤ i ∧ i ≤ hi - 1
    · rw [ite_eq_left h1, ite_eq_left (show lo ≤ i ∧ i ≤ hi by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      congr 1
      omega
    · rw [ite_eq_right h1]
      by_cases h2 : i = hi
      · subst h2
        rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (show lo ≤ i ∧ i ≤ i by omega),
          getElem?_eq_some_getD (by omega)]
        congr 2
        omega
      · by_cases h3 : i = lo
        · subst h3
          rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
            ite_eq_left (show i ≤ i ∧ i ≤ hi by omega), getElem?_eq_some_getD (by omega)]
          congr 2
          omega
        · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · next hlt =>
    rw [post_pure]
    refine ⟨rfl, fun i => ?_⟩
    split
    · congr 1
      omega
    · rfl

theorem countAndMakeRun_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {lowArg high : Nat} {c : Core} {e : ε}
    (hh : high ≤ c.work.length) :
    ((countAndMakeRun cmp (lowArg : Int) (high : Int)) e c).Post (fun (r : Int) _ c' => ∃ k : Nat, r = (k : Int) ∧
      lowArg + k ≤ high ∧ c'.work.length = c.work.length ∧
      seg c'.work lowArg (lowArg + k) = msort le (seg c.work lowArg (lowArg + k)) ∧
      ∀ i, lowArg + k ≤ i → c'.work[i]? = c.work[i]?) := by
  unfold countAndMakeRun
  simp only [post_bind, post_dcheck]
  intro h
  rw [post_ite]
  split
  · next h1 =>
    rw [post_pure]
    refine ⟨1, rfl, by omega, rfl, ?_, fun _ _ => rfl⟩
    rw [seg_single (by omega), msort_single]
  · next h1 =>
    simp only [post_bind, post_ld, post_jsAny, post_compare, Core.get_work]
    intro _ eLow hlo _ ePred hpred o e1 ho
    rw [show ((lowArg : Int) + 1).toNat = lowArg + 1 by omega] at hlo
    rw [Int.toNat_natCast] at hpred
    have hg := hc _ _ _ _ _ ho
    rw [show (lowArg : Int) + 2 = ((lowArg + 2 : Nat) : Int) by omega,
      show (2 : Int) = ((lowArg + 2 - lowArg : Nat) : Int) by omega]
    refine (countRunLoop_post cmp hle hc (isDesc := decide (o < 0)) (high - (lowArg + 2)) eLow (lowArg + 2) e1 rfl
      (by omega) (by omega) (by simpa using hlo) ?_).mono ?_
    · intro i j hi hij hj
      have : i = lowArg := by omega
      subst this
      have : j = i + 1 := by omega
      subst this
      rw [hpred, hlo]
      simp only [oleq]
      by_cases ho' : o < 0
      · simp only [ho', decide_true, Bool.not_true]
        exact hg.1 ho'
      · simp only [ho', decide_false, Bool.not_false]
        cases h : le ePred eLow
        · exact absurd (hg.2 h) ho'
        · rfl
    · rintro r e2 c2 ⟨hc2, k, hk, hk2, hkh, hrel⟩
      subst c2
      subst hk
      rw [post_doIf]
      split
      · next ho' =>
        unfold reverseRange
        rw [show (lowArg : Int) + (k : Int) - 1 = ((lowArg + k - 1 : Nat) : Int) by omega]
        refine (reverseLoop_post (lowArg + k - 1 - lowArg) lowArg (lowArg + k - 1) e2 c rfl (by omega)).mono ?_
        rintro _ e3 c3 ⟨hl3, hs3⟩
        rw [post_pure]
        refine ⟨k, rfl, hkh, hl3, ?_, fun i hi => by rw [hs3 i, ite_eq_right (by omega)]⟩
        rw [show lowArg + k = lowArg + k - 1 + 1 by omega, rev_seg (by omega) (by omega) hs3]
        symm
        apply msort_desc hle
        apply pairwise_seg_of (by omega)
        intro i j hi hij hj
        have := hrel i j hi hij (by omega)
        simpa [ho'] using this
      · next ho' =>
        rw [post_pure]
        refine ⟨k, rfl, hkh, rfl, ?_, fun _ _ => rfl⟩
        symm
        apply msort_sorted
        apply pairwise_seg_of (by omega)
        intro i j hi hij hj
        have := hrel i j hi hij hj
        simpa [ho'] using this

end

end ArraySort
