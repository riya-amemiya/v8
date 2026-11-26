import ArraySort.SortMergeHigh

namespace ArraySort

open Torque

theorem merge_trim {le : Val → Val → Bool} {A1 A2 B1 B2 : List (Option Val)}
    (h1 : ∀ x ∈ A1, ∀ y ∈ B1 ++ B2, oleq le x y = true) (h2 : ∀ x ∈ A2, ∀ y ∈ B2, oleq le x y = true) :
    List.merge (A1 ++ A2) (B1 ++ B2) (oleq le) = A1 ++ List.merge A2 B1 (oleq le) ++ B2 := by
  rw [merge_take_left (oleq le) h1, merge_drop_right (oleq le) h2, List.append_assoc]

theorem vals_of_msort {le : Val → Val → Bool} {w w0 : List (Option Val)} {lo hi : Nat} (hh : hi ≤ w.length)
    (hs : seg w lo hi = msort le (seg w0 lo hi)) (hv : Vals w0 lo hi) : Vals w lo hi := by
  apply vals_of_allSome hh
  rw [hs]
  exact (allSome_of_vals hv).perm (List.mergeSort_perm _ _)

section

variable {ε : Type} (cmp : Cmp ε) (smiMax : Nat) {le : Val → Val → Bool}

theorem mergeAtTail_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {bA lA lB : Nat} {c : Core} {e : ε}
    (hla : 0 < lA) (hlb : 0 < lB) (hv : Vals c.work bA (bA + lA + lB)) (hA : Srt le (seg c.work bA (bA + lA)))
    (hB : Srt le (seg c.work (bA + lA) (bA + lA + lB))) :
    ((mergeAtTail cmp smiMax (bA : Int) (lA : Int) ((bA + lA : Nat) : Int) (lB : Int)) e c).Post
      (fun _ _ c' => seg c'.work bA (bA + lA + lB) =
          List.merge (seg c.work bA (bA + lA)) (seg c.work (bA + lA) (bA + lA + lB)) (oleq le) ∧
        (∀ i, (i < bA ∨ bA + lA + lB ≤ i) → c'.work[i]? = c.work[i]?) ∧ c'.work.length = c.work.length ∧
        c'.runs = c.runs ∧ c'.size = c.size ∧ c'.powers = c.powers) := by
  have hl := hv.1
  have hsA : SrtAt le (c.get .work) bA (bA + lA) := srtAt_of_srt hle (by simp; omega) hA
  have hsB : SrtAt le (c.get .work) (bA + lA) (bA + lA + lB) := srtAt_of_srt hle (by simp; omega) hB
  have hsplit : seg c.work bA (bA + lA + lB) = seg c.work bA (bA + lA) ++ seg c.work (bA + lA) (bA + lA + lB) :=
    seg_split _ (by omega) (by omega)
  unfold mergeAtTail
  simp only [post_bind, post_ld, post_jsAny, Core.get_work, Int.toNat_natCast]
  intro _ v1 hv1
  have hB0 : ∀ y ∈ seg c.work (bA + lA) (bA + lA + lB), oleq le (some v1) y = true := by
    intro y hy
    rw [← hv1]
    rw [seg_cons_getD (by omega) (by omega)] at hy hB
    exact srt_cons_ge hle hB (oleq_refl hle _) y hy
  refine (gallop_post cmp smiMax hle hc (isRight := true) (key := v1) (hint := 0) (e := e) hsA).mono ?_
  rintro k e2 c2 ⟨hc2, kN, hk, hkN, hgl, hgr⟩
  subst c2
  subst hk
  simp only [Core.get_work] at hgl hgr
  rw [post_dcheck]
  intro _
  have hA1 : ∀ x ∈ seg c.work bA (bA + kN), ∀ y ∈ seg c.work (bA + lA) (bA + lA + lB), oleq le x y = true := by
    intro x hx y hy
    obtain ⟨i, hi1, hi2, hi⟩ := mem_seg.1 hx
    have := hgl (i - bA) (by omega)
    rw [show bA + (i - bA) = i by omega, getD_of_getElem? hi] at this
    exact oleq_trans hle _ _ _ (by simpa [gp] using this) (hB0 y hy)
  have hsA' : seg c.work bA (bA + lA) = seg c.work bA (bA + kN) ++ seg c.work (bA + kN) (bA + lA) :=
    seg_split _ (by omega) (by omega)
  rw [post_ite]
  split
  · rw [post_pure]
    refine ⟨?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    have : kN = lA := by omega
    subst this
    rw [hsplit, List.merge_of_le fun a b ha hb => hA1 a (by rwa [hsA', seg_self, List.append_nil] at ha) b hb]
  · simp only [post_bind, post_dcheck, post_ld, post_jsAny, Core.get_work]
    intro _ _ v2 hv2
    rw [show ((bA : Int) + (kN : Int) + ((lA : Int) - (kN : Int)) - 1).toNat = bA + lA - 1 by omega] at hv2
    have hgal := gallop_post cmp smiMax hle hc (isRight := false) (key := v2) (base := bA + lA) (length := lB)
      (hint := lB - 1) (e := e2) hsB
    rw [show ((lB - 1 : Nat) : Int) = (lB : Int) - 1 by omega] at hgal
    refine hgal.mono ?_
    rintro lb' e3 c3 ⟨hc3, lbN, hlb', hlbN, hgl2, hgr2⟩
    subst c3
    subst hlb'
    simp only [Core.get_work] at hgl2 hgr2
    intro _
    have hAl : ∀ x ∈ seg c.work bA (bA + lA), oleq le x (some v2) = true := by
      rw [← hv2]
      have := seg_snoc' (l := c.work) (lo := bA) (hi := bA + lA) (by omega) (by omega)
      rw [this] at hA ⊢
      exact srt_snoc_le hle hA
    have hB2 : ∀ x ∈ seg c.work bA (bA + lA), ∀ y ∈ seg c.work (bA + lA + lbN) (bA + lA + lB),
        oleq le x y = true := by
      intro x hx y hy
      obtain ⟨i, hi1, hi2, hi⟩ := mem_seg.1 hy
      have := hgr2 (i - (bA + lA)) (by omega) (by omega)
      rw [show bA + lA + (i - (bA + lA)) = i by omega, getD_of_getElem? hi] at this
      exact oleq_trans hle _ _ _ (hAl x hx) (by simpa [gp] using this)
    have hsB' : seg c.work (bA + lA) (bA + lA + lB) =
        seg c.work (bA + lA) (bA + lA + lbN) ++ seg c.work (bA + lA + lbN) (bA + lA + lB) :=
      seg_split _ (by omega) (by omega)
    rw [post_ite]
    split
    · rw [post_pure]
      refine ⟨?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
      have : lbN = 0 := by omega
      subst this
      rw [hsplit, List.merge_of_le fun a b ha hb => hB2 a ha b (by rw [Nat.add_zero]; exact hb)]
    · have hfull : List.merge (seg c.work bA (bA + lA)) (seg c.work (bA + lA) (bA + lA + lB)) (oleq le) =
          seg c.work bA (bA + kN) ++ List.merge (seg c.work (bA + kN) (bA + lA))
            (seg c.work (bA + lA) (bA + lA + lbN)) (oleq le) ++ seg c.work (bA + lA + lbN) (bA + lA + lB) := by
        rw [hsA', hsB']
        exact merge_trim (fun x hx y hy => hA1 x hx y (by rw [hsB']; exact hy))
          fun x hx y hy => hB2 x (by rw [hsA']; exact List.mem_append_right _ hx) y hy
      rw [show (bA : Int) + (kN : Int) = ((bA + kN : Nat) : Int) by omega,
        show (lA : Int) - (kN : Int) = ((lA - kN : Nat) : Int) by omega,
        show ((bA + lA : Nat) : Int) = ((bA + kN + (lA - kN) : Nat) : Int) by omega]
      have hv' : Vals c.work (bA + kN) (bA + kN + (lA - kN) + lbN) := hv.mono (by omega) (by omega)
      have hA' : Srt le (seg c.work (bA + kN) (bA + kN + (lA - kN))) := by
        rw [show bA + kN + (lA - kN) = bA + lA by omega]
        exact (srt_split (by omega) (by omega) hA).2
      have hB' : Srt le (seg c.work (bA + kN + (lA - kN)) (bA + kN + (lA - kN) + lbN)) := by
        rw [show bA + kN + (lA - kN) = bA + lA by omega]
        exact (srt_split (by omega) (by omega) hB).1
      have h0 : oleq le (c.work.getD (bA + kN) none) (c.work.getD (bA + kN + (lA - kN)) none) = false := by
        rw [show bA + kN + (lA - kN) = bA + lA by omega, hv1]
        have := hgr kN (Nat.le_refl _) (by omega)
        simpa [gp] using this
      have hlast : ∀ y ∈ seg c.work (bA + kN + (lA - kN)) (bA + kN + (lA - kN) + lbN),
          oleq le (c.work.getD (bA + kN + (lA - kN) - 1) none) y = false := by
        intro y hy
        rw [show bA + kN + (lA - kN) - 1 = bA + lA - 1 by omega, hv2]
        rw [show bA + kN + (lA - kN) = bA + lA by omega] at hy
        obtain ⟨i, hi1, hi2, hi⟩ := mem_seg.1 hy
        have := hgl2 (i - (bA + lA)) (by omega)
        rw [show bA + lA + (i - (bA + lA)) = i by omega, getD_of_getElem? hi] at this
        simpa [gp] using this
      have hfin : ∀ c' : Core, PermOn c.work c'.work (bA + kN) (bA + kN + (lA - kN) + lbN) →
          seg c'.work (bA + kN) (bA + kN + (lA - kN) + lbN) = List.merge (seg c.work (bA + kN) (bA + kN + (lA - kN)))
            (seg c.work (bA + kN + (lA - kN)) (bA + kN + (lA - kN) + lbN)) (oleq le) →
          c'.runs = c.runs → c'.powers = c.powers → c'.size = c.size →
          seg c'.work bA (bA + lA + lB) =
            List.merge (seg c.work bA (bA + lA)) (seg c.work (bA + lA) (bA + lA + lB)) (oleq le) ∧
          (∀ i, (i < bA ∨ bA + lA + lB ≤ i) → c'.work[i]? = c.work[i]?) ∧ c'.work.length = c.work.length ∧
          c'.runs = c.runs ∧ c'.size = c.size ∧ c'.powers = c.powers := by
        intro c' hp hs hr hpw hsz
        refine ⟨?_, fun i hi => hp.out i (by omega), hp.len, hr, hsz, hpw⟩
        rw [hfull, seg_split c'.work (show bA ≤ bA + kN by omega) (show bA + kN ≤ bA + lA + lB by omega),
          seg_split c'.work (show bA + kN ≤ bA + lA + lbN by omega) (show bA + lA + lbN ≤ bA + lA + lB by omega),
          show bA + lA + lbN = bA + kN + (lA - kN) + lbN by omega, hs, show bA + kN + (lA - kN) = bA + lA by omega,
          seg_congr (l' := c'.work) (l := c.work) (lo := bA) (hi := bA + kN) fun i h1 h2 => hp.out i (by omega),
          seg_congr (l' := c'.work) (l := c.work) (lo := bA + lA + lbN) (hi := bA + lA + lB)
            fun i h1 h2 => hp.out i (by omega), List.append_assoc]
      rw [post_ite]
      split
      · refine (post_and (post_of_good (mergeLow_good cmp smiMax (e := e3) (by omega) (by omega) hv'))
          (mergeLow_post cmp smiMax hle hc (by omega) (by omega) hv' hA' hB' h0 hlast)).mono ?_
        rintro _ _ c' ⟨⟨hp, hr, hpw, hsz⟩, hs⟩
        exact hfin c' hp hs hr hpw hsz
      · refine (post_and (post_of_good (mergeHigh_good cmp smiMax (e := e3) (by omega) (by omega) hv'))
          (mergeHigh_post cmp smiMax hle hc (by omega) (by omega) hv' hA' hB' h0 hlast)).mono ?_
        rintro _ _ c' ⟨⟨hp, hr, hpw, hsz⟩, hs⟩
        exact hfin c' hp hs hr hpw hsz

end

end ArraySort
