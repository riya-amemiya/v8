import ArraySort.SortMergeLow

namespace ArraySort

open Torque

def HO (le : Val → Val → Bool) (M0 : List (Option Val)) (k : MCtx) (w : List (Option Val)) (la lb : Nat) : Prop :=
  List.merge (seg w k.baseA (k.baseA + la)) (seg k.T 0 lb) (oleq le) ++ seg w (k.baseA + la + lb) k.endPos = M0 ∧
    Srt le (seg w k.baseA (k.baseA + la)) ∧ Srt le (seg k.T 0 lb) ∧
    ∀ x ∈ seg w k.baseA (k.baseA + la), oleq le x (k.T.getD 0 none) = false

def HighOrd (le : Val → Val → Bool) (M0 : List (Option Val)) (k : MCtx) (c : Core) (s : MS) : Prop :=
  HO le M0 k c.work s.la.toNat s.lb.toNat

def HGOrd (le : Val → Val → Bool) (M0 : List (Option Val)) (k : MCtx) : GStep → Core → Prop
  | .exit x, c => HighOrd le M0 k c x.st
  | .cont s _ _, c => HighOrd le M0 k c s

section

variable {le : Val → Val → Bool} {M0 : List (Option Val)} {k : MCtx}

theorem highOrd_of {c : Core} {s : MS} {la lb : Nat} (h1 : s.la = la) (h2 : s.lb = lb)
    (h : HO le M0 k c.work la lb) : HighOrd le M0 k c s := by
  unfold HighOrd
  rw [h1, h2]
  simpa using h

theorem ho_of {c : Core} {s : MS} {la lb : Nat} (h1 : s.la = la) (h2 : s.lb = lb) (h : HighOrd le M0 k c s) :
    HO le M0 k c.work la lb := by
  unfold HighOrd at h
  rw [h1, h2] at h
  simpa using h

theorem seg_snoc' {l : List (Option Val)} {lo hi : Nat} (h1 : lo < hi) (h2 : hi ≤ l.length) :
    seg l lo hi = seg l lo (hi - 1) ++ [l.getD (hi - 1) none] := by
  have := seg_snoc_getD (l := l) (lo := lo) (hi := hi - 1) (by omega) (by omega)
  rwa [show hi - 1 + 1 = hi by omega] at this

theorem srt_snoc_le (hle : TotalPreorder le) {l : List (Option Val)} {z : Option Val} (h : Srt le (l ++ [z])) :
    ∀ y ∈ l ++ [z], oleq le y z = true := by
  intro y hy
  unfold Srt at h
  rw [List.pairwise_append] at h
  rcases List.mem_append.1 hy with hy | hy
  · exact h.2.2 y hy z (by simp)
  · simp only [List.mem_singleton] at hy
    subst hy
    exact oleq_refl hle _

theorem HO.moveA (hle : TotalPreorder le) {w : List (Option Val)} {la lb : Nat} (h : HO le M0 k w la lb)
    (hla : 1 ≤ la) (hpos : k.baseA + la + lb ≤ k.endPos) (hw : k.endPos ≤ w.length)
    (hord : 1 ≤ lb → oleq le (w.getD (k.baseA + la - 1) none) (k.T.getD (lb - 1) none) = false)
    (hT : lb ≤ k.T.length) :
    HO le M0 k (w.set (k.baseA + la + lb - 1) (w.getD (k.baseA + la - 1) none)) (la - 1) lb := by
  obtain ⟨o1, o2, o3, o4⟩ := h
  unfold HO
  rw [show k.baseA + (la - 1) = k.baseA + la - 1 by omega]
  have hRA : seg w k.baseA (k.baseA + la) = seg w k.baseA (k.baseA + la - 1) ++ [w.getD (k.baseA + la - 1) none] :=
    seg_snoc' (by omega) (by omega)
  have hRA' : seg (w.set (k.baseA + la + lb - 1) (w.getD (k.baseA + la - 1) none)) k.baseA (k.baseA + la - 1) =
      seg w k.baseA (k.baseA + la - 1) := seg_set_out (Or.inr (by omega))
  have hout : seg (w.set (k.baseA + la + lb - 1) (w.getD (k.baseA + la - 1) none)) (k.baseA + la - 1 + lb)
      k.endPos = w.getD (k.baseA + la - 1) none :: seg w (k.baseA + la + lb) k.endPos := by
    rw [show k.baseA + la - 1 + lb = k.baseA + la + lb - 1 by omega, seg_set_cons (by omega) (by omega),
      show k.baseA + la + lb - 1 + 1 = k.baseA + la + lb by omega]
  rw [hRA] at o1 o2 o4
  refine ⟨?_, ?_, o3, ?_⟩
  · rw [hRA', hout, ← o1, merge_drop_left (oleq le) (fun y hy x hx => ?_), List.append_assoc]
    · rfl
    · simp only [List.mem_singleton] at hx
      subst hx
      rcases Nat.eq_zero_or_pos lb with hl0 | hl0
      · subst hl0
        rw [seg_self] at hy
        cases hy
      · rw [show lb = (lb - 1) + 1 by omega, seg_snoc_getD (by omega) (by omega)] at hy o3
        exact oleq_false_of_le' hle (hord hl0) (srt_snoc_le hle o3 y hy)
  · rw [hRA']
    unfold Srt at o2 ⊢
    exact (List.pairwise_append.1 o2).1
  · rw [hRA']
    exact fun x hx => o4 x (List.mem_append_left _ hx)

theorem HO.moveB (hle : TotalPreorder le) {w : List (Option Val)} {la lb : Nat} (h : HO le M0 k w la lb)
    (hlb : 1 ≤ lb) (hpos : k.baseA + la + lb ≤ k.endPos) (hw : k.endPos ≤ w.length) (hT : lb ≤ k.T.length)
    (hord : 1 ≤ la → oleq le (w.getD (k.baseA + la - 1) none) (k.T.getD (lb - 1) none) = true) :
    HO le M0 k (w.set (k.baseA + la + lb - 1) (k.T.getD (lb - 1) none)) la (lb - 1) := by
  obtain ⟨o1, o2, o3, o4⟩ := h
  have hRB : seg k.T 0 lb = seg k.T 0 (lb - 1) ++ [k.T.getD (lb - 1) none] := by
    rw [show lb = (lb - 1) + 1 by omega, seg_snoc_getD (by omega) (by omega), Nat.add_sub_cancel]
  have hRA' : seg (w.set (k.baseA + la + lb - 1) (k.T.getD (lb - 1) none)) k.baseA (k.baseA + la) =
      seg w k.baseA (k.baseA + la) := seg_set_out (Or.inr (by omega))
  have hout : seg (w.set (k.baseA + la + lb - 1) (k.T.getD (lb - 1) none)) (k.baseA + la + (lb - 1))
      k.endPos = k.T.getD (lb - 1) none :: seg w (k.baseA + la + lb) k.endPos := by
    rw [show k.baseA + la + (lb - 1) = k.baseA + la + lb - 1 by omega, seg_set_cons (by omega) (by omega),
      show k.baseA + la + lb - 1 + 1 = k.baseA + la + lb by omega]
  rw [hRB] at o1 o3
  refine ⟨?_, by rw [hRA']; exact o2, ?_, by rw [hRA']; exact o4⟩
  · rw [hRA', hout, ← o1, merge_drop_right (oleq le) (fun x hx y hy => ?_), List.append_assoc]
    · rfl
    · simp only [List.mem_singleton] at hy
      subst hy
      rcases Nat.eq_zero_or_pos la with hl0 | hl0
      · subst hl0
        rw [Nat.add_zero, seg_self] at hx
        cases hx
      · have hRA := seg_snoc' (l := w) (lo := k.baseA) (hi := k.baseA + la) (by omega) (by omega)
        rw [hRA] at hx o2
        exact oleq_trans hle _ _ _ (srt_snoc_le hle o2 x hx) (hord hl0)
  · unfold Srt at o3 ⊢
    exact (List.pairwise_append.1 o3).1

theorem HO.copyA (hle : TotalPreorder le) {w : List (Option Val)} {la lb n : Nat} (h : HO le M0 k w la lb)
    (hn : n ≤ la) (hpos : k.baseA + la + lb ≤ k.endPos) (hw : k.endPos ≤ w.length) (hT : lb ≤ k.T.length)
    (hord : 1 ≤ lb → ∀ i, la - n ≤ i → i < la → oleq le (w.getD (k.baseA + i) none) (k.T.getD (lb - 1) none) = false) :
    HO le M0 k (over w (k.baseA + la + lb - n) (seg w (k.baseA + la - n) (k.baseA + la - n + n))) (la - n) lb := by
  obtain ⟨o1, o2, o3, o4⟩ := h
  have hlen : (seg w (k.baseA + la - n) (k.baseA + la - n + n)).length = n := by rw [length_seg (by omega)]; omega
  have hl : k.baseA + la + lb - n + (seg w (k.baseA + la - n) (k.baseA + la - n + n)).length ≤ w.length := by
    rw [hlen]; omega
  have hsplit : seg w k.baseA (k.baseA + la) =
      seg w k.baseA (k.baseA + (la - n)) ++ seg w (k.baseA + la - n) (k.baseA + la - n + n) := by
    rw [show k.baseA + la - n + n = k.baseA + la by omega, show k.baseA + (la - n) = k.baseA + la - n by omega]
    exact seg_split _ (by omega) (by omega)
  have hRA' : seg (over w (k.baseA + la + lb - n) (seg w (k.baseA + la - n) (k.baseA + la - n + n))) k.baseA
      (k.baseA + (la - n)) = seg w k.baseA (k.baseA + (la - n)) := seg_over_out hl (Or.inl (by omega))
  have hout : seg (over w (k.baseA + la + lb - n) (seg w (k.baseA + la - n) (k.baseA + la - n + n)))
      (k.baseA + (la - n) + lb) k.endPos =
      seg w (k.baseA + la - n) (k.baseA + la - n + n) ++ seg w (k.baseA + la + lb) k.endPos := by
    rw [show k.baseA + (la - n) + lb = k.baseA + la + lb - n by omega, seg_over_right hl (by rw [hlen]; omega),
      hlen, show k.baseA + la + lb - n + n = k.baseA + la + lb by omega]
  rw [hsplit] at o1 o2 o4
  refine ⟨?_, by rw [hRA']; unfold Srt at o2 ⊢; exact (List.pairwise_append.1 o2).1, o3,
    by rw [hRA']; exact fun x hx => o4 x (List.mem_append_left _ hx)⟩
  rw [hRA', hout, ← o1, merge_drop_left (oleq le) (fun y hy x hx => ?_), List.append_assoc]
  obtain ⟨i, hi1, hi2, hi⟩ := mem_seg.1 hx
  rcases Nat.eq_zero_or_pos lb with hl0 | hl0
  · subst hl0
    rw [seg_self] at hy
    cases hy
  · have hx' := hord hl0 (i - k.baseA) (by omega) (by omega)
    rw [show k.baseA + (i - k.baseA) = i by omega, getD_of_getElem? hi] at hx'
    rw [show lb = (lb - 1) + 1 by omega, seg_snoc_getD (by omega) (by omega)] at hy o3
    exact oleq_false_of_le' hle hx' (srt_snoc_le hle o3 y hy)

theorem HO.copyB (hle : TotalPreorder le) {w : List (Option Val)} {la lb n : Nat} (h : HO le M0 k w la lb)
    (hn : n ≤ lb) (hpos : k.baseA + la + lb ≤ k.endPos) (hw : k.endPos ≤ w.length) (hT : lb ≤ k.T.length)
    (hord : 1 ≤ la → ∀ i, lb - n ≤ i → i < lb → oleq le (w.getD (k.baseA + la - 1) none) (k.T.getD i none) = true) :
    HO le M0 k (over w (k.baseA + la + lb - n) (seg k.T (lb - n) (lb - n + n))) la (lb - n) := by
  obtain ⟨o1, o2, o3, o4⟩ := h
  have hlen : (seg k.T (lb - n) (lb - n + n)).length = n := by rw [length_seg (by omega)]; omega
  have hl : k.baseA + la + lb - n + (seg k.T (lb - n) (lb - n + n)).length ≤ w.length := by rw [hlen]; omega
  have hsplit : seg k.T 0 lb = seg k.T 0 (lb - n) ++ seg k.T (lb - n) (lb - n + n) := by
    rw [show lb - n + n = lb by omega]
    exact seg_split _ (by omega) (by omega)
  have hRA' : seg (over w (k.baseA + la + lb - n) (seg k.T (lb - n) (lb - n + n))) k.baseA (k.baseA + la) =
      seg w k.baseA (k.baseA + la) := seg_over_out hl (Or.inl (by omega))
  have hout : seg (over w (k.baseA + la + lb - n) (seg k.T (lb - n) (lb - n + n))) (k.baseA + la + (lb - n))
      k.endPos = seg k.T (lb - n) (lb - n + n) ++ seg w (k.baseA + la + lb) k.endPos := by
    rw [show k.baseA + la + (lb - n) = k.baseA + la + lb - n by omega, seg_over_right hl (by rw [hlen]; omega),
      hlen, show k.baseA + la + lb - n + n = k.baseA + la + lb by omega]
  rw [hsplit] at o1 o3
  refine ⟨?_, by rw [hRA']; exact o2, by unfold Srt at o3 ⊢; exact (List.pairwise_append.1 o3).1,
    by rw [hRA']; exact o4⟩
  rw [hRA', hout, ← o1, merge_drop_right (oleq le) (fun x hx y hy => ?_), List.append_assoc]
  obtain ⟨i, hi1, hi2, hi⟩ := mem_seg.1 hy
  rcases Nat.eq_zero_or_pos la with hl0 | hl0
  · subst hl0
    rw [Nat.add_zero, seg_self] at hx
    cases hx
  · have hy' := hord hl0 i (by omega) (by omega)
    rw [getD_of_getElem? hi] at hy'
    have hRA := seg_snoc' (l := w) (lo := k.baseA) (hi := k.baseA + la) (by omega) (by omega)
    rw [hRA] at hx o2
    exact oleq_trans hle _ _ _ (srt_snoc_le hle o2 x hx) hy'

theorem HO.final {w : List (Option Val)} {la : Nat} (h : HO le M0 k w la 0) (hpos : k.baseA + la ≤ k.endPos) :
    seg w k.baseA k.endPos = M0 := by
  obtain ⟨o1, -, -, -⟩ := h
  rw [seg_self, List.merge_right, Nat.add_zero] at o1
  rw [seg_split w (show k.baseA ≤ k.baseA + la by omega) hpos]
  exact o1

end

section

variable {ε : Type} (cmp : Cmp ε) (smiMax : Nat) {le : Val → Val → Bool} {M0 : List (Option Val)}

theorem highGallopC_post (hle : TotalPreorder le) {k : MCtx} (s : MS) (na pa nb pb : Int) (e : ε) (c : Core)
    (h : HighInv k c ⟨s.dest - pa - 1 - pb, s.ct - 1 - pb, s.cur - pa, s.la - pa, s.lb - 1 - pb⟩)
    (ho : HighOrd le M0 k c ⟨s.dest - pa - 1 - pb, s.ct - 1 - pb, s.cur - pa, s.la - pa, s.lb - 1 - pb⟩)
    (hla : 1 ≤ s.la - pa) (hlb : 2 ≤ s.lb - 1 - pb)
    (hord : oleq le (c.work.getD (s.cur - pa).toNat none) (k.T.getD (s.ct - 1 - pb).toNat none) = false) :
    ((highGallopC s na pa nb pb : M ε GStep) e c).Post (fun r _ c' => HGOrd le M0 k r c') := by
  obtain ⟨la, lb, e1, e2, e3, e4, e5, g1, g2, g3, g4, g5, g6⟩ := h.ghosts
  try simp only at e1 e2 e3 e4 e5
  have ho' := ho_of (s := ⟨s.dest - pa - 1 - pb, s.ct - 1 - pb, s.cur - pa, s.la - pa, s.lb - 1 - pb⟩) e1 e2 ho
  rw [show (s.cur - pa).toNat = k.baseA + la - 1 by omega, show (s.ct - 1 - pb).toNat = lb - 1 by omega] at hord
  have hn := HO.moveA hle ho' (by omega) g1 (by omega) (fun _ => hord) (by omega)
  unfold highGallopC
  rw [post_bind, post_mv]
  intro _ _
  simp only [Core.get_work, Core.put_work]
  rw [show (s.cur - pa).toNat = k.baseA + la - 1 by omega,
    show (s.dest - pa - 1 - pb).toNat = k.baseA + la + lb - 1 by omega]
  rw [post_ite]
  split
  · rw [post_pure]
    exact highOrd_of (by simp only [Exit.st]; omega) (by simp only [Exit.st]; omega) hn
  · rw [post_pure]
    exact highOrd_of (by simp only; omega) (by simp only; omega) hn

theorem highGallopB_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {k : MCtx} (s : MS) (na pa : Int)
    (e : ε) (c : Core) (h : HighInv k c ⟨s.dest - pa, s.ct, s.cur - pa, s.la - pa, s.lb⟩)
    (ho : HighOrd le M0 k c ⟨s.dest - pa, s.ct, s.cur - pa, s.la - pa, s.lb⟩)
    (hla : 1 ≤ s.la - pa) (hlb : 2 ≤ s.lb)
    (hord : oleq le (c.work.getD (s.cur - pa).toNat none) (k.T.getD s.ct.toNat none) = true) :
    ((highGallopB cmp smiMax s na pa) e c).Post (fun r _ c' => HGOrd le M0 k r c') := by
  obtain ⟨la, lb, e1, e2, e3, e4, e5, g1, g2, g3, g4, g5, g6⟩ := h.ghosts
  try simp only at e1 e2 e3 e4 e5
  have ho' := ho_of (s := ⟨s.dest - pa, s.ct, s.cur - pa, s.la - pa, s.lb⟩) e1 e2 ho
  rw [show (s.cur - pa).toNat = k.baseA + la - 1 by omega, show s.ct.toNat = lb - 1 by omega] at hord
  have hn := HO.moveB hle ho' (by omega) g1 (by omega) (by omega) fun _ => hord
  unfold highGallopB
  rw [post_bind, post_mv]
  intro _ _
  simp only [Core.get_work, Core.get_temp, Core.put_work]
  rw [show s.ct.toNat = lb - 1 by omega, show (s.dest - pa).toNat = k.baseA + la + lb - 1 by omega,
    show c.temp.getD (lb - 1) none = k.T.getD (lb - 1) none by rw [g3]]
  have hi := h.moveB (la := la) (lb := lb) (by osos) (by osos) (by omega)
  rw [post_ite]
  split
  · rw [post_pure]
    exact highOrd_of (by simp only [Exit.st]; omega) (by simp only [Exit.st]; omega) hn
  · simp only [post_bind, post_ld, post_jsAny, post_dcheck, Core.get_work]
    intro _ v hv
    rw [show (s.cur - pa).toNat = k.baseA + la - 1 by omega] at hv
    have haL : (c.work.set (k.baseA + la + lb - 1) (k.T.getD (lb - 1) none)).getD (k.baseA + la - 1) none =
        c.work.getD (k.baseA + la - 1) none := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_set, ite_eq_right (by omega), ← List.getD_eq_getElem?_getD]
    have hsrt : SrtAt le ({ c with work := c.work.set (k.baseA + la + lb - 1) (k.T.getD (lb - 1) none) }.get .temp)
        0 (0 + (lb - 1)) := by
      simp only [Core.get_temp]
      rw [g3, Nat.zero_add]
      exact srtAt_of_srt hle (by omega) hn.2.2.1
    have hgal := gallop_post cmp smiMax hle hc (isRight := false) (key := v) (base := 0) (length := lb - 1)
      (hint := lb - 2) (e := e) hsrt
    rw [show ((lb - 1 : Nat) : Int) = s.lb - 1 by omega, show ((lb - 2 : Nat) : Int) = s.lb - 2 by omega,
      show ((0 : Nat) : Int) = 0 by rfl] at hgal
    refine hgal.mono ?_
    rintro k2 e2 c2 ⟨hc2, k2N, hk2, hk2N, hgl, hgr⟩
    subst c2
    subst hk2
    simp only [Core.get_temp, Nat.zero_add] at hgl hgr
    rw [g3] at hgl hgr
    intro _
    have hcB : 1 ≤ la → ∀ i, lb - 1 - (lb - 1 - k2N) ≤ i → i < lb - 1 →
        oleq le ((c.work.set (k.baseA + la + lb - 1) (k.T.getD (lb - 1) none)).getD (k.baseA + la - 1) none)
          (k.T.getD i none) = true := by
      intro _ i hi1 hi2
      rw [hv]
      have := hgr i (by omega) hi2
      simpa [gp] using this
    have hn2 := HO.copyB hle (n := lb - 1 - k2N) hn (by omega) (by omega)
      (by simp; omega) (by omega) hcB
    have hi2 := hi.copyB (la := la) (lb := lb - 1) (n := lb - 1 - k2N) (by osos) (by osos) (by omega)
    refine Res.Post.mono (Q := fun _ _ c3 =>
      HighInv k c3 ⟨s.dest - pa - 1 - max (s.lb - 1 - (k2N : Int)) 0, s.ct - 1 - max (s.lb - 1 - (k2N : Int)) 0,
        s.cur - pa, s.la - pa, s.lb - 1 - max (s.lb - 1 - (k2N : Int)) 0⟩ ∧
      HighOrd le M0 k c3 ⟨s.dest - pa - 1 - max (s.lb - 1 - (k2N : Int)) 0,
        s.ct - 1 - max (s.lb - 1 - (k2N : Int)) 0, s.cur - pa, s.la - pa, s.lb - 1 - max (s.lb - 1 - (k2N : Int)) 0⟩ ∧
      c3.work.getD (k.baseA + la - 1) none = some v) ?_ ?_
    · rintro _ e3 c3 ⟨hinv3, hord3, hv3⟩
      rw [post_ite]
      split
      · rw [post_pure]
        exact hord3
      · rw [post_ite]
        split
        · rw [post_pure]
          exact hord3
        · refine highGallopC_post hle s _ pa _ _ e3 c3 hinv3 hord3 hla (by omega) ?_
          rw [show (s.cur - pa).toNat = k.baseA + la - 1 by omega,
            show (s.ct - 1 - max (s.lb - 1 - (k2N : Int)) 0).toNat = k2N - 1 by omega, hv3]
          have := hgl (k2N - 1) (by omega)
          simpa [gp] using this
    · rw [post_doIf]
      split
      · refine post_of_good (copy_good_int (spN := lb - 1 - (lb - 1 - k2N))
          (dpN := k.baseA + la + (lb - 1) - (lb - 1 - k2N)) (nN := lb - 1 - k2N)
          (Q := fun _ _ c3 => c3 = { c with work := over (c.work.set (k.baseA + la + lb - 1) (k.T.getD (lb - 1) none)) (k.baseA + la + (lb - 1) - (lb - 1 - k2N)) (seg k.T (lb - 1 - (lb - 1 - k2N)) (lb - 1 - (lb - 1 - k2N) + (lb - 1 - k2N))) })
          (by omega) (by omega) (by omega) (by simp; rw [g3]; omega) (by simp; omega) (by simp [g3])) |>.mono ?_
        rintro _ e3 c3 rfl
        refine ⟨hi2.congr (by osos) (by osos) rfl rfl (by osos),
          highOrd_of (by simp only; omega) (by simp only; omega) hn2, ?_⟩
        simp only
        rw [getD_over_out (by rw [length_seg (by omega)]; simp; omega) (Or.inl (by omega)), hv]
      · have : k2N = lb - 1 := by omega
        subst this
        refine ⟨hi.congr (by osos) (by osos) rfl rfl (by osos), highOrd_of (by simp only; omega) (by simp only; omega)
          hn, by simp only; rw [hv]⟩

theorem highGallopStep_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {k : MCtx} (s : MS) (e : ε) (c : Core)
    (h : HighInv k c s) (ho : HighOrd le M0 k c s) (hla : 0 < s.la) (hlb : 1 < s.lb) :
    ((highGallopStep cmp smiMax (k.baseA : Int) s) e c).Post (fun r _ c' => HGOrd le M0 k r c') := by
  obtain ⟨la, lb, e1, e2, e3, e4, e5, g1, g2, g3, g4, g5, g6⟩ := h.ghosts
  have ho' := ho_of e1 e2 ho
  unfold highGallopStep
  simp only [post_bind, post_ld, post_jsAny, Core.get_temp]
  intro _ v hv
  rw [show s.ct.toNat = lb - 1 by omega, g3] at hv
  have hsrt : SrtAt le (c.get .work) k.baseA (k.baseA + la) := by
    simp only [Core.get_work]
    exact srtAt_of_srt hle (by omega) ho'.2.1
  have hgal := gallop_post cmp smiMax hle hc (isRight := true) (key := v) (base := k.baseA) (length := la)
    (hint := la - 1) (e := e) hsrt
  rw [show ((la : Nat) : Int) = s.la by omega, show ((la - 1 : Nat) : Int) = s.la - 1 by omega] at hgal
  refine hgal.mono ?_
  rintro kk e2' c2 ⟨hc2, kN, hkk, hkN, hgl, hgr⟩
  subst c2
  subst hkk
  simp only [Core.get_work] at hgl hgr
  rw [post_dcheck]
  intro _
  have hcA : 1 ≤ lb → ∀ i, la - (la - kN) ≤ i → i < la →
      oleq le (c.work.getD (k.baseA + i) none) (k.T.getD (lb - 1) none) = false := by
    intro _ i hi1 hi2
    rw [hv]
    have := hgr i (by omega) hi2
    simpa [gp] using this
  have hn := HO.copyA hle (n := la - kN) ho' (by omega) g1 (by omega) (by omega) hcA
  have hi := h.copyA (la := la) (lb := lb) (n := la - kN) e1 e2 (by omega)
  refine Res.Post.mono (Q := fun _ _ c3 =>
    HighInv k c3 ⟨s.dest - max (s.la - (kN : Int)) 0, s.ct, s.cur - max (s.la - (kN : Int)) 0,
      s.la - max (s.la - (kN : Int)) 0, s.lb⟩ ∧
    HighOrd le M0 k c3 ⟨s.dest - max (s.la - (kN : Int)) 0, s.ct, s.cur - max (s.la - (kN : Int)) 0,
      s.la - max (s.la - (kN : Int)) 0, s.lb⟩ ∧
    (1 ≤ kN → c3.work.getD (k.baseA + kN - 1) none = c.work.getD (k.baseA + kN - 1) none)) ?_ ?_
  · rintro _ e3 c3 ⟨hinv3, hord3, hv3⟩
    rw [post_ite]
    split
    · rw [post_pure]
      exact hord3
    · refine highGallopB_post cmp smiMax hle hc s _ _ e3 c3 hinv3 hord3 (by omega) hlb ?_
      rw [show (s.cur - max (s.la - (kN : Int)) 0).toNat = k.baseA + kN - 1 by omega, hv3 (by omega),
        show s.ct.toNat = lb - 1 by omega, hv]
      have := hgl (kN - 1) (by omega)
      rw [show k.baseA + (kN - 1) = k.baseA + kN - 1 by omega] at this
      simpa [gp] using this
  · rw [post_doIf]
    split
    · refine post_of_good (copy_good_int (src := .work) (dst := .work) (c := c) (e := e2')
        (spN := k.baseA + la - (la - kN)) (dpN := k.baseA + la + lb - (la - kN))
        (nN := la - kN) (Q := fun _ _ c3 => c3 = { c with work := over c.work (k.baseA + la + lb - (la - kN)) (seg c.work (k.baseA + la - (la - kN)) (k.baseA + la - (la - kN) + (la - kN))) })
        (by omega) (by omega) (by omega) (by simp; omega) (by simp; omega) (by simp)) |>.mono ?_
      rintro _ e3 c3 rfl
      refine ⟨hi.congr (by osos) rfl (by osos) (by osos) rfl, highOrd_of (by simp only; omega) (by simp only; omega) hn,
        fun _ => ?_⟩
      simp only
      rw [getD_over_out (by rw [length_seg (by omega)]; omega) (Or.inl (by omega))]
    · have : kN = la := by omega
      refine ⟨h.congr (by osos) rfl (by osos) (by osos) rfl,
        highOrd_of (la := la) (lb := lb) (by simp only; omega) (by simp only; omega) ho', fun _ => rfl⟩

theorem highLoop_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {k : MCtx} (hv : Vals k.w0 k.baseA k.endPos) :
    ∀ (mg : Int) (ph : Ph) (s : MS) (e : ε) (c : Core), HighInv k c s → HighOrd le M0 k c s → 0 < s.la →
      1 < s.lb → ((highLoop cmp smiMax (k.baseA : Int) mg ph s) e c).Post (fun x _ c' => HighOrd le M0 k c' x.st)
  | mg, .simple wa wb, s, e, c, hinv, ho, hla, hlb => by
    obtain ⟨la, lb, e1, e2, e3, e4, e5, g1, g2, g3, g4, g5, g6⟩ := hinv.ghosts
    have ho' := ho_of e1 e2 ho
    rw [highLoop, dite_eq_left ⟨hla, hlb⟩]
    simp only [post_bind, post_ld, post_jsAny, post_compare, Core.get_work, Core.get_temp]
    intro _ v1 hv1 _ v2 hv2 o e' ho2
    rw [show s.ct.toNat = lb - 1 by omega, g3] at hv1
    rw [show s.cur.toNat = k.baseA + la - 1 by omega] at hv2
    have hg := hc _ _ _ _ _ ho2
    rw [post_ite]
    split
    · next hlt =>
      rw [post_bind, post_mv]
      intro _ _
      simp only [Core.get_work, Core.put_work]
      rw [show s.cur.toNat = k.baseA + la - 1 by omega, show s.dest.toNat = k.baseA + la + lb - 1 by omega]
      have hi := hinv.moveA e1 e2 (by omega) (by omega)
      have hn := HO.moveA hle ho' (by omega) g1 (by omega) (fun _ => by rw [hv2, hv1]; exact hg.1 hlt) (by omega)
      have hon : HighOrd le M0 k { c with work := c.work.set (k.baseA + la + lb - 1) (c.work.getD (k.baseA + la - 1) none) }
          ⟨s.dest - 1, s.ct, s.cur - 1, s.la - 1, s.lb⟩ :=
        highOrd_of (by simp only; omega) (by simp only; omega) hn
      rw [post_ite]
      split
      · rw [post_pure]
        exact hon
      · rw [post_ite]
        split
        · exact highLoop_post hle hc hv _ _ _ e' _ hi hon (by osos) (by osos)
        · exact highLoop_post hle hc hv _ _ _ e' _ hi hon (by osos) (by osos)
    · next hlt =>
      rw [post_bind, post_mv]
      intro _ _
      simp only [Core.get_work, Core.get_temp, Core.put_work]
      rw [show s.ct.toNat = lb - 1 by omega, show s.dest.toNat = k.baseA + la + lb - 1 by omega,
        show c.temp.getD (lb - 1) none = k.T.getD (lb - 1) none by rw [g3]]
      have hi := hinv.moveB e1 e2 (by omega)
      have hn := HO.moveB hle ho' (by omega) g1 (by omega) (by omega) fun _ => by
        rw [hv2, hv1]
        cases h : le v2 v1
        · exact absurd (hg.2 h) hlt
        · exact h
      have hon : HighOrd le M0 k { c with work := c.work.set (k.baseA + la + lb - 1) (k.T.getD (lb - 1) none) }
          ⟨s.dest - 1, s.ct - 1, s.cur, s.la, s.lb - 1⟩ :=
        highOrd_of (by simp only; omega) (by simp only; omega) hn
      rw [post_ite]
      split
      · rw [post_pure]
        exact hon
      · rw [post_ite]
        split
        · exact highLoop_post hle hc hv _ _ _ e' _ hi hon (by osos) (by osos)
        · exact highLoop_post hle hc hv _ _ _ e' _ hi hon (by osos) (by osos)
  | mg, .gallop first wa wb, s, e, c, hinv, ho, hla, hlb => by
    rw [highLoop, post_ite]
    split
    · simp only [post_bind, post_dcheck, post_setMinGallop]
      intro _
      refine (post_and (post_of_good (highGallopStep_good cmp smiMax hv s e { c with minGallop := max 1 (mg - 1) }
        (hinv.minGallop (g := max 1 (mg - 1))) hla hlb))
        (highGallopStep_post cmp smiMax hle hc s e { c with minGallop := max 1 (mg - 1) }
          (hinv.minGallop (g := max 1 (mg - 1))) ho hla hlb)).mono ?_
      rintro r e' c' ⟨hr, hro⟩
      cases r with
      | exit x => exact hro
      | cont s' na nb =>
        obtain ⟨hinv', hla', hlb', hlt⟩ := hr
        dsimp only
        rw [dite_eq_left hlt]
        exact highLoop_post hle hc hv _ _ _ e' _ hinv' hro hla' hlb'
    · simp only [post_bind, post_setMinGallop]
      exact highLoop_post hle hc hv _ _ _ e _ hinv.minGallop ho hla hlb
termination_by _ ph s => 2 * (s.la.toNat + s.lb.toNat) + ph.rank
decreasing_by all_goals simp only [Ph.rank]; omega

theorem mergeHigh_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {baseA la0 lb0 : Nat} {c : Core} {e : ε}
    (hla : 0 < la0) (hlb : 0 < lb0) (hv : Vals c.work baseA (baseA + la0 + lb0))
    (hA : Srt le (seg c.work baseA (baseA + la0))) (hB : Srt le (seg c.work (baseA + la0) (baseA + la0 + lb0)))
    (h0 : oleq le (c.work.getD baseA none) (c.work.getD (baseA + la0) none) = false)
    (hlast : ∀ y ∈ seg c.work (baseA + la0) (baseA + la0 + lb0),
      oleq le (c.work.getD (baseA + la0 - 1) none) y = false) :
    ((mergeHigh cmp smiMax (baseA : Int) (la0 : Int) ((baseA + la0 : Nat) : Int) (lb0 : Int)) e c).Post
      (fun _ _ c' => seg c'.work baseA (baseA + la0 + lb0) =
        List.merge (seg c.work baseA (baseA + la0)) (seg c.work (baseA + la0) (baseA + la0 + lb0)) (oleq le)) := by
  have hl := hv.1
  unfold mergeHigh
  simp only [post_bind, post_dcheck]
  intro _ _ _
  refine post_of_good (getTempArray_spec fun t ht => ?_)
  have hlenS : (seg c.work (baseA + la0) (baseA + la0 + lb0)).length = lb0 := by
    rw [length_seg (by omega)]; omega
  have hTl : (over t 0 (seg c.work (baseA + la0) (baseA + la0 + lb0))).length = t.length :=
    length_over (by rw [hlenS]; omega)
  refine (post_of_good (copy_good (sp := baseA + la0) (dp := 0) (n := lb0)
    (Q := fun _ e' c' => e' = e ∧ c' = { c with temp := over t 0 (seg c.work (baseA + la0) (baseA + la0 + lb0)) })
    (by simp only [Core.get_work]; omega) (by simp only [Core.get_temp]; omega) ⟨rfl, rfl⟩)).mono ?_
  rintro _ e1 c1 ⟨rfl, rfl⟩
  let k : MCtx := ⟨c.work, over t 0 (seg c.work (baseA + la0) (baseA + la0 + lb0)), baseA, lb0,
    baseA + la0 + lb0, c.runs, c.powers, c.size⟩
  have hRB : seg (over t 0 (seg c.work (baseA + la0) (baseA + la0 + lb0))) 0 lb0 =
      seg c.work (baseA + la0) (baseA + la0 + lb0) := by
    have := seg_over_in (l := t) (s := seg c.work (baseA + la0) (baseA + la0 + lb0)) (pos := 0)
      (by rw [hlenS]; omega)
    rwa [hlenS, Nat.zero_add] at this
  have hinv0 : HighInv k { c with temp := over t 0 (seg c.work (baseA + la0) (baseA + la0 + lb0)) }
      ⟨(baseA : Int) + la0 + lb0 - 1, (lb0 : Int) - 1, (baseA : Int) + la0 - 1, la0, lb0⟩ := by
    refine ⟨la0, lb0, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, rfl, by simp only [k]; omega,
      rfl, by simp only [k]; omega, fun _ _ => rfl, ?_, rfl, rfl, rfl⟩
    simp only [k, seg_self, List.append_nil]
    rw [hRB, ← seg_split c.work (Nat.le_add_right baseA la0) (by omega)]
  have hT0 : ∀ i, i < lb0 → k.T.getD i none = c.work.getD (baseA + la0 + i) none := by
    intro i hi
    simp only [k]
    rw [getD_over_in (by rw [hlenS]; omega) (Nat.zero_le _) (by rw [hlenS]; omega), Nat.sub_zero,
      getD_seg' (by omega)]
  have ho0 : HO le (List.merge (seg c.work baseA (baseA + la0)) (seg c.work (baseA + la0) (baseA + la0 + lb0))
      (oleq le)) k c.work la0 lb0 := by
    refine ⟨?_, hA, ?_, ?_⟩
    · simp only [k]
      rw [hRB, seg_self, List.append_nil]
    · simp only [k]
      rw [hRB]
      exact hB
    · intro x hx
      rw [hT0 0 hlb, Nat.add_zero]
      simp only [k] at hx
      rw [seg_cons_getD (by omega) (by omega)] at hx hA
      exact srt_cons_lt hle hA h0 x hx
  have hv' : Vals k.w0 k.baseA k.endPos := hv
  rw [post_mv]
  intro _ _
  simp only [Core.get_work, Core.put_work]
  rw [show ((baseA : Int) + (la0 : Int) - 1).toNat = k.baseA + la0 - 1 by simp only [k]; omega,
    show (((baseA + la0 : Nat) : Int) + (lb0 : Int) - 1).toNat = k.baseA + la0 + lb0 - 1 by simp only [k]; omega]
  have hinv1 := (hinv0.moveA (la := la0) (lb := lb0) rfl rfl hla hlb).congr
    (s' := ⟨((baseA + la0 : Nat) : Int) + lb0 - 2, (lb0 : Int) - 1, (baseA : Int) + la0 - 2, (la0 : Int) - 1,
      lb0⟩) (by osos) rfl (by osos) rfl rfl
  have ho1 := HO.moveA hle ho0 hla (by simp only [k]; omega) (by simp only [k]; omega) (fun _ => by
      rw [hT0 (lb0 - 1) (by omega)]
      apply hlast
      rw [mem_seg]
      exact ⟨baseA + la0 + (lb0 - 1), by omega, by omega, getElem?_eq_some_getD (by omega)⟩)
    (by simp only [k]; omega)
  let M0 := List.merge (seg c.work baseA (baseA + la0)) (seg c.work (baseA + la0) (baseA + la0 + lb0)) (oleq le)
  let c1 : Core := { c with temp := over t 0 (seg c.work (baseA + la0) (baseA + la0 + lb0)), work := c.work.set (k.baseA + la0 + lb0 - 1) (c.work.getD (k.baseA + la0 - 1) none) }
  have hho1 : HighOrd le M0 k c1 ⟨((baseA + la0 : Nat) : Int) + lb0 - 2, (lb0 : Int) - 1, (baseA : Int) + la0 - 2,
      (la0 : Int) - 1, lb0⟩ := highOrd_of (by osos) (by osos) ho1
  have hrun : (highRun cmp smiMax (baseA : Int) ⟨((baseA + la0 : Nat) : Int) + lb0 - 2, (lb0 : Int) - 1,
      (baseA : Int) + la0 - 2, (la0 : Int) - 1, lb0⟩ e1 c1).Post
      (fun x _ c' => HighPost k x c' ∧ HighOrd le M0 k c' x.st) := by
    rw [highRun, post_ite]
    split
    · exact ⟨⟨hinv1, Or.inl (by osos)⟩, hho1⟩
    · rw [post_ite]
      split
      · exact ⟨⟨hinv1, by osos, by osos⟩, hho1⟩
      · rw [post_bind, post_getMinGallop]
        exact post_and (post_of_good (highLoop_good cmp smiMax hv' _ _ _ e1 _ hinv1 (by osos) (by osos)))
          (highLoop_post cmp smiMax hle hc hv' _ _ _ e1 _ hinv1 hho1 (by osos) (by osos))
  refine hrun.mono ?_
  rintro x e2 c2 ⟨hx, hxo⟩
  cases x with
  | succeed s =>
    obtain ⟨hinv, hor⟩ := hx
    obtain ⟨la, lb, e1', e2', e3, e4, e5, g1, g2, g3, g4, g5, g6⟩ := hinv.ghosts
    have ho := ho_of e1' e2' hxo
    rw [highFinish, post_ite]
    split
    · simp only [post_bind, post_dcheck]
      intro hla0
      have : la = 0 := by omega
      subst this
      refine post_of_good (copy_good_int (spN := 0) (dpN := k.baseA) (nN := lb)
        (Q := fun _ _ c3 => c3 = { c2 with work := over c2.work (k.baseA + 0 + lb - lb) (seg k.T (lb - lb) (lb - lb + lb)) })
        rfl (by omega) e2' (by simp; rw [g3]; omega) (by simp; omega)
        (by simp only [Core.get_work, Core.get_temp, Core.put_work]; rw [g3, Nat.sub_self, Nat.add_zero, Nat.zero_add,
          Nat.add_sub_cancel])) |>.mono ?_
      rintro _ _ c3 rfl
      have ho2 := HO.copyB hle ho (n := lb) (Nat.le_refl _) (by omega) (by omega) (by omega)
        fun h => absurd h (by omega)
      simp only [Nat.sub_self] at ho2 ⊢
      exact ho2.final (by omega)
    · rw [post_pure]
      have : lb = 0 := by omega
      subst this
      exact ho.final (by omega)
  | copy s =>
    obtain ⟨hinv, hlb1, hla1⟩ := hx
    obtain ⟨la, lb, e1', e2', e3, e4, e5, g1, g2, g3, g4, g5, g6⟩ := hinv.ghosts
    have ho := ho_of e1' e2' hxo
    have hlb1' : lb = 1 := by omega
    subst hlb1'
    rw [highFinish]
    simp only [post_bind, post_dcheck]
    intro _
    refine post_of_good (copy_good_int (spN := k.baseA) (dpN := k.baseA + 1) (nN := la)
      (Q := fun _ _ c3 => c3 = { c2 with work := over c2.work (k.baseA + la + 1 - la) (seg c2.work (k.baseA + la - la) (k.baseA + la - la + la)) })
      (by omega) (by omega) e1' (by simp; omega) (by simp; omega)
      (by simp only [Core.get_work, Core.put_work]; rw [show k.baseA + la + 1 - la = k.baseA + 1 by omega,
        show k.baseA + la - la = k.baseA by omega])) |>.mono ?_
    rintro _ e3' c3 rfl
    have ho2 := HO.copyA hle ho (n := la) (Nat.le_refl _) (by omega) (by omega) (by omega) fun _ i _ hi2 => by
      have := ho.2.2.2 (c2.work.getD (k.baseA + i) none) (by
        rw [mem_seg]
        exact ⟨k.baseA + i, by omega, by omega, getElem?_eq_some_getD (by omega)⟩)
      simpa using this
    rw [post_mv]
    intro _ _
    simp only [Core.get_work, Core.get_temp, Core.put_work]
    rw [show s.ct.toNat = 1 - 1 by omega, show (s.dest - s.la).toNat = k.baseA + (la - la) + 1 - 1 by omega,
      show c2.temp.getD (1 - 1) none = k.T.getD (1 - 1) none by rw [g3]]
    have hlo : (over c2.work (k.baseA + la + 1 - la) (seg c2.work (k.baseA + la - la) (k.baseA + la - la + la))).length =
        c2.work.length := length_over (by rw [length_seg (by omega)]; omega)
    have ho3 := HO.moveB hle ho2 (Nat.le_refl _) (by omega) (by rw [hlo]; omega) (by omega)
      fun h => absurd h (by omega)
    exact ho3.final (by omega)

end

end ArraySort
