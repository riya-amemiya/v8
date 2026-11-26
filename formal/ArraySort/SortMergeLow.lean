import ArraySort.SortRun

namespace ArraySort

open Torque

def LO (le : Val → Val → Bool) (M0 : List (Option Val)) (k : MCtx) (w : List (Option Val)) (d ct b la : Nat) :
    Prop :=
  seg w k.baseA d ++ List.merge (seg k.T ct (ct + la)) (seg w b k.endPos) (oleq le) = M0 ∧
    Srt le (seg k.T ct (ct + la)) ∧ Srt le (seg w b k.endPos) ∧
    ∀ y ∈ seg w b k.endPos, oleq le (k.T.getD (k.la0 - 1) none) y = false

def LowOrd (le : Val → Val → Bool) (M0 : List (Option Val)) (k : MCtx) (c : Core) (s : MS) : Prop :=
  LO le M0 k c.work s.dest.toNat s.ct.toNat s.cur.toNat s.la.toNat

section

variable {le : Val → Val → Bool} {M0 : List (Option Val)} {k : MCtx}

theorem srt_tail {a : Option Val} {l : List (Option Val)} (h : Srt le (a :: l)) : Srt le l :=
  (List.pairwise_cons.1 h).2

theorem srt_split {l : List (Option Val)} {lo m hi : Nat} (h1 : lo ≤ m) (h2 : m ≤ hi) (h : Srt le (seg l lo hi)) :
    Srt le (seg l lo m) ∧ Srt le (seg l m hi) := by
  unfold Srt at *
  rw [seg_split l h1 h2, List.pairwise_append] at h
  exact ⟨h.1, h.2.1⟩

theorem LO.moveB (hle : TotalPreorder le) {w : List (Option Val)} {d ct b la : Nat} (h : LO le M0 k w d ct b la)
    (hdb : d + la = b) (hbe : b < k.endPos) (hbd : k.baseA ≤ d) (hw : k.endPos ≤ w.length)
    (hT : ct + la ≤ k.T.length) (hord : 1 ≤ la → oleq le (k.T.getD ct none) (w.getD b none) = false) :
    LO le M0 k (w.set d (w.getD b none)) (d + 1) ct (b + 1) la := by
  obtain ⟨o1, o2, o3, o4⟩ := h
  have hRB : seg w b k.endPos = w.getD b none :: seg w (b + 1) k.endPos := seg_cons_getD hbe (by omega)
  have hout : seg (w.set d (w.getD b none)) k.baseA (d + 1) = seg w k.baseA d ++ [w.getD b none] :=
    seg_set_snoc hbd (by omega)
  have hRB' : seg (w.set d (w.getD b none)) (b + 1) k.endPos = seg w (b + 1) k.endPos :=
    seg_set_out (Or.inl (by omega))
  rw [hRB] at o1 o3 o4
  refine ⟨?_, o2, ?_, ?_⟩
  · rw [hout, hRB', List.append_assoc, ← o1]
    congr 1
    have := merge_take_right (oleq le) (A := seg k.T ct (ct + la)) (B1 := [w.getD b none])
      (B2 := seg w (b + 1) k.endPos) (fun y hy x hx => by
        simp only [List.mem_singleton] at hy
        subst hy
        rcases Nat.eq_zero_or_pos la with hl0 | hl0
        · subst hl0
          rw [Nat.add_zero, seg_self] at hx
          cases hx
        · rw [seg_cons_getD (by omega) (by omega)] at hx o2
          exact srt_cons_lt hle o2 (hord hl0) x hx)
    exact this.symm
  · rw [hRB']
    exact srt_tail o3
  · rw [hRB']
    intro y hy
    exact o4 y (List.mem_cons_of_mem _ hy)

theorem LO.moveA (hle : TotalPreorder le) {w : List (Option Val)} {d ct b la : Nat} (h : LO le M0 k w d ct b la)
    (hdb : d + la = b) (hla : 1 ≤ la) (hbe : b ≤ k.endPos) (hbd : k.baseA ≤ d) (hw : k.endPos ≤ w.length)
    (hT : ct + la ≤ k.T.length) (hord : b < k.endPos → oleq le (k.T.getD ct none) (w.getD b none) = true) :
    LO le M0 k (w.set d (k.T.getD ct none)) (d + 1) (ct + 1) b (la - 1) := by
  obtain ⟨o1, o2, o3, o4⟩ := h
  have hRA : seg k.T ct (ct + la) = k.T.getD ct none :: seg k.T (ct + 1) (ct + 1 + (la - 1)) := by
    rw [show ct + 1 + (la - 1) = ct + la by omega]
    exact seg_cons_getD (by omega) (by omega)
  have hout : seg (w.set d (k.T.getD ct none)) k.baseA (d + 1) = seg w k.baseA d ++ [k.T.getD ct none] :=
    seg_set_snoc hbd (by omega)
  have hRB' : seg (w.set d (k.T.getD ct none)) b k.endPos = seg w b k.endPos := seg_set_out (Or.inl (by omega))
  rw [hRA] at o1 o2
  refine ⟨?_, srt_tail o2, ?_, ?_⟩
  · rw [hout, hRB', List.append_assoc, ← o1]
    congr 1
    have := merge_take_left (oleq le) (A1 := [k.T.getD ct none]) (A2 := seg k.T (ct + 1) (ct + 1 + (la - 1)))
      (B := seg w b k.endPos) (fun x hx y hy => by
        simp only [List.mem_singleton] at hx
        subst hx
        rcases Nat.lt_or_ge b k.endPos with hbe' | hbe'
        · rw [seg_cons_getD hbe' (by omega)] at hy o3
          exact srt_cons_ge hle o3 (hord hbe') y hy
        · rw [show k.endPos = b by omega, seg_self] at hy
          cases hy)
    exact this.symm
  · rw [hRB']
    exact o3
  · rw [hRB']
    exact o4

theorem LO.copyA (hle : TotalPreorder le) {w : List (Option Val)} {d ct b la n : Nat} (h : LO le M0 k w d ct b la)
    (hdb : d + la = b) (hn : n ≤ la) (hbe : b ≤ k.endPos) (hbd : k.baseA ≤ d) (hw : k.endPos ≤ w.length)
    (hT : ct + la ≤ k.T.length)
    (hord : b < k.endPos → ∀ i, i < n → oleq le (k.T.getD (ct + i) none) (w.getD b none) = true) :
    LO le M0 k (over w d (seg k.T ct (ct + n))) (d + n) (ct + n) b (la - n) := by
  obtain ⟨o1, o2, o3, o4⟩ := h
  have hlen : (seg k.T ct (ct + n)).length = n := by rw [length_seg (by omega)]; omega
  have hl : d + (seg k.T ct (ct + n)).length ≤ w.length := by rw [hlen]; omega
  have hsplit : seg k.T ct (ct + la) = seg k.T ct (ct + n) ++ seg k.T (ct + n) (ct + n + (la - n)) := by
    rw [show ct + n + (la - n) = ct + la by omega]
    exact seg_split _ (by omega) (by omega)
  have hout : seg (over w d (seg k.T ct (ct + n))) k.baseA (d + n) = seg w k.baseA d ++ seg k.T ct (ct + n) := by
    rw [show d + n = d + (seg k.T ct (ct + n)).length by rw [hlen]]
    exact seg_over_left hl hbd
  have hRB' : seg (over w d (seg k.T ct (ct + n))) b k.endPos = seg w b k.endPos :=
    seg_over_out hl (Or.inr (by rw [hlen]; omega))
  rw [hsplit] at o1 o2
  refine ⟨?_, (List.pairwise_append.1 o2).2.1, by rw [hRB']; exact o3, by rw [hRB']; exact o4⟩
  rw [hout, hRB', List.append_assoc, ← o1]
  congr 1
  symm
  apply merge_take_left
  intro x hx y hy
  obtain ⟨i, hi1, hi2, hi⟩ := mem_seg.1 hx
  rcases Nat.lt_or_ge b k.endPos with hbe' | hbe'
  · have hx' := hord hbe' (i - ct) (by omega)
    rw [show ct + (i - ct) = i by omega, getD_of_getElem? hi] at hx'
    rw [seg_cons_getD hbe' (by omega)] at hy o3
    exact oleq_trans hle _ _ _ hx' (srt_cons_ge hle o3 (oleq_refl hle _) y hy)
  · rw [show k.endPos = b by omega, seg_self] at hy
    cases hy

theorem LO.copyB (hle : TotalPreorder le) {w : List (Option Val)} {d ct b la n : Nat} (h : LO le M0 k w d ct b la)
    (hdb : d + la = b) (hn : b + n ≤ k.endPos) (hbd : k.baseA ≤ d) (hw : k.endPos ≤ w.length)
    (hT : ct + la ≤ k.T.length)
    (hord : 1 ≤ la → ∀ i, i < n → oleq le (k.T.getD ct none) (w.getD (b + i) none) = false) :
    LO le M0 k (over w d (seg w b (b + n))) (d + n) ct (b + n) la := by
  obtain ⟨o1, o2, o3, o4⟩ := h
  have hlen : (seg w b (b + n)).length = n := by rw [length_seg (by omega)]; omega
  have hl : d + (seg w b (b + n)).length ≤ w.length := by rw [hlen]; omega
  have hsplit : seg w b k.endPos = seg w b (b + n) ++ seg w (b + n) k.endPos := seg_split _ (by omega) hn
  have hout : seg (over w d (seg w b (b + n))) k.baseA (d + n) = seg w k.baseA d ++ seg w b (b + n) := by
    rw [show d + n = d + (seg w b (b + n)).length by rw [hlen]]
    exact seg_over_left hl hbd
  have hRB' : seg (over w d (seg w b (b + n))) (b + n) k.endPos = seg w (b + n) k.endPos :=
    seg_over_out hl (Or.inr (by rw [hlen]; omega))
  rw [hsplit] at o1 o3 o4
  refine ⟨?_, o2, by rw [hRB']; exact (List.pairwise_append.1 o3).2.1,
    by rw [hRB']; exact fun y hy => o4 y (List.mem_append_right _ hy)⟩
  rw [hout, hRB', List.append_assoc, ← o1]
  congr 1
  symm
  apply merge_take_right
  intro y hy x hx
  obtain ⟨i, hi1, hi2, hi⟩ := mem_seg.1 hy
  rcases Nat.eq_zero_or_pos la with hl0 | hl0
  · subst hl0
    rw [Nat.add_zero, seg_self] at hx
    cases hx
  · have hy' := hord hl0 (i - b) (by omega)
    rw [show b + (i - b) = i by omega, getD_of_getElem? hi] at hy'
    rw [seg_cons_getD (by omega) (by omega)] at hx o2
    exact oleq_false_of_le hle hy' (srt_cons_ge hle o2 (oleq_refl hle _) x hx)

theorem LO.final {w : List (Option Val)} {d ct b : Nat} (h : LO le M0 k w d ct b 0) (hdb : d = b)
    (hbd : k.baseA ≤ d) (hbe : b ≤ k.endPos) : seg w k.baseA k.endPos = M0 := by
  obtain ⟨o1, -, -, -⟩ := h
  rw [Nat.add_zero, seg_self, List.nil_merge, hdb] at o1
  rw [seg_split w (show k.baseA ≤ b by omega) hbe]
  exact o1

theorem lowOrd_of {c : Core} {s : MS} {d ct b la : Nat} (h1 : s.dest = d) (h2 : s.ct = ct) (h3 : s.cur = b)
    (h4 : s.la = la) (h : LO le M0 k c.work d ct b la) : LowOrd le M0 k c s := by
  unfold LowOrd
  rw [h1, h2, h3, h4]
  simpa using h

theorem lo_of {c : Core} {s : MS} {d ct b la : Nat} (h1 : s.dest = d) (h2 : s.ct = ct) (h3 : s.cur = b)
    (h4 : s.la = la) (h : LowOrd le M0 k c s) : LO le M0 k c.work d ct b la := by
  unfold LowOrd at h
  rw [h1, h2, h3, h4] at h
  simpa using h

end

def Exit.st : Exit → MS
  | .succeed s => s
  | .copy s => s

def GOrd (le : Val → Val → Bool) (M0 : List (Option Val)) (k : MCtx) : GStep → Core → Prop
  | .exit x, c => LowOrd le M0 k c x.st
  | .cont s _ _, c => LowOrd le M0 k c s

macro "osos" : tactic => `(tactic| first | omega | (simp only [Exit.st]; omega) | sos)

section

variable {ε : Type} (cmp : Cmp ε) (smiMax : Nat) {le : Val → Val → Bool} {M0 : List (Option Val)}

theorem lowGallopC_post (hle : TotalPreorder le) {k : MCtx} (s : MS) (na nb : Int) (e : ε) (c : Core)
    (h : LowInv k c ⟨s.dest + na + 1 + nb, s.ct + na, s.cur + 1 + nb, s.la - na, s.lb - 1 - nb⟩)
    (ho : LowOrd le M0 k c ⟨s.dest + na + 1 + nb, s.ct + na, s.cur + 1 + nb, s.la - na, s.lb - 1 - nb⟩)
    (hla : 2 ≤ s.la - na) (hlb : 1 ≤ s.lb - 1 - nb)
    (hord : oleq le (k.T.getD (s.ct + na).toNat none) (c.work.getD (s.cur + 1 + nb).toNat none) = true) :
    ((lowGallopC s na nb) e c).Post (fun r _ c' => GOrd le M0 k r c') := by
  obtain ⟨d, ct, b, la, lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h.ghosts
  try simp only at e1 e2 e3 e4 e5
  have ho' := lo_of e1 e2 e3 e4 ho
  rw [show (s.ct + na).toNat = ct by omega, show (s.cur + 1 + nb).toNat = b by omega] at hord
  have hn := LO.moveA hle ho' h1 (by omega) (by omega) h4 (by omega) (by omega) fun _ => hord
  unfold lowGallopC
  rw [post_bind, post_mv]
  intro _ _
  simp only [Core.get_work, Core.get_temp, Core.put_work]
  rw [show (s.ct + na).toNat = ct by omega, show (s.dest + na + 1 + nb).toNat = d by omega, h5]
  rw [post_ite]
  split
  · rw [post_pure]
    exact lowOrd_of (c := { c with work := c.work.set d (k.T.getD ct none) }) (by osos)
      (by osos) (by osos) (by osos) hn
  · rw [post_pure]
    exact lowOrd_of (c := { c with work := c.work.set d (k.T.getD ct none) }) (by osos)
      (by osos) (by osos) (by osos) hn

theorem lowGallopB_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {k : MCtx} (s : MS) (na : Int) (e : ε)
    (c : Core) (h : LowInv k c ⟨s.dest + na, s.ct + na, s.cur, s.la - na, s.lb⟩)
    (ho : LowOrd le M0 k c ⟨s.dest + na, s.ct + na, s.cur, s.la - na, s.lb⟩)
    (hla : 2 ≤ s.la - na) (hlb : 1 ≤ s.lb)
    (hord : oleq le (k.T.getD (s.ct + na).toNat none) (c.work.getD s.cur.toNat none) = false) :
    ((lowGallopB cmp smiMax s na) e c).Post (fun r _ c' => GOrd le M0 k r c') := by
  obtain ⟨d, ct, b, la, lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h.ghosts
  try simp only at e1 e2 e3 e4 e5
  have ho' := lo_of (s := ⟨s.dest + na, s.ct + na, s.cur, s.la - na, s.lb⟩) e1 e2 e3 e4 ho
  rw [show (s.ct + na).toNat = ct by omega, show s.cur.toNat = b by omega] at hord
  have hn := LO.moveB hle ho' h1 (by omega) h4 (by omega) (by omega) fun _ => hord
  unfold lowGallopB
  rw [post_bind, post_mv]
  intro _ _
  simp only [Core.get_work, Core.put_work]
  rw [show s.cur.toNat = b by omega, show (s.dest + na).toNat = d by omega]
  have hi := h.moveB (d := d) (b := b) (lb := lb) (by osos) (by osos) (by osos) (by omega)
  rw [post_ite]
  split
  · rw [post_pure]
    exact lowOrd_of (c := { c with work := c.work.set d (c.work.getD b none) }) (by osos)
      (by osos) (by osos) (by osos) hn
  · simp only [post_bind, post_ld, post_jsAny, post_dcheck, Core.get_temp]
    intro _ v2 hv2
    rw [show (s.ct + na).toNat = ct by omega, h5] at hv2
    have hsrt : SrtAt le ({ c with work := c.work.set d (c.work.getD b none) }.get .work) (b + 1)
        (b + 1 + (lb - 1)) := by
      simp only [Core.get_work]
      rw [show b + 1 + (lb - 1) = k.endPos by omega]
      exact srtAt_of_srt hle (by simp; omega) hn.2.2.1
    rw [show s.cur + 1 = ((b + 1 : Nat) : Int) by omega, show s.lb - 1 = ((lb - 1 : Nat) : Int) by omega]
    refine (gallop_post cmp smiMax hle hc (isRight := false) (key := v2) (hint := 0) hsrt).mono ?_
    rintro nb e2 c2 ⟨hc2, k2, hnb, hk2, hgl, hgr⟩
    subst c2
    subst hnb
    simp only [Core.get_work] at hgl hgr
    intro _
    have hcB : ∀ i, i < k2 → oleq le (k.T.getD ct none)
        ((c.work.set d (c.work.getD b none)).getD (b + 1 + i) none) = false := by
      intro i hi
      have := hgl i hi
      rw [hv2]
      simpa [gp] using this
    have hn2 := LO.copyB hle hn (n := k2) (by omega) (by omega) (by omega) (by simp; omega) (by omega)
      fun _ => hcB
    have hi2 := hi.copyB (d := d + 1) (b := b + 1) (lb := lb - 1) (n := k2) (by osos) (by osos) (by osos) (by omega)
    rw [post_doIf]
    split
    · refine post_of_good (copy_good_int (spN := b + 1) (dpN := d + 1) (nN := k2) (Q := fun _ _ c3 =>
        c3 = { c with work := over (c.work.set d (c.work.getD b none)) (d + 1) (seg (c.work.set d (c.work.getD b none)) (b + 1) (b + 1 + k2)) })
          (by omega) (by omega) rfl (by simp; omega) (by simp; omega) rfl) |>.mono ?_
      rintro _ e3 c3 rfl
      rw [post_ite]
      split
      · rw [post_pure]
        exact lowOrd_of (by osos) (by osos) (by osos) (by osos) hn2
      · refine lowGallopC_post hle s na k2 e3 _ (hi2.congr (by osos) rfl (by osos) rfl (by osos))
          (lowOrd_of (by osos) (by osos) (by osos) (by osos) hn2)
          hla (by omega) ?_
        simp only
        have hsl : (seg (c.work.set d (c.work.getD b none)) (b + 1) (b + 1 + k2)).length = k2 := by
          rw [length_seg (by simp; omega)]
          omega
        rw [show (s.ct + na).toNat = ct by omega, show (s.cur + 1 + (k2 : Int)).toNat = b + 1 + k2 by omega,
          getD_over_out (by rw [hsl]; simp; omega) (Or.inr (by rw [hsl]; omega))]
        have := hgr k2 (Nat.le_refl _) (by omega)
        rw [hv2]
        simpa [gp] using this
    · have : k2 = 0 := by omega
      subst this
      rw [post_ite, ite_eq_right (by omega)]
      refine lowGallopC_post hle s na 0 e2 _ (hi.congr (by osos) rfl (by osos) rfl (by osos))
        (lowOrd_of (by osos) (by osos) (by osos) (by osos) hn)
        hla (by omega) ?_
      simp only
      rw [show (s.ct + na).toNat = ct by omega, show (s.cur + 1 + 0).toNat = b + 1 + 0 by omega]
      have := hgr 0 (Nat.le_refl _) (by omega)
      rw [hv2]
      simpa [gp] using this

theorem lowGallopStep_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {k : MCtx} (s : MS) (e : ε) (c : Core)
    (h : LowInv k c s) (ho : LowOrd le M0 k c s) (hla : 1 < s.la) (hlb : 0 < s.lb) :
    ((lowGallopStep cmp smiMax s) e c).Post (fun r _ c' => GOrd le M0 k r c') := by
  obtain ⟨d, ct, b, la, lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h.ghosts
  have ho' := lo_of e1 e2 e3 e4 ho
  unfold lowGallopStep
  simp only [post_bind, post_ld, post_jsAny, Core.get_work]
  intro _ v1 hv1
  rw [show s.cur.toNat = b by omega] at hv1
  have hsrt : SrtAt le (c.get .temp) ct (ct + la) := by
    simp only [Core.get_temp]
    rw [h5]
    exact srtAt_of_srt hle (by omega) ho'.2.1
  rw [e2, e4]
  refine (gallop_post cmp smiMax hle hc (isRight := true) (key := v1) (hint := 0) hsrt).mono ?_
  rintro na e2' c2 ⟨hc2, k1, hna, hk1, hgl, hgr⟩
  subst c2
  subst hna
  simp only [Core.get_temp] at hgl hgr
  rw [h5] at hgl hgr
  rw [post_dcheck]
  intro _
  have hcA : b < k.endPos → ∀ i, i < k1 → oleq le (k.T.getD (ct + i) none) (c.work.getD b none) = true := by
    intro _ i hi
    have := hgl i hi
    rw [hv1]
    simpa [gp] using this
  have hn := LO.copyA hle ho' (n := k1) h1 hk1 (by omega) h4 (by omega) (by omega) hcA
  have hi := h.copyA (d := d) (ct := ct) (la := la) (n := k1) e1 e2 e4 hk1
  have hcont : ∀ e3 c3, c3 = { c with work := over c.work d (seg k.T ct (ct + k1)) } →
      ((if 0 < (k1 : Int) ∧ (la : Int) - (k1 : Int) = 1 then
          pure (GStep.exit (Exit.copy ⟨s.dest + k1, (ct : Int) + k1, s.cur, (la : Int) - k1, s.lb⟩))
        else if 0 < (k1 : Int) ∧ (la : Int) - (k1 : Int) = 0 then
          pure (GStep.exit (Exit.succeed ⟨s.dest + k1, (ct : Int) + k1, s.cur, (la : Int) - k1, s.lb⟩))
        else lowGallopB cmp smiMax s k1) e3 c3).Post (fun r _ c' => GOrd le M0 k r c') := by
    rintro e3 c3 rfl
    rw [post_ite]
    split
    · rw [post_pure]
      exact lowOrd_of (by osos) (by osos) (by osos) (by osos) hn
    · rw [post_ite]
      split
      · rw [post_pure]
        exact lowOrd_of (by osos) (by osos) (by osos) (by osos) hn
      · refine lowGallopB_post cmp smiMax hle hc s k1 e3 _ hi
          (lowOrd_of (by osos) (by osos) (by osos) (by osos) hn)
          (by omega) hlb ?_
        simp only
        rw [show (s.ct + (k1 : Int)).toNat = ct + k1 by omega, show s.cur.toNat = b by omega,
          List.getD_eq_getElem?_getD (l := over c.work d (seg k.T ct (ct + k1))),
          getElem?_over_out (by rw [length_seg (by omega)]; omega) (Or.inr (by rw [length_seg (by omega)]; omega)),
          ← List.getD_eq_getElem?_getD, hv1]
        have := hgr k1 (Nat.le_refl _) (by omega)
        simpa [gp] using this
  rw [post_doIf]
  split
  · refine (post_of_good (copy_good_int (src := .temp) (dst := .work) (c := c) (e := e2') (spN := ct) (dpN := d)
      (nN := k1) (Q := fun _ _ c3 => c3 = { c with work := over c.work d (seg k.T ct (ct + k1)) }) rfl e1 rfl
      (by simp only [Core.get_temp]; rw [h5]; omega) (by simp only [Core.get_work]; omega)
      (by simp [h5]))).mono ?_
    rintro _ e3 c3 h3
    exact hcont e3 c3 h3
  · have : k1 = 0 := by omega
    subst this
    exact hcont e2' c (by rw [Nat.add_zero, seg_self, over_nil])

theorem lowLoop_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {k : MCtx} (hv : Vals k.w0 k.baseA k.endPos) :
    ∀ (mg : Int) (ph : Ph) (s : MS) (e : ε) (c : Core), LowInv k c s → LowOrd le M0 k c s → 1 < s.la →
      0 < s.lb → ((lowLoop cmp smiMax mg ph s) e c).Post (fun x _ c' => LowOrd le M0 k c' x.st)
  | mg, .simple wa wb, s, e, c, hinv, ho, hla, hlb => by
    obtain ⟨d, ct, b, la, lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hinv.ghosts
    have ho' := lo_of e1 e2 e3 e4 ho
    rw [lowLoop, dite_eq_left ⟨hla, hlb⟩]
    simp only [post_bind, post_ld, post_jsAny, post_compare, Core.get_work, Core.get_temp]
    intro _ v1 hv1 _ v2 hv2 o e' ho2
    rw [show s.cur.toNat = b by omega] at hv1
    rw [show s.ct.toNat = ct by omega, h5] at hv2
    have hg := hc _ _ _ _ _ ho2
    rw [post_ite]
    split
    · next hlt =>
      rw [post_bind, post_mv]
      intro _ _
      simp only [Core.get_work, Core.put_work]
      rw [show s.cur.toNat = b by omega, show s.dest.toNat = d by omega]
      have hi := hinv.moveB e1 e3 e5 (by omega)
      have hn := LO.moveB hle ho' h1 (by omega) h4 (by omega) (by omega) fun _ => by
        rw [hv1, hv2]
        exact hg.1 hlt
      have hon : LowOrd le M0 k { c with work := c.work.set d (c.work.getD b none) }
          ⟨s.dest + 1, s.ct, s.cur + 1, s.la, s.lb - 1⟩ :=
        lowOrd_of (by osos) (by osos) (by osos) (by osos) hn
      rw [post_ite]
      split
      · rw [post_pure]
        exact hon
      · rw [post_ite]
        split
        · exact lowLoop_post hle hc hv _ _ _ e' _ hi hon (by osos) (by osos)
        · exact lowLoop_post hle hc hv _ _ _ e' _ hi hon (by osos) (by osos)
    · next hlt =>
      rw [post_bind, post_mv]
      intro _ _
      simp only [Core.get_work, Core.get_temp, Core.put_work]
      rw [show s.ct.toNat = ct by omega, show s.dest.toNat = d by omega,
        show c.temp.getD ct none = k.T.getD ct none by rw [h5]]
      have hi := hinv.moveA e1 e2 e4 (by omega)
      have hn := LO.moveA hle ho' h1 (by omega) (by omega) h4 (by omega) (by omega) fun _ => by
        rw [hv1, hv2]
        cases h : le v2 v1
        · exact absurd (hg.2 h) hlt
        · exact h
      have hon : LowOrd le M0 k { c with work := c.work.set d (k.T.getD ct none) }
          ⟨s.dest + 1, s.ct + 1, s.cur, s.la - 1, s.lb⟩ :=
        lowOrd_of (by osos) (by osos) (by osos) (by osos) hn
      rw [post_ite]
      split
      · rw [post_pure]
        exact hon
      · rw [post_ite]
        split
        · exact lowLoop_post hle hc hv _ _ _ e' _ hi hon (by osos) (by osos)
        · exact lowLoop_post hle hc hv _ _ _ e' _ hi hon (by osos) (by osos)
  | mg, .gallop first wa wb, s, e, c, hinv, ho, hla, hlb => by
    rw [lowLoop, post_ite]
    split
    · simp only [post_bind, post_dcheck, post_setMinGallop]
      intro _
      refine (post_and (post_of_good (lowGallopStep_good cmp smiMax hv s e { c with minGallop := max 1 (mg - 1) }
        (hinv.minGallop (g := max 1 (mg - 1))) hla hlb))
        (lowGallopStep_post cmp smiMax hle hc s e { c with minGallop := max 1 (mg - 1) }
          (hinv.minGallop (g := max 1 (mg - 1))) ho hla hlb)).mono ?_
      rintro r e' c' ⟨hr, hro⟩
      cases r with
      | exit x => exact hro
      | cont s' na nb =>
        obtain ⟨hinv', hla', hlb', hlt⟩ := hr
        dsimp only
        rw [dite_eq_left hlt]
        exact lowLoop_post hle hc hv _ _ _ e' _ hinv' hro hla' hlb'
    · simp only [post_bind, post_setMinGallop]
      exact lowLoop_post hle hc hv _ _ _ e _ hinv.minGallop ho hla hlb
termination_by _ ph s => 2 * (s.la.toNat + s.lb.toNat) + ph.rank
decreasing_by all_goals simp only [Ph.rank]; omega

end

theorem getD_seg' {l : List (Option Val)} {lo hi i : Nat} (h : i < hi - lo) :
    (seg l lo hi).getD i none = l.getD (lo + i) none := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, getElem?_seg, ite_eq_left h]

theorem getD_over_in {l s : List (Option Val)} {pos i : Nat} (h : pos + s.length ≤ l.length) (h1 : pos ≤ i)
    (h2 : i < pos + s.length) : (over l pos s).getD i none = s.getD (i - pos) none := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, getElem?_over h, ite_eq_right (by omega),
    ite_eq_left h2]

section

variable {ε : Type} (cmp : Cmp ε) (smiMax : Nat) {le : Val → Val → Bool}

theorem mergeLow_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {baseA la0 lb0 : Nat} {c : Core} {e : ε}
    (hla : 0 < la0) (hlb : 0 < lb0) (hv : Vals c.work baseA (baseA + la0 + lb0))
    (hA : Srt le (seg c.work baseA (baseA + la0))) (hB : Srt le (seg c.work (baseA + la0) (baseA + la0 + lb0)))
    (h0 : oleq le (c.work.getD baseA none) (c.work.getD (baseA + la0) none) = false)
    (hlast : ∀ y ∈ seg c.work (baseA + la0) (baseA + la0 + lb0),
      oleq le (c.work.getD (baseA + la0 - 1) none) y = false) :
    ((mergeLow cmp smiMax (baseA : Int) (la0 : Int) ((baseA + la0 : Nat) : Int) (lb0 : Int)) e c).Post
      (fun _ _ c' => seg c'.work baseA (baseA + la0 + lb0) =
        List.merge (seg c.work baseA (baseA + la0)) (seg c.work (baseA + la0) (baseA + la0 + lb0)) (oleq le)) := by
  have hl := hv.1
  unfold mergeLow
  simp only [post_bind, post_dcheck]
  intro _ _ _
  refine post_of_good (getTempArray_spec fun t ht => ?_)
  have hlenS : (seg c.work baseA (baseA + la0)).length = la0 := by rw [length_seg (by omega)]; omega
  have hTl : (over t 0 (seg c.work baseA (baseA + la0))).length = t.length :=
    length_over (by rw [hlenS]; omega)
  refine (post_of_good (copy_good (sp := baseA) (dp := 0) (n := la0)
    (Q := fun _ e' c' => e' = e ∧ c' = { c with temp := over t 0 (seg c.work baseA (baseA + la0)) })
    (by simp only [Core.get_work]; omega) (by simp only [Core.get_temp]; omega) ⟨rfl, rfl⟩)).mono ?_
  rintro _ e1 c1 ⟨rfl, rfl⟩
  let k : MCtx := ⟨c.work, over t 0 (seg c.work baseA (baseA + la0)), baseA, la0, baseA + la0 + lb0, c.runs,
    c.powers, c.size⟩
  have hRA : seg (over t 0 (seg c.work baseA (baseA + la0))) 0 la0 = seg c.work baseA (baseA + la0) := by
    have := seg_over_in (l := t) (s := seg c.work baseA (baseA + la0)) (pos := 0) (by rw [hlenS]; omega)
    rwa [hlenS, Nat.zero_add] at this
  have hinv0 : LowInv k { c with temp := over t 0 (seg c.work baseA (baseA + la0)) }
      ⟨baseA, 0, ((baseA + la0 : Nat) : Int), la0, lb0⟩ := by
    refine ⟨baseA, 0, baseA + la0, la0, lb0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [k], Nat.le_refl _,
      rfl, by simp only [k]; omega, rfl, by simp only [k]; omega, fun _ _ => rfl, ?_, rfl, rfl, rfl⟩
    simp only [k, seg_self, List.nil_append, Nat.zero_add]
    rw [hRA, ← seg_split c.work (Nat.le_add_right baseA la0) (by omega)]
  have hT0 : ∀ i, i < la0 → k.T.getD i none = c.work.getD (baseA + i) none := by
    intro i hi
    simp only [k]
    rw [getD_over_in (by rw [hlenS]; omega) (Nat.zero_le _) (by rw [hlenS]; omega), Nat.sub_zero,
      getD_seg' (by omega)]
  have lo0 : LO le (List.merge (seg c.work baseA (baseA + la0)) (seg c.work (baseA + la0) (baseA + la0 + lb0))
      (oleq le)) k c.work baseA 0 (baseA + la0) la0 := by
    refine ⟨?_, ?_, hB, ?_⟩
    · simp only [k, seg_self, List.nil_append, Nat.zero_add]
      rw [hRA]
    · simp only [k, Nat.zero_add]
      rw [hRA]
      exact hA
    · intro y hy
      simp only [k] at hy ⊢
      rw [show (over t 0 (seg c.work baseA (baseA + la0))).getD (la0 - 1) none =
        c.work.getD (baseA + la0 - 1) none by
          have := hT0 (la0 - 1) (by omega)
          simp only [k] at this
          rw [this, show baseA + (la0 - 1) = baseA + la0 - 1 by omega]]
      exact hlast y hy
  have hv' : Vals k.w0 k.baseA k.endPos := hv
  rw [post_mv]
  intro _ _
  simp only [Core.get_work, Core.put_work, Int.toNat_natCast]
  have hinv1 := (hinv0.moveB (d := baseA) (b := baseA + la0) (lb := lb0) rfl rfl rfl hlb).congr
    (s' := ⟨(baseA : Int) + 1, 0, ((baseA + la0 : Nat) : Int) + 1, la0, (lb0 : Int) - 1⟩) rfl rfl rfl rfl rfl
  have lo1 := LO.moveB hle lo0 rfl (by simp only [k]; omega) (Nat.le_refl _) (by simp only [k]; omega)
    (by simp only [k]; omega) fun _ => by
      rw [hT0 0 hla, Nat.add_zero]
      exact h0
  let c1 : Core := { c with temp := over t 0 (seg c.work baseA (baseA + la0)), work := c.work.set baseA (c.work.getD (baseA + la0) none) }
  let M0 := List.merge (seg c.work baseA (baseA + la0)) (seg c.work (baseA + la0) (baseA + la0 + lb0)) (oleq le)
  have ho1 : LowOrd le M0 k c1 ⟨(baseA : Int) + 1, 0, ((baseA + la0 : Nat) : Int) + 1, la0, (lb0 : Int) - 1⟩ :=
    lowOrd_of (by osos) (by osos) (by osos) (by osos) lo1
  have hrun : (lowRun cmp smiMax ⟨(baseA : Int) + 1, 0, ((baseA + la0 : Nat) : Int) + 1, la0, (lb0 : Int) - 1⟩ e1
      c1).Post (fun x _ c' => LowPost k x c' ∧ LowOrd le M0 k c' x.st) := by
    rw [lowRun, post_ite]
    split
    · exact ⟨⟨hinv1, Or.inl (by osos)⟩, ho1⟩
    · rw [post_ite]
      split
      · exact ⟨⟨hinv1, by osos, by osos⟩, ho1⟩
      · rw [post_bind, post_getMinGallop]
        exact post_and (post_of_good (lowLoop_good cmp smiMax hv' _ _ _ e1 _ hinv1 (by osos) (by osos)))
          (lowLoop_post cmp smiMax hle hc hv' _ _ _ e1 _ hinv1 ho1 (by osos) (by osos))
  refine hrun.mono ?_
  rintro x e2 c2 ⟨hx, hxo⟩
  cases x with
  | succeed s =>
    obtain ⟨hinv, hor⟩ := hx
    obtain ⟨d, ct, b, la, lb, e1', e2', e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hinv.ghosts
    have lo := lo_of e1' e2' e3 e4 hxo
    rw [lowFinish, post_ite]
    split
    · refine post_of_good (copy_good_int (spN := ct) (dpN := d) (nN := la)
        (Q := fun _ _ c3 => c3 = { c2 with work := over c2.work d (seg k.T ct (ct + la)) }) e2' e1' e4
        (by simp only [Core.get_temp]; rw [h5]; omega) (by simp only [Core.get_work]; omega) (by simp [h5]))
        |>.mono ?_
      rintro _ _ c3 rfl
      have lo2 := LO.copyA hle lo (n := la) h1 (Nat.le_refl _) (by omega) h4 (by omega) (by omega)
        fun hb => absurd hb (by omega)
      rw [Nat.sub_self] at lo2
      exact lo2.final (by omega) (by omega) (by omega)
    · rw [post_pure]
      have : la = 0 := by omega
      subst this
      exact lo.final (by omega) h4 (by omega)
  | copy s =>
    obtain ⟨hinv, hla1, hlb1⟩ := hx
    obtain ⟨d, ct, b, la, lb, e1', e2', e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hinv.ghosts
    have lo := lo_of e1' e2' e3 e4 hxo
    rw [lowFinish]
    simp only [post_bind, post_dcheck]
    intro _
    refine post_of_good (copy_good_int (spN := b) (dpN := d) (nN := lb)
      (Q := fun _ _ c3 => c3 = { c2 with work := over c2.work d (seg c2.work b (b + lb)) }) e3 e1' e5
      (by simp only [Core.get_work]; omega) (by simp only [Core.get_work]; omega) (by simp)) |>.mono ?_
    rintro _ e3' c3 rfl
    have lo2 := LO.copyB hle lo (n := lb) h1 (by omega) h4 (by omega) (by omega) fun _ i hi => by
      have hm : c2.work.getD (b + i) none ∈ seg c2.work b k.endPos := by
        rw [mem_seg]
        refine ⟨b + i, by omega, by omega, ?_⟩
        rw [getElem?_eq_some_getD (by omega)]
      have := lo.2.2.2 _ hm
      rwa [show k.la0 - 1 = ct by omega] at this
    rw [post_mv]
    intro _ _
    simp only [Core.get_work, Core.get_temp, Core.put_work]
    rw [show s.ct.toNat = ct by omega, show (s.dest + s.lb).toNat = d + lb by omega, h5]
    have hlo : (over c2.work d (seg c2.work b (b + lb))).length = c2.work.length :=
      length_over (by rw [length_seg (by omega)]; omega)
    have hla1' : la = 1 := by omega
    subst hla1'
    have lo3 := LO.moveA hle lo2 (by omega) (by omega) (by omega) (by omega) (by rw [hlo]; omega) (by omega)
      fun hb => absurd hb (by omega)
    exact lo3.final (by omega) (by omega) (by omega)

end

end ArraySort
