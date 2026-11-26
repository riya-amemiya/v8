import ArraySort.MergeLow

namespace ArraySort

open Torque

def HighInv (k : MCtx) (c : Core) (s : MS) : Prop :=
  ∃ la lb : Nat, s.la = la ∧ s.lb = lb ∧ s.cur = (k.baseA : Int) + la - 1 ∧ s.ct = (lb : Int) - 1 ∧
    s.dest = (k.baseA : Int) + la + lb - 1 ∧ k.baseA + la + lb ≤ k.endPos ∧ lb ≤ k.la0 ∧
    c.temp = k.T ∧ k.la0 ≤ k.T.length ∧ c.work.length = k.w0.length ∧ k.endPos ≤ k.w0.length ∧
    (∀ i, (i < k.baseA ∨ k.endPos ≤ i) → c.work[i]? = k.w0[i]?) ∧
    (seg c.work k.baseA (k.baseA + la) ++ seg k.T 0 lb ++ seg c.work (k.baseA + la + lb) k.endPos).Perm
      (seg k.w0 k.baseA k.endPos) ∧
    c.runs = k.runs ∧ c.powers = k.powers ∧ c.size = k.size

theorem HighInv.ghosts {k : MCtx} {c : Core} {s : MS} (h : HighInv k c s) :
    ∃ la lb : Nat, s.la = la ∧ s.lb = lb ∧ s.cur = (k.baseA : Int) + la - 1 ∧ s.ct = (lb : Int) - 1 ∧
      s.dest = (k.baseA : Int) + la + lb - 1 ∧ k.baseA + la + lb ≤ k.endPos ∧ lb ≤ k.la0 ∧
      c.temp = k.T ∧ k.la0 ≤ k.T.length ∧ c.work.length = k.w0.length ∧ k.endPos ≤ k.w0.length := by
  obtain ⟨la, lb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _⟩ := h
  exact ⟨la, lb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem HighInv.minGallop {k : MCtx} {c : Core} {s : MS} {g : Int} (h : HighInv k c s) :
    HighInv k { c with minGallop := g } s := h

theorem HighInv.congr {k : MCtx} {c : Core} {s s' : MS} (h : HighInv k c s) (h1 : s'.dest = s.dest)
    (h2 : s'.ct = s.ct) (h3 : s'.cur = s.cur) (h4 : s'.la = s.la) (h5 : s'.lb = s.lb) : HighInv k c s' := by
  obtain ⟨la, lb, e1, e2, e3, e4, e5, rest⟩ := h
  exact ⟨la, lb, h4.trans e1, h5.trans e2, h3.trans e3, h2.trans e4, h1.trans e5, rest⟩

theorem HighInv.copyA {k : MCtx} {c : Core} {s : MS} {la lb n : Nat} (h : HighInv k c s)
    (hla : s.la = la) (hlb : s.lb = lb) (hn : n ≤ la) :
    HighInv k { c with work := over c.work (k.baseA + la + lb - n) (seg c.work (k.baseA + la - n) (k.baseA + la - n + n)) }
      ⟨s.dest - n, s.ct, s.cur - n, s.la - n, s.lb⟩ := by
  obtain ⟨la', lb', e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, hp, h8, h9, h10⟩ := h
  have : la = la' := by omega
  subst this
  have : lb = lb' := by omega
  subst this
  have hlen : (seg c.work (k.baseA + la - n) (k.baseA + la - n + n)).length = n := by
    rw [length_seg (by omega)]; omega
  refine ⟨la - n, lb, by sos, e2, by sos, e4, by sos, by omega, h2, h3, h4, ?_, h6, ?_, ?_, h8, h9, h10⟩
  · simp only
    rw [length_over (by rw [hlen]; omega), h5]
  · intro i hi
    simp only
    rw [getElem?_over_out (by rw [hlen]; omega) (by rw [hlen]; omega), h7 i hi]
  · simp only
    rw [seg_over_out (by rw [hlen]; omega) (by rw [hlen]; omega),
      show k.baseA + (la - n) + lb = k.baseA + la + lb - n by omega,
      seg_over_right (by rw [hlen]; omega) (by rw [hlen]; omega), hlen,
      show k.baseA + la + lb - n + n = k.baseA + la + lb by omega]
    rw [seg_split c.work (show k.baseA ≤ k.baseA + la - n by omega)
      (show k.baseA + la - n ≤ k.baseA + la by omega)] at hp
    have e : seg c.work (k.baseA + la - n) (k.baseA + la) =
        seg c.work (k.baseA + la - n) (k.baseA + la - n + n) := by
      rw [show k.baseA + la - n + n = k.baseA + la by omega]
    rw [e] at hp
    rw [show k.baseA + (la - n) = k.baseA + la - n by omega]
    have : (seg c.work k.baseA (k.baseA + la - n) ++ seg k.T 0 lb ++
        (seg c.work (k.baseA + la - n) (k.baseA + la - n + n) ++
          seg c.work (k.baseA + la + lb) k.endPos)).Perm
        (seg c.work k.baseA (k.baseA + la - n) ++ seg c.work (k.baseA + la - n) (k.baseA + la - n + n) ++
          seg k.T 0 lb ++ seg c.work (k.baseA + la + lb) k.endPos) := by
      simp only [List.append_assoc]
      exact List.Perm.append_left _ (by
        rw [← List.append_assoc, ← List.append_assoc]
        exact List.Perm.append_right _ List.perm_append_comm)
    exact this.trans hp

theorem HighInv.copyB {k : MCtx} {c : Core} {s : MS} {la lb n : Nat} (h : HighInv k c s)
    (hla : s.la = la) (hlb : s.lb = lb) (hn : n ≤ lb) :
    HighInv k { c with work := over c.work (k.baseA + la + lb - n) (seg k.T (lb - n) (lb - n + n)) }
      ⟨s.dest - n, s.ct - n, s.cur, s.la, s.lb - n⟩ := by
  obtain ⟨la', lb', e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, hp, h8, h9, h10⟩ := h
  have : la = la' := by omega
  subst this
  have : lb = lb' := by omega
  subst this
  have hlen : (seg k.T (lb - n) (lb - n + n)).length = n := by rw [length_seg (by omega)]; omega
  refine ⟨la, lb - n, e1, by sos, e3, by sos, by sos, by omega, by omega, h3, h4, ?_, h6, ?_, ?_, h8, h9,
    h10⟩
  · simp only
    rw [length_over (by rw [hlen]; omega), h5]
  · intro i hi
    simp only
    rw [getElem?_over_out (by rw [hlen]; omega) (by rw [hlen]; omega), h7 i hi]
  · simp only
    rw [seg_over_out (by rw [hlen]; omega) (by rw [hlen]; omega),
      show k.baseA + la + (lb - n) = k.baseA + la + lb - n by omega,
      seg_over_right (by rw [hlen]; omega) (by rw [hlen]; omega), hlen,
      show k.baseA + la + lb - n + n = k.baseA + la + lb by omega]
    rw [seg_split k.T (show 0 ≤ lb - n by omega) (show lb - n ≤ lb by omega)] at hp
    have e : seg k.T (lb - n) lb = seg k.T (lb - n) (lb - n + n) := by
      rw [show lb - n + n = lb by omega]
    rw [e] at hp
    simpa only [List.append_assoc] using hp

theorem HighInv.moveA {k : MCtx} {c : Core} {s : MS} {la lb : Nat} (h : HighInv k c s)
    (hla : s.la = la) (hlb : s.lb = lb) (h1 : 1 ≤ la) (h2 : 1 ≤ lb) :
    HighInv k { c with work := c.work.set (k.baseA + la + lb - 1) (c.work.getD (k.baseA + la - 1) none) }
      ⟨s.dest - 1, s.ct, s.cur - 1, s.la - 1, s.lb⟩ := by
  obtain ⟨la', lb', e1, e2, e3, e4, e5, g1, g2, g3, g4, g5, g6⟩ := h.ghosts
  have hd : k.baseA + la + lb - 1 < c.work.length := by omega
  have hs : k.baseA + la - 1 < c.work.length := by omega
  have := h.copyA hla hlb h1
  rw [show k.baseA + la - 1 + 1 = k.baseA + la - 1 + 1 by rfl, seg_single hs, ← getD_eq_getElem hs,
    ← set_eq_over hd] at this
  exact this

theorem HighInv.moveB {k : MCtx} {c : Core} {s : MS} {la lb : Nat} (h : HighInv k c s)
    (hla : s.la = la) (hlb : s.lb = lb) (h2 : 1 ≤ lb) :
    HighInv k { c with work := c.work.set (k.baseA + la + lb - 1) (k.T.getD (lb - 1) none) }
      ⟨s.dest - 1, s.ct - 1, s.cur, s.la, s.lb - 1⟩ := by
  obtain ⟨la', lb', e1, e2, e3, e4, e5, g1, g2, g3, g4, g5, g6⟩ := h.ghosts
  have hd : k.baseA + la + lb - 1 < c.work.length := by omega
  have hs : lb - 1 < k.T.length := by omega
  have := h.copyB hla hlb h2
  rw [seg_single hs, ← getD_eq_getElem hs, ← set_eq_over hd] at this
  exact this

theorem HighInv.final {k : MCtx} {c : Core} {s : MS} (h : HighInv k c s) (hlb : s.lb = 0) :
    PermOn k.w0 c.work k.baseA k.endPos ∧ c.temp = k.T ∧ c.runs = k.runs ∧ c.powers = k.powers ∧
      c.size = k.size := by
  obtain ⟨la, lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, hp, h8, h9, h10⟩ := h
  have : lb = 0 := by omega
  subst this
  refine ⟨⟨h5, h7, ?_⟩, h3, h8, h9, h10⟩
  rw [seg_self, List.append_nil, Nat.add_zero,
    ← seg_split c.work (Nat.le_add_right k.baseA la) (by omega)] at hp
  exact hp

theorem HighInv.vals_work {k : MCtx} {c : Core} {s : MS} {la : Nat} (h : HighInv k c s) (hla : s.la = la)
    (hv : Vals k.w0 k.baseA k.endPos) : Vals c.work k.baseA (k.baseA + la) := by
  obtain ⟨la', lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, hp, _⟩ := h
  have : la = la' := by omega
  subst this
  exact vals_of_allSome (by omega) ((allSome_of_vals hv).perm hp).append_left.append_left

theorem HighInv.vals_temp {k : MCtx} {c : Core} {s : MS} {lb : Nat} (h : HighInv k c s) (hlb : s.lb = lb)
    (hv : Vals k.w0 k.baseA k.endPos) : Vals c.temp 0 lb := by
  obtain ⟨la, lb', e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, hp, _⟩ := h
  have : lb = lb' := by omega
  subst this
  rw [h3]
  exact vals_of_allSome (by omega) ((allSome_of_vals hv).perm hp).append_left.append_right

def HighPost (k : MCtx) : Exit → Core → Prop
  | .succeed s, c => HighInv k c s ∧ (s.la = 0 ∨ s.lb = 0)
  | .copy s, c => HighInv k c s ∧ s.lb = 1 ∧ 0 < s.la

def HGPost (k : MCtx) (s0 : MS) : GStep → Core → Prop
  | .exit x, c => HighPost k x c
  | .cont s _ _, c => HighInv k c s ∧ 0 < s.la ∧ 1 < s.lb ∧
      s.la.toNat + s.lb.toNat < s0.la.toNat + s0.lb.toNat

section

variable {ε : Type} (cmp : Cmp ε) (smiMax : Nat)

theorem highGallopC_good {k : MCtx} (s : MS) (na pa nb pb : Int) (e : ε) (c : Core)
    (h : HighInv k c ⟨s.dest - pa - 1 - pb, s.ct - 1 - pb, s.cur - pa, s.la - pa, s.lb - 1 - pb⟩)
    (hla : 1 ≤ s.la - pa) (hlb : 2 ≤ s.lb - 1 - pb) (hpa : 0 ≤ pa) (hpb : 0 ≤ pb) :
    ((highGallopC s na pa nb pb : M ε GStep) e c).Good (fun r _ c' => HGPost k s r c') := by
  obtain ⟨la, lb, e1, e2, e3, e4, e5, g1, g2, g3, g4, g5, g6⟩ := h.ghosts
  try simp only at e1 e2 e3 e4 e5
  unfold highGallopC
  rw [good_bind, good_mv]
  refine ⟨⟨by omega, by bnd⟩, ⟨by omega, by bnd⟩, ?_⟩
  simp only [Core.get_work, Core.put_work]
  rw [show (s.cur - pa).toNat = k.baseA + la - 1 by omega,
    show (s.dest - pa - 1 - pb).toNat = k.baseA + la + lb - 1 by omega]
  have hi := (h.moveA (la := la) (lb := lb) (by sos) (by sos) (by omega) (by omega)).congr
    (s' := ⟨s.dest - pa - 2 - pb, s.ct - 1 - pb, s.cur - pa - 1, s.la - pa - 1, s.lb - 1 - pb⟩)
    (by sos) rfl rfl rfl rfl
  rw [good_ite]
  split
  · exact ⟨hi, Or.inl (by sos)⟩
  · exact ⟨hi, by sos, by sos, by sos⟩

theorem highGallopB_good {k : MCtx} (hv : Vals k.w0 k.baseA k.endPos) (s : MS) (na pa : Int) (e : ε)
    (c : Core) (h : HighInv k c ⟨s.dest - pa, s.ct, s.cur - pa, s.la - pa, s.lb⟩)
    (hla : 1 ≤ s.la - pa) (hlb : 2 ≤ s.lb) (hpa : 0 ≤ pa) :
    ((highGallopB cmp smiMax s na pa) e c).Good (fun r _ c' => HGPost k s r c') := by
  obtain ⟨la, lb, e1, e2, e3, e4, e5, g1, g2, g3, g4, g5, g6⟩ := h.ghosts
  try simp only at e1 e2 e3 e4 e5
  have hT : c.temp.length = k.T.length := by rw [g3]
  unfold highGallopB
  rw [good_bind, good_mv]
  refine ⟨⟨by omega, by bnd⟩, ⟨by omega, by bnd⟩, ?_⟩
  simp only [Core.get_work, Core.get_temp, Core.put_work]
  rw [show s.ct.toNat = lb - 1 by omega, show (s.dest - pa).toNat = k.baseA + la + lb - 1 by omega,
    show c.temp.getD (lb - 1) none = k.T.getD (lb - 1) none by rw [g3]]
  have hi := h.moveB (la := la) (lb := lb) (by sos) (by sos) (by omega)
  rw [good_ite]
  split
  · exact ⟨hi, by sos, by sos⟩
  · simp only [good_bind, good_ld, good_jsAny, good_dcheck, Core.get_work]
    obtain ⟨v, hv'⟩ := (hi.vals_work (la := la) (by sos) hv).2 (k.baseA + la - 1) (by omega) (by omega)
    refine ⟨⟨by omega, by bnd⟩, v, by
      rw [show (s.cur - pa).toNat = k.baseA + la - 1 by omega]; exact hv', ?_⟩
    refine (gallop_good_int cmp smiMax (a := .temp) (key := v) (isRight := false)
      (baseN := 0) (lengthN := lb - 1) (hintN := lb - 2) rfl (by omega) (by omega)
      (by rw [Nat.zero_add]; exact hi.vals_temp (lb := lb - 1) (by sos) hv) (by omega)).mono ?_
    rintro k2 e2 c2 ⟨hc2, k2N, hk2, hk2N⟩
    subst c2
    subst hk2
    refine ⟨by omega, ?_⟩
    refine Res.Good.mono (Q := fun _ _ c3 =>
      HighInv k c3 ⟨s.dest - pa - 1 - max (s.lb - 1 - (k2N : Int)) 0, s.ct - 1 - max (s.lb - 1 - (k2N : Int)) 0,
        s.cur - pa, s.la - pa, s.lb - 1 - max (s.lb - 1 - (k2N : Int)) 0⟩) ?_ ?_
    · rintro _ e3 c3 hinv3
      rw [good_ite]
      split
      · exact ⟨hinv3, by sos, by sos⟩
      · rw [good_ite]
        split
        · exact ⟨hinv3, Or.inr (by sos)⟩
        · exact highGallopC_good s _ pa _ _ e3 c3 hinv3 hla (by omega) hpa (by omega)
    · rw [good_doIf]
      split
      · refine copy_good_int (spN := lb - 1 - (lb - 1 - k2N)) (dpN := k.baseA + la + (lb - 1) - (lb - 1 - k2N))
          (nN := lb - 1 - k2N) (by omega) (by omega) (by omega) (by bnd) (by bnd) ?_
        have := hi.copyB (la := la) (lb := lb - 1) (n := lb - 1 - k2N) (by sos) (by sos) (by omega)
        simp only [Core.get_work, Core.get_temp, Core.put_work]
        rw [show seg c.temp (lb - 1 - (lb - 1 - k2N)) (lb - 1 - (lb - 1 - k2N) + (lb - 1 - k2N)) =
          seg k.T (lb - 1 - (lb - 1 - k2N)) (lb - 1 - (lb - 1 - k2N) + (lb - 1 - k2N)) by rw [g3]]
        exact this.congr (by sos) (by sos) rfl rfl (by sos)
      · exact hi.congr (by sos) (by sos) rfl rfl (by sos)

theorem highGallopStep_good {k : MCtx} (hv : Vals k.w0 k.baseA k.endPos) (s : MS) (e : ε) (c : Core)
    (h : HighInv k c s) (hla : 0 < s.la) (hlb : 1 < s.lb) :
    ((highGallopStep cmp smiMax (k.baseA : Int) s) e c).Good (fun r _ c' => HGPost k s r c') := by
  obtain ⟨la, lb, e1, e2, e3, e4, e5, g1, g2, g3, g4, g5, g6⟩ := h.ghosts
  have hT : c.temp.length = k.T.length := by rw [g3]
  unfold highGallopStep
  simp only [good_bind, good_ld, good_jsAny, Core.get_temp]
  obtain ⟨v, hv'⟩ := (h.vals_temp e2 hv).2 (lb - 1) (by omega) (by omega)
  refine ⟨⟨by omega, by omega⟩, v, by rw [show s.ct.toNat = lb - 1 by omega]; exact hv', ?_⟩
  refine (gallop_good_int cmp smiMax (a := .work) (key := v) (c := c) (e := e) (isRight := true)
    (baseN := k.baseA) (lengthN := la) (hintN := la - 1) rfl e1 (by omega) (h.vals_work e1 hv)
    (by omega)).mono ?_
  rintro kk e2' c2 ⟨hc2, kN, hkk, hkN⟩
  subst c2
  subst hkk
  simp only [good_dcheck]
  refine ⟨by omega, ?_⟩
  refine Res.Good.mono (Q := fun _ _ c3 =>
    HighInv k c3 ⟨s.dest - max (s.la - (kN : Int)) 0, s.ct, s.cur - max (s.la - (kN : Int)) 0,
      s.la - max (s.la - (kN : Int)) 0, s.lb⟩) ?_ ?_
  · rintro _ e3 c3 hinv3
    rw [good_ite]
    split
    · exact ⟨hinv3, Or.inl (by sos)⟩
    · exact highGallopB_good cmp smiMax hv s _ _ e3 c3 hinv3 (by omega) hlb (by omega)
  · rw [good_doIf]
    split
    · refine copy_good_int (spN := k.baseA + la - (la - kN)) (dpN := k.baseA + la + lb - (la - kN))
        (nN := la - kN) (by omega) (by omega) (by omega) (by bnd) (by bnd) ?_
      have := h.copyA (la := la) (lb := lb) (n := la - kN) e1 e2 (by omega)
      simp only [Core.get_work, Core.put_work]
      exact this.congr (by sos) rfl (by sos) (by sos) rfl
    · exact h.congr (by sos) rfl (by sos) (by sos) rfl

theorem highLoop_good {k : MCtx} (hv : Vals k.w0 k.baseA k.endPos) :
    ∀ (mg : Int) (ph : Ph) (s : MS) (e : ε) (c : Core), HighInv k c s → 0 < s.la → 1 < s.lb →
      ((highLoop cmp smiMax (k.baseA : Int) mg ph s) e c).Good (fun x _ c' => HighPost k x c')
  | mg, .simple wa wb, s, e, c, hinv, hla, hlb => by
    obtain ⟨la, lb, e1, e2, e3, e4, e5, g1, g2, g3, g4, g5, g6⟩ := hinv.ghosts
    have hT : c.temp.length = k.T.length := by rw [g3]
    rw [highLoop, dite_eq_left ⟨hla, hlb⟩]
    simp only [good_bind, good_ld, good_jsAny, good_compare, Core.get_work, Core.get_temp]
    obtain ⟨v1, hv1⟩ := (hinv.vals_temp e2 hv).2 (lb - 1) (by omega) (by omega)
    obtain ⟨v2, hv2⟩ := (hinv.vals_work e1 hv).2 (k.baseA + la - 1) (by omega) (by omega)
    refine ⟨⟨by omega, by omega⟩, v1, by rw [show s.ct.toNat = lb - 1 by omega]; exact hv1,
      ⟨by omega, by omega⟩, v2, by rw [show s.cur.toNat = k.baseA + la - 1 by omega]; exact hv2,
      fun o e' _ => ?_⟩
    rw [good_ite]
    split
    · rw [good_bind, good_mv]
      refine ⟨⟨by bnd, by bnd⟩, ⟨by omega, by bnd⟩, ?_⟩
      simp only [Core.get_work, Core.put_work]
      rw [show s.cur.toNat = k.baseA + la - 1 by omega, show s.dest.toNat = k.baseA + la + lb - 1 by omega]
      have hi := hinv.moveA e1 e2 (by omega) (by omega)
      rw [good_ite]
      split
      · exact ⟨hi, Or.inl (by sos)⟩
      · rw [good_ite]
        split
        · exact highLoop_good hv _ _ _ e' _ hi (by sos) (by sos)
        · exact highLoop_good hv _ _ _ e' _ hi (by sos) (by sos)
    · rw [good_bind, good_mv]
      refine ⟨⟨by bnd, by bnd⟩, ⟨by omega, by bnd⟩, ?_⟩
      simp only [Core.get_work, Core.get_temp, Core.put_work]
      rw [show s.ct.toNat = lb - 1 by omega, show s.dest.toNat = k.baseA + la + lb - 1 by omega,
        show c.temp.getD (lb - 1) none = k.T.getD (lb - 1) none by rw [g3]]
      have hi := hinv.moveB e1 e2 (by omega)
      rw [good_ite]
      split
      · exact ⟨hi, by sos, by sos⟩
      · rw [good_ite]
        split
        · exact highLoop_good hv _ _ _ e' _ hi (by sos) (by sos)
        · exact highLoop_good hv _ _ _ e' _ hi (by sos) (by sos)
  | mg, .gallop first wa wb, s, e, c, hinv, hla, hlb => by
    rw [highLoop, good_ite]
    split
    · simp only [good_bind, good_dcheck, good_setMinGallop]
      refine ⟨⟨hla, hlb⟩, (highGallopStep_good cmp smiMax hv s e _ hinv.minGallop hla hlb).mono ?_⟩
      rintro r e' c' hr
      cases r with
      | exit x => exact hr
      | cont s' na nb =>
        obtain ⟨hinv', hla', hlb', hlt⟩ := hr
        dsimp only
        rw [dite_eq_left hlt]
        exact highLoop_good hv _ _ _ e' _ hinv' hla' hlb'
    · simp only [good_bind, good_setMinGallop]
      exact highLoop_good hv _ _ _ e _ hinv.minGallop hla hlb
termination_by _ ph s => 2 * (s.la.toNat + s.lb.toNat) + ph.rank
decreasing_by all_goals simp only [Ph.rank]; omega

theorem mergeHigh_good {baseA la0 lb0 : Nat} {c : Core} {e : ε} (hla : 0 < la0) (hlb : 0 < lb0)
    (hv : Vals c.work baseA (baseA + la0 + lb0)) :
    ((mergeHigh cmp smiMax (baseA : Int) (la0 : Int) ((baseA + la0 : Nat) : Int) (lb0 : Int)) e c).Good
      (fun _ _ c' => PermOn c.work c'.work baseA (baseA + la0 + lb0) ∧ c'.runs = c.runs ∧
        c'.powers = c.powers ∧ c'.size = c.size) := by
  have hl := hv.1
  unfold mergeHigh
  simp only [good_bind, good_dcheck]
  refine ⟨by omega, by omega, by omega, getTempArray_spec fun t ht => ?_⟩
  refine copy_good (sp := baseA + la0) (dp := 0) (n := lb0) (by simp only [Core.get_work]; omega)
    (by simp only [Core.get_temp]; omega) ?_
  simp only [Core.get_work, Core.get_temp, Core.put_temp]
  let k : MCtx := ⟨c.work, over t 0 (seg c.work (baseA + la0) (baseA + la0 + lb0)), baseA, lb0,
    baseA + la0 + lb0, c.runs, c.powers, c.size⟩
  have hlenS : (seg c.work (baseA + la0) (baseA + la0 + lb0)).length = lb0 := by
    rw [length_seg (by omega)]; omega
  have hTl : (over t 0 (seg c.work (baseA + la0) (baseA + la0 + lb0))).length = t.length :=
    length_over (by rw [hlenS]; omega)
  have hinv0 : HighInv k { c with temp := over t 0 (seg c.work (baseA + la0) (baseA + la0 + lb0)) }
      ⟨(baseA : Int) + la0 + lb0 - 1, (lb0 : Int) - 1, (baseA : Int) + la0 - 1, la0, lb0⟩ := by
    refine ⟨la0, lb0, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, rfl, by simp only [k]; omega,
      rfl, by simp only [k]; omega, fun _ _ => rfl, ?_, rfl, rfl, rfl⟩
    simp only [k, seg_self, List.append_nil]
    have : seg (over t 0 (seg c.work (baseA + la0) (baseA + la0 + lb0))) 0 lb0 =
        seg c.work (baseA + la0) (baseA + la0 + lb0) := by
      have := seg_over_in (l := t) (s := seg c.work (baseA + la0) (baseA + la0 + lb0)) (pos := 0)
        (by rw [hlenS]; omega)
      rwa [hlenS, Nat.zero_add] at this
    rw [this, ← seg_split c.work (Nat.le_add_right baseA la0) (by omega)]
  have hv' : Vals k.w0 k.baseA k.endPos := hv
  rw [good_mv]
  refine ⟨⟨by omega, by simp only [Core.get_work]; omega⟩, ⟨by omega, by simp only [Core.get_work]; omega⟩, ?_⟩
  simp only [Core.get_work, Core.put_work]
  rw [show ((baseA : Int) + (la0 : Int) - 1).toNat = k.baseA + la0 - 1 by simp only [k]; omega,
    show (((baseA + la0 : Nat) : Int) + (lb0 : Int) - 1).toNat = k.baseA + la0 + lb0 - 1 by simp only [k]; omega]
  have hinv1 := (hinv0.moveA (la := la0) (lb := lb0) rfl rfl hla hlb).congr
    (s' := ⟨((baseA + la0 : Nat) : Int) + lb0 - 2, (lb0 : Int) - 1, (baseA : Int) + la0 - 2, (la0 : Int) - 1,
      lb0⟩) (by sos) rfl (by sos) rfl rfl
  refine Res.Good.mono (Q := fun x _ c' => HighPost k x c') ?_ ?_
  · rintro x e2 c2 hx
    cases x with
    | succeed s =>
      obtain ⟨hinv, hor⟩ := hx
      obtain ⟨la, lb, e1, e2', e3, e4, e5, g1, g2, g3, g4, g5, g6⟩ := hinv.ghosts
      have hT : c2.temp.length = k.T.length := by rw [g3]
      rw [highFinish, good_ite]
      split
      · simp only [good_bind, good_dcheck]
        refine ⟨by omega, ?_⟩
        refine copy_good_int (spN := 0) (dpN := k.baseA) (nN := lb) rfl (by omega) e2' (by bnd) (by bnd) ?_
        have := (hinv.copyB (la := la) (lb := lb) (n := lb) e1 e2' (Nat.le_refl lb)).final (by sos)
        simp only [Core.get_work, Core.get_temp, Core.put_work]
        rw [show seg c2.temp 0 (0 + lb) = seg k.T (lb - lb) (lb - lb + lb) by rw [g3, Nat.sub_self],
          show k.baseA = k.baseA + la + lb - lb by omega]
        exact ⟨this.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩
      · have := hinv.final (by omega)
        exact ⟨this.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩
    | copy s =>
      obtain ⟨hinv, hlb1, hla1⟩ := hx
      obtain ⟨la, lb, e1, e2', e3, e4, e5, g1, g2, g3, g4, g5, g6⟩ := hinv.ghosts
      have hT : c2.temp.length = k.T.length := by rw [g3]
      rw [highFinish]
      simp only [good_bind, good_dcheck]
      refine ⟨⟨hlb1, hla1⟩, ?_⟩
      refine copy_good_int (spN := k.baseA) (dpN := k.baseA + 1) (nN := la) (by omega) (by omega) e1
        (by bnd) (by bnd) ?_
      have hi := hinv.copyA (la := la) (lb := lb) (n := la) e1 e2' (Nat.le_refl la)
      have hlo : (over c2.work (k.baseA + 1) (seg c2.work k.baseA (k.baseA + la))).length = c2.work.length :=
        length_over (by rw [length_seg (by omega)]; omega)
      simp only [Core.get_work, Core.put_work]
      rw [good_mv]
      refine ⟨⟨by omega, by bnd⟩, ⟨by omega, by bnd⟩, ?_⟩
      simp only [Core.get_work, Core.get_temp, Core.put_work]
      rw [show s.ct.toNat = lb - 1 by omega, show (s.dest - s.la).toNat = k.baseA + 0 + lb - 1 by omega,
        show c2.temp.getD (lb - 1) none = k.T.getD (lb - 1) none by rw [g3]]
      rw [show k.baseA + la + lb - la = k.baseA + 1 by omega, show k.baseA + la - la = k.baseA by omega] at hi
      have := (hi.moveB (la := 0) (lb := lb) (by sos) (by sos) (by omega)).final (by sos)
      exact ⟨this.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩
  · rw [highRun, good_ite]
    split
    · exact ⟨hinv1, Or.inl (by sos)⟩
    · rw [good_ite]
      split
      · exact ⟨hinv1, by sos, by sos⟩
      · rw [good_bind, good_getMinGallop]
        exact highLoop_good cmp smiMax hv' _ _ _ e _ hinv1 (by sos) (by sos)

end

end ArraySort
