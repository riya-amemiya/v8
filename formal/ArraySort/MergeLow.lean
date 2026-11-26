import ArraySort.Gallop

namespace ArraySort

open Torque

def AllSome (l : List (Option Val)) : Prop := ∀ x ∈ l, x ≠ none

theorem allSome_of_vals {l : List (Option Val)} {lo hi : Nat} (h : Vals l lo hi) : AllSome (seg l lo hi) := by
  intro x hx
  obtain ⟨i, h1, h2, hi⟩ := mem_seg.1 hx
  obtain ⟨v, hv⟩ := h.2 i h1 h2
  rw [getD_of_getElem? hi] at hv
  simp [hv]

theorem vals_of_allSome {l : List (Option Val)} {lo hi : Nat} (hl : hi ≤ l.length)
    (h : AllSome (seg l lo hi)) : Vals l lo hi := by
  refine ⟨hl, fun i h1 h2 => ?_⟩
  have hil : i < l.length := by omega
  have hm : l[i] ∈ seg l lo hi := mem_seg.2 ⟨i, h1, h2, List.getElem?_eq_getElem hil⟩
  have := h _ hm
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]
  cases hx : l[i] with
  | none => exact absurd hx this
  | some v => exact ⟨v, rfl⟩

theorem AllSome.perm {l l' : List (Option Val)} (h : AllSome l) (hp : l'.Perm l) : AllSome l' :=
  fun x hx => h x (hp.mem_iff.1 hx)

theorem AllSome.append_left {l l' : List (Option Val)} (h : AllSome (l ++ l')) : AllSome l :=
  fun x hx => h x (List.mem_append_left _ hx)

theorem AllSome.append_right {l l' : List (Option Val)} (h : AllSome (l ++ l')) : AllSome l' :=
  fun x hx => h x (List.mem_append_right _ hx)

structure MCtx where
  w0 : List (Option Val)
  T : List (Option Val)
  baseA : Nat
  la0 : Nat
  endPos : Nat
  runs : List Int
  powers : List Int
  size : Int

def LowInv (k : MCtx) (c : Core) (s : MS) : Prop :=
  ∃ d ct b la lb : Nat, s.dest = d ∧ s.ct = ct ∧ s.cur = b ∧ s.la = la ∧ s.lb = lb ∧
    d + la = b ∧ b + lb = k.endPos ∧ ct + la = k.la0 ∧
    k.baseA ≤ d ∧ c.temp = k.T ∧ k.la0 ≤ k.T.length ∧ c.work.length = k.w0.length ∧
    k.endPos ≤ k.w0.length ∧
    (∀ i, (i < k.baseA ∨ k.endPos ≤ i) → c.work[i]? = k.w0[i]?) ∧
    (seg c.work k.baseA d ++ seg k.T ct (ct + la) ++ seg c.work b k.endPos).Perm
      (seg k.w0 k.baseA k.endPos) ∧
    c.runs = k.runs ∧ c.powers = k.powers ∧ c.size = k.size

theorem LowInv.ghosts {k : MCtx} {c : Core} {s : MS} (h : LowInv k c s) :
    ∃ d ct b la lb : Nat, s.dest = d ∧ s.ct = ct ∧ s.cur = b ∧ s.la = la ∧ s.lb = lb ∧
      d + la = b ∧ b + lb = k.endPos ∧ ct + la = k.la0 ∧ k.baseA ≤ d ∧ c.temp = k.T ∧
      k.la0 ≤ k.T.length ∧ c.work.length = k.w0.length ∧ k.endPos ≤ k.w0.length := by
  obtain ⟨d, ct, b, la, lb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, _⟩ := h
  exact ⟨d, ct, b, la, lb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem LowInv.minGallop {k : MCtx} {c : Core} {s : MS} {g : Int} (h : LowInv k c s) :
    LowInv k { c with minGallop := g } s := h

theorem LowInv.copyA {k : MCtx} {c : Core} {s : MS} {d ct la n : Nat} (h : LowInv k c s)
    (hd : s.dest = d) (hct : s.ct = ct) (hla : s.la = la) (hn : n ≤ la) :
    LowInv k { c with work := over c.work d (seg k.T ct (ct + n)) }
      ⟨s.dest + n, s.ct + n, s.cur, s.la - n, s.lb⟩ := by
  obtain ⟨d', ct', b, la', lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8, h9, hp, h10, h11, h12⟩ := h
  have : d = d' := by omega
  subst this
  have : ct = ct' := by omega
  subst this
  have : la = la' := by omega
  subst this
  have hlen : (seg k.T ct (ct + n)).length = n := by rw [length_seg (by omega)]; omega
  refine ⟨d + n, ct + n, b, la - n, lb, by sos, by sos, e3, by sos,
    e5, by omega, h2, by omega, by omega, h5, h6, ?_, h8, ?_, ?_, h10, h11, h12⟩
  · simp only
    rw [length_over (by rw [hlen]; omega), h7]
  · intro i hi
    simp only
    rw [getElem?_over_out (by rw [hlen]; omega) (by rw [hlen]; omega), h9 i hi]
  · simp only
    rw [show d + n = d + (seg k.T ct (ct + n)).length by rw [hlen],
      seg_over_left (by rw [hlen]; omega) h4, seg_over_out (by rw [hlen]; omega) (by rw [hlen]; omega),
      show ct + n + (la - n) = ct + la by omega]
    rw [seg_split k.T (show ct ≤ ct + n by omega) (show ct + n ≤ ct + la by omega)] at hp
    simpa only [List.append_assoc] using hp

theorem LowInv.copyB {k : MCtx} {c : Core} {s : MS} {d b lb n : Nat} (h : LowInv k c s)
    (hd : s.dest = d) (hb : s.cur = b) (hlb : s.lb = lb) (hn : n ≤ lb) :
    LowInv k { c with work := over c.work d (seg c.work b (b + n)) }
      ⟨s.dest + n, s.ct, s.cur + n, s.la, s.lb - n⟩ := by
  obtain ⟨d', ct, b', la, lb', e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8, h9, hp, h10, h11, h12⟩ := h
  have : d = d' := by omega
  subst this
  have : b = b' := by omega
  subst this
  have : lb = lb' := by omega
  subst this
  have hlen : (seg c.work b (b + n)).length = n := by rw [length_seg (by omega)]; omega
  refine ⟨d + n, ct, b + n, la, lb - n, by sos, e2, by sos, e4,
    by sos, by omega, by omega, h3, by omega, h5, h6, ?_, h8, ?_, ?_, h10, h11, h12⟩
  · simp only
    rw [length_over (by rw [hlen]; omega), h7]
  · intro i hi
    simp only
    rw [getElem?_over_out (by rw [hlen]; omega) (by rw [hlen]; omega), h9 i hi]
  · simp only
    rw [show d + n = d + (seg c.work b (b + n)).length by rw [hlen],
      seg_over_left (by rw [hlen]; omega) h4, seg_over_out (by rw [hlen]; omega) (by rw [hlen]; omega)]
    rw [seg_split c.work (show b ≤ b + n by omega) (show b + n ≤ k.endPos by omega)] at hp
    have : (seg c.work k.baseA d ++ seg c.work b (b + n) ++ seg k.T ct (ct + la) ++
        seg c.work (b + n) k.endPos).Perm
        (seg c.work k.baseA d ++ seg k.T ct (ct + la) ++ (seg c.work b (b + n) ++
          seg c.work (b + n) k.endPos)) := by
      simp only [List.append_assoc]
      exact List.Perm.append_left _ (by
        rw [← List.append_assoc, ← List.append_assoc]
        exact List.Perm.append_right _ List.perm_append_comm)
    exact this.trans hp

theorem LowInv.moveA {k : MCtx} {c : Core} {s : MS} {d ct la : Nat} (h : LowInv k c s)
    (hd : s.dest = d) (hct : s.ct = ct) (hla : s.la = la) (hn : 1 ≤ la) :
    LowInv k { c with work := c.work.set d (k.T.getD ct none) }
      ⟨s.dest + 1, s.ct + 1, s.cur, s.la - 1, s.lb⟩ := by
  obtain ⟨d', ct', b, la', lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h.ghosts
  have hl : d < c.work.length := by omega
  have hc : ct < k.T.length := by omega
  have := h.copyA hd hct hla hn
  rw [seg_single hc, ← getD_eq_getElem hc, ← set_eq_over hl] at this
  exact this

theorem LowInv.moveB {k : MCtx} {c : Core} {s : MS} {d b lb : Nat} (h : LowInv k c s)
    (hd : s.dest = d) (hb : s.cur = b) (hlb : s.lb = lb) (hn : 1 ≤ lb) :
    LowInv k { c with work := c.work.set d (c.work.getD b none) }
      ⟨s.dest + 1, s.ct, s.cur + 1, s.la, s.lb - 1⟩ := by
  obtain ⟨d', ct', b', la', lb', e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h.ghosts
  have hl : d < c.work.length := by omega
  have hb' : b < c.work.length := by omega
  have := h.copyB hd hb hlb hn
  rw [seg_single hb', ← getD_eq_getElem hb', ← set_eq_over hl] at this
  exact this

theorem LowInv.final {k : MCtx} {c : Core} {s : MS} (h : LowInv k c s) (hla : s.la = 0) :
    PermOn k.w0 c.work k.baseA k.endPos ∧ c.temp = k.T ∧ c.runs = k.runs ∧ c.powers = k.powers ∧
      c.size = k.size := by
  obtain ⟨d, ct, b, la, lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8, h9, hp, h10, h11, h12⟩ := h
  have : la = 0 := by omega
  subst this
  refine ⟨⟨h7, h9, ?_⟩, h5, h10, h11, h12⟩
  rw [Nat.add_zero, seg_self, List.append_nil, show b = d by omega,
    ← seg_split c.work h4 (show d ≤ k.endPos by omega)] at hp
  exact hp

theorem LowInv.vals_work {k : MCtx} {c : Core} {s : MS} {b : Nat} (h : LowInv k c s) (hb : s.cur = b)
    (hv : Vals k.w0 k.baseA k.endPos) : Vals c.work b k.endPos := by
  obtain ⟨d, ct, b', la, lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8, h9, hp, _⟩ := h
  have : b = b' := by omega
  subst this
  exact vals_of_allSome (by omega) ((allSome_of_vals hv).perm hp).append_right

theorem LowInv.vals_temp {k : MCtx} {c : Core} {s : MS} {ct la : Nat} (h : LowInv k c s)
    (hct : s.ct = ct) (hla : s.la = la) (hv : Vals k.w0 k.baseA k.endPos) : Vals c.temp ct (ct + la) := by
  obtain ⟨d, ct', b, la', lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8, h9, hp, _⟩ := h
  have : ct = ct' := by omega
  subst this
  have : la = la' := by omega
  subst this
  rw [h5]
  exact vals_of_allSome (by omega) ((allSome_of_vals hv).perm hp).append_left.append_right

def LowPost (k : MCtx) : Exit → Core → Prop
  | .succeed s, c => LowInv k c s ∧ (s.lb = 0 ∨ s.la = 0)
  | .copy s, c => LowInv k c s ∧ s.la = 1 ∧ 0 < s.lb

theorem LowInv.congr {k : MCtx} {c : Core} {s s' : MS} (h : LowInv k c s) (h1 : s'.dest = s.dest)
    (h2 : s'.ct = s.ct) (h3 : s'.cur = s.cur) (h4 : s'.la = s.la) (h5 : s'.lb = s.lb) : LowInv k c s' := by
  obtain ⟨d, ct, b, la, lb, e1, e2, e3, e4, e5, rest⟩ := h
  exact ⟨d, ct, b, la, lb, h1.trans e1, h2.trans e2, h3.trans e3, h4.trans e4, h5.trans e5, rest⟩

section

variable {ε : Type}

theorem copy_good_int {src dst : Arr} {sp dp n : Int} {spN dpN nN : Nat} {e : ε} {c : Core}
    {Q : Unit → ε → Core → Prop} (hsp : sp = spN) (hdp : dp = dpN) (hn : n = nN)
    (hs : spN + nN ≤ (c.get src).length) (hd : dpN + nN ≤ (c.get dst).length)
    (hQ : Q () e (c.put dst (over (c.get dst) dpN (seg (c.get src) spN (spN + nN))))) :
    ((copy src sp dst dp n) e c).Good Q := by
  subst hsp
  subst hdp
  subst hn
  exact copy_good hs hd hQ

variable (cmp : Cmp ε) (smiMax : Nat)

theorem gallop_good_int {isRight : Bool} {a : Arr} {key : Val} {base length hint : Int}
    {baseN lengthN hintN : Nat} {c : Core} {e : ε} (hb : base = baseN) (hl : length = lengthN)
    (hh : hint = hintN) (hv : Vals (c.get a) baseN (baseN + lengthN)) (hlt : hintN < lengthN) :
    ((gallop cmp smiMax isRight a key base length hint) e c).Good
      (fun r _ c' => c' = c ∧ ∃ k : Nat, r = (k : Int) ∧ k ≤ lengthN) := by
  subst hb
  subst hl
  subst hh
  exact gallop_good cmp smiMax hv hlt

def GPost (k : MCtx) (s0 : MS) : GStep → Core → Prop
  | .exit x, c => LowPost k x c
  | .cont s _ _, c => LowInv k c s ∧ 1 < s.la ∧ 0 < s.lb ∧
      s.la.toNat + s.lb.toNat < s0.la.toNat + s0.lb.toNat

theorem lowGallopC_good {k : MCtx} (s : MS) (na nb : Int) (e : ε)
    (c : Core) (h : LowInv k c ⟨s.dest + na + 1 + nb, s.ct + na, s.cur + 1 + nb, s.la - na, s.lb - 1 - nb⟩)
    (hla : 2 ≤ s.la - na) (hlb : 1 ≤ s.lb - 1 - nb) (hna : 0 ≤ na) (hnb : 0 ≤ nb) :
    ((lowGallopC s na nb) e c).Good (fun r _ c' => GPost k s r c') := by
  obtain ⟨d, ct, b, la, lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h.ghosts
  try simp only at e1 e2 e3 e4 e5
  have hT : c.temp.length = k.T.length := by rw [h5]
  unfold lowGallopC
  rw [good_bind, good_mv]
  refine ⟨⟨by omega, by bnd⟩, ⟨by omega, by bnd⟩, ?_⟩
  simp only [Core.get_work, Core.get_temp, Core.put_work]
  rw [show (s.ct + na).toNat = ct by omega, show (s.dest + na + 1 + nb).toNat = d by omega,
    show c.temp.getD ct none = k.T.getD ct none by rw [h5]]
  have hi := (h.moveA (d := d) (ct := ct) (la := la) (by sos) (by sos)
    (by sos) (by omega)).congr (s' := ⟨s.dest + na + 2 + nb, s.ct + na + 1, s.cur + 1 + nb,
      s.la - na - 1, s.lb - 1 - nb⟩) (by sos) rfl rfl rfl rfl
  rw [good_ite]
  split
  · exact ⟨hi, by sos, by sos⟩
  · exact ⟨hi, by sos, by sos, by sos⟩

theorem lowGallopB_good {k : MCtx} (hv : Vals k.w0 k.baseA k.endPos) (s : MS) (na : Int) (e : ε)
    (c : Core) (h : LowInv k c ⟨s.dest + na, s.ct + na, s.cur, s.la - na, s.lb⟩)
    (hla : 2 ≤ s.la - na) (hlb : 1 ≤ s.lb) (hna : 0 ≤ na) :
    ((lowGallopB cmp smiMax s na) e c).Good (fun r _ c' => GPost k s r c') := by
  obtain ⟨d, ct, b, la, lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h.ghosts
  try simp only at e1 e2 e3 e4 e5
  have hT : c.temp.length = k.T.length := by rw [h5]
  unfold lowGallopB
  rw [good_bind, good_mv]
  refine ⟨⟨by omega, by bnd⟩, ⟨by omega, by bnd⟩, ?_⟩
  simp only [Core.get_work, Core.put_work]
  rw [show s.cur.toNat = b by omega, show (s.dest + na).toNat = d by omega]
  have hi := h.moveB (d := d) (b := b) (lb := lb) (by sos) (by sos)
    (by sos) (by omega)
  rw [good_ite]
  split
  · exact ⟨hi, Or.inl (by sos)⟩
  · obtain ⟨_, _, _, _, _, p1, p2, p3, p4, p5, q1, q2, q3, q4, q5, q6, q7, q8⟩ := hi.ghosts
    simp only [good_bind, good_ld, good_jsAny, good_dcheck, Core.get_temp]
    obtain ⟨v2, hv2⟩ := (hi.vals_temp (ct := ct) (la := la) (by sos) (by sos) hv).2
      ct (Nat.le_refl _) (by omega)
    refine ⟨⟨by omega, by sos⟩, v2, by rw [show (s.ct + na).toNat = ct by omega]; exact hv2, ?_⟩
    refine (gallop_good_int cmp smiMax (a := .work) (key := v2) (isRight := false)
      (baseN := b + 1) (lengthN := lb - 1) (hintN := 0) (by omega) (by omega) rfl
      (by
        have := hi.vals_work (b := b + 1) (by sos) hv
        rw [show b + 1 + (lb - 1) = k.endPos by omega]
        exact this) (by omega)).mono ?_
    rintro nb e2 c2 ⟨hc2, k2, hnb, hk2⟩
    subst c2
    subst hnb
    refine ⟨by omega, ?_⟩
    refine Res.Good.mono (Q := fun _ _ c3 =>
      LowInv k c3 ⟨s.dest + na + 1 + (k2 : Int), s.ct + na, s.cur + 1 + (k2 : Int), s.la - na,
        s.lb - 1 - (k2 : Int)⟩) ?_ ?_
    · rintro _ e3 c3 hinv3
      rw [good_ite]
      split
      · exact ⟨hinv3, Or.inl (by sos)⟩
      · exact lowGallopC_good s na k2 e3 c3 hinv3 hla (by omega) hna (by omega)
    · rw [good_doIf]
      split
      · refine copy_good_int (spN := b + 1) (dpN := d + 1) (nN := k2) (by omega) (by omega) rfl
          (by bnd) (by bnd) ?_
        have := hi.copyB (d := d + 1) (b := b + 1) (lb := lb - 1) (n := k2) (by sos)
          (by sos) (by sos) (by omega)
        simp only [Core.get_work, Core.put_work]
        exact this.congr (by sos) rfl (by sos) rfl (by sos)
      · have : k2 = 0 := by omega
        subst this
        exact hi.congr (by sos) rfl (by sos) rfl (by sos)

theorem lowGallopStep_good {k : MCtx} (hv : Vals k.w0 k.baseA k.endPos) (s : MS) (e : ε) (c : Core)
    (h : LowInv k c s) (hla : 1 < s.la) (hlb : 0 < s.lb) :
    ((lowGallopStep cmp smiMax s) e c).Good (fun r _ c' => GPost k s r c') := by
  obtain ⟨d, ct, b, la, lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h.ghosts
  have hT : c.temp.length = k.T.length := by rw [h5]
  unfold lowGallopStep
  simp only [good_bind, good_ld, good_jsAny, Core.get_work]
  obtain ⟨v1, hv1⟩ := (h.vals_work e3 hv).2 b (Nat.le_refl _) (by omega)
  refine ⟨⟨by omega, by omega⟩, v1, by rw [show s.cur.toNat = b by omega]; exact hv1, ?_⟩
  refine (gallop_good_int cmp smiMax (a := .temp) (key := v1) (c := c) (e := e) (isRight := true)
    (baseN := ct) (lengthN := la) (hintN := 0) e2 e4 rfl (h.vals_temp e2 e4 hv) (by omega)).mono ?_
  rintro na e2' c2 ⟨hc2, k1, hna, hk1⟩
  subst c2
  subst hna
  simp only [good_dcheck]
  refine ⟨by omega, ?_⟩
  refine Res.Good.mono (Q := fun _ _ c3 =>
    LowInv k c3 ⟨s.dest + (k1 : Int), s.ct + (k1 : Int), s.cur, s.la - (k1 : Int), s.lb⟩) ?_ ?_
  · rintro _ e3 c3 hinv3
    rw [good_ite]
    split
    · exact ⟨hinv3, by sos, by sos⟩
    · rw [good_ite]
      split
      · exact ⟨hinv3, Or.inr (by sos)⟩
      · exact lowGallopB_good cmp smiMax hv s k1 e3 c3 hinv3 (by omega) hlb (by omega)
  · rw [good_doIf]
    split
    · refine copy_good_int (spN := ct) (dpN := d) (nN := k1) e2 e1 rfl (by bnd) (by bnd) ?_
      have := h.copyA e1 e2 e4 hk1
      simp only [Core.get_work, Core.get_temp, Core.put_work]
      rw [show seg c.temp ct (ct + k1) = seg k.T ct (ct + k1) by rw [h5]]
      exact this
    · have : k1 = 0 := by omega
      subst this
      exact h.congr (by sos) (by sos) rfl (by sos) rfl

theorem lowLoop_good {k : MCtx} (hv : Vals k.w0 k.baseA k.endPos) :
    ∀ (mg : Int) (ph : Ph) (s : MS) (e : ε) (c : Core), LowInv k c s → 1 < s.la → 0 < s.lb →
      ((lowLoop cmp smiMax mg ph s) e c).Good (fun x _ c' => LowPost k x c')
  | mg, .simple wa wb, s, e, c, hinv, hla, hlb => by
    obtain ⟨d, ct, b, la, lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hinv.ghosts
    have hT : c.temp.length = k.T.length := by rw [h5]
    rw [lowLoop, dite_eq_left ⟨hla, hlb⟩]
    simp only [good_bind, good_ld, good_jsAny, good_compare, Core.get_work, Core.get_temp]
    obtain ⟨v1, hv1⟩ := (hinv.vals_work e3 hv).2 b (Nat.le_refl _) (by omega)
    obtain ⟨v2, hv2⟩ := (hinv.vals_temp e2 e4 hv).2 ct (Nat.le_refl _) (by omega)
    refine ⟨⟨by omega, by omega⟩, v1, by rw [show s.cur.toNat = b by omega]; exact hv1,
      ⟨by omega, by omega⟩, v2, by rw [show s.ct.toNat = ct by omega]; exact hv2, fun o e' _ => ?_⟩
    rw [good_ite]
    split
    · rw [good_bind, good_mv]
      refine ⟨⟨by bnd, by bnd⟩,
        ⟨by omega, by bnd⟩, ?_⟩
      simp only [Core.get_work, Core.put_work]
      rw [show s.cur.toNat = b by omega, show s.dest.toNat = d by omega]
      have hi := hinv.moveB e1 e3 e5 (by omega)
      rw [good_ite]
      split
      · exact ⟨hi, Or.inl (by sos)⟩
      · rw [good_ite]
        split
        · exact lowLoop_good hv _ _ _ e' _ hi (by sos) (by sos)
        · exact lowLoop_good hv _ _ _ e' _ hi (by sos) (by sos)
    · rw [good_bind, good_mv]
      refine ⟨⟨by bnd, by bnd⟩,
        ⟨by omega, by bnd⟩, ?_⟩
      simp only [Core.get_work, Core.get_temp, Core.put_work]
      rw [show s.ct.toNat = ct by omega, show s.dest.toNat = d by omega,
        show c.temp.getD ct none = k.T.getD ct none by rw [h5]]
      have hi := hinv.moveA e1 e2 e4 (by omega)
      rw [good_ite]
      split
      · exact ⟨hi, by sos, by sos⟩
      · rw [good_ite]
        split
        · exact lowLoop_good hv _ _ _ e' _ hi (by sos) (by sos)
        · exact lowLoop_good hv _ _ _ e' _ hi (by sos) (by sos)
  | mg, .gallop first wa wb, s, e, c, hinv, hla, hlb => by
    obtain ⟨d, ct, b, la, lb, e1, e2, e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hinv.ghosts
    have hT : c.temp.length = k.T.length := by rw [h5]
    rw [lowLoop, good_ite]
    split
    · simp only [good_bind, good_dcheck, good_setMinGallop]
      refine ⟨⟨hla, hlb⟩, (lowGallopStep_good cmp smiMax hv s e _ hinv.minGallop hla hlb).mono ?_⟩
      rintro r e' c' hr
      cases r with
      | exit x => exact hr
      | cont s' na nb =>
        obtain ⟨hinv', hla', hlb', hlt⟩ := hr
        dsimp only
        rw [dite_eq_left hlt]
        exact lowLoop_good hv _ _ _ e' _ hinv' hla' hlb'
    · simp only [good_bind, good_setMinGallop]
      exact lowLoop_good hv _ _ _ e _ hinv.minGallop hla hlb
termination_by _ ph s => 2 * (s.la.toNat + s.lb.toNat) + ph.rank
decreasing_by all_goals simp only [Ph.rank]; omega

theorem getTempArray_spec {r : Nat} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core}
    (hQ : ∀ t : List (Option Val), r ≤ t.length → Q () e { c with temp := t }) :
    ((getTempArray (r : Int)) e c).Good Q := by
  rw [good_getTempArray]
  split
  · next h =>
    have := hQ c.temp (by simp only [kSortStateTempSize] at h; omega)
    exact this
  · exact hQ _ (by simp only [List.length_replicate, kSortStateTempSize]; omega)

theorem mergeLow_good {baseA la0 lb0 : Nat} {c : Core} {e : ε} (hla : 0 < la0) (hlb : 0 < lb0)
    (hv : Vals c.work baseA (baseA + la0 + lb0)) :
    ((mergeLow cmp smiMax (baseA : Int) (la0 : Int) ((baseA + la0 : Nat) : Int) (lb0 : Int)) e c).Good
      (fun _ _ c' => PermOn c.work c'.work baseA (baseA + la0 + lb0) ∧ c'.runs = c.runs ∧
        c'.powers = c.powers ∧ c'.size = c.size) := by
  have hl := hv.1
  unfold mergeLow
  simp only [good_bind, good_dcheck]
  refine ⟨by omega, by omega, by omega, getTempArray_spec fun t ht => ?_⟩
  refine copy_good (sp := baseA) (dp := 0) (n := la0) (by simp only [Core.get_work]; omega)
    (by simp only [Core.get_temp]; omega) ?_
  simp only [Core.get_work, Core.get_temp, Core.put_temp]
  let k : MCtx := ⟨c.work, over t 0 (seg c.work baseA (baseA + la0)), baseA, la0, baseA + la0 + lb0, c.runs,
    c.powers, c.size⟩
  have hlenS : (seg c.work baseA (baseA + la0)).length = la0 := by rw [length_seg (by omega)]; omega
  have hTl : (over t 0 (seg c.work baseA (baseA + la0))).length = t.length :=
    length_over (by rw [hlenS]; omega)
  have hinv0 : LowInv k { c with temp := over t 0 (seg c.work baseA (baseA + la0)) }
      ⟨baseA, 0, ((baseA + la0 : Nat) : Int), la0, lb0⟩ := by
    refine ⟨baseA, 0, baseA + la0, la0, lb0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [k], Nat.le_refl _,
      rfl, by simp only [k]; omega, rfl, by simp only [k]; omega, fun _ _ => rfl, ?_, rfl, rfl, rfl⟩
    simp only [k, seg_self, List.nil_append, Nat.zero_add]
    have : seg (over t 0 (seg c.work baseA (baseA + la0))) 0 la0 = seg c.work baseA (baseA + la0) := by
      have := seg_over_in (l := t) (s := seg c.work baseA (baseA + la0)) (pos := 0) (by rw [hlenS]; omega)
      rwa [hlenS, Nat.zero_add] at this
    rw [this, ← seg_split c.work (Nat.le_add_right baseA la0) (by omega)]
  have hv' : Vals k.w0 k.baseA k.endPos := hv
  rw [good_mv]
  refine ⟨⟨by omega, by simp only [Core.get_work]; omega⟩, ⟨by omega, by simp only [Core.get_work]; omega⟩, ?_⟩
  simp only [Core.get_work, Core.put_work, Int.toNat_natCast]
  have hinv1 := (hinv0.moveB (d := baseA) (b := baseA + la0) (lb := lb0) rfl rfl rfl hlb).congr
    (s' := ⟨(baseA : Int) + 1, 0, ((baseA + la0 : Nat) : Int) + 1, la0, (lb0 : Int) - 1⟩) rfl rfl rfl rfl rfl
  refine Res.Good.mono (Q := fun x _ c' => LowPost k x c') ?_ ?_
  · rintro x e2 c2 hx
    cases x with
    | succeed s =>
      obtain ⟨hinv, hor⟩ := hx
      obtain ⟨d, ct, b, la, lb, e1, e2', e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hinv.ghosts
      have hT : c2.temp.length = k.T.length := by rw [h5]
      rw [lowFinish, good_ite]
      split
      · refine copy_good_int (spN := ct) (dpN := d) (nN := la) e2' e1 e4 (by bnd) (by bnd) ?_
        have := (hinv.copyA e1 e2' e4 (Nat.le_refl la)).final (by simp only; omega)
        simp only [Core.get_work, Core.get_temp, Core.put_work]
        rw [show seg c2.temp ct (ct + la) = seg k.T ct (ct + la) by rw [h5]]
        exact ⟨this.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩
      · have := hinv.final (by omega)
        exact ⟨this.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩
    | copy s =>
      obtain ⟨hinv, hla1, hlb1⟩ := hx
      obtain ⟨d, ct, b, la, lb, e1, e2', e3, e4, e5, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hinv.ghosts
      have hT : c2.temp.length = k.T.length := by rw [h5]
      rw [lowFinish]
      simp only [good_bind, good_dcheck]
      refine ⟨⟨hla1, hlb1⟩, ?_⟩
      refine copy_good_int (spN := b) (dpN := d) (nN := lb) e3 e1 e5 (by bnd) (by bnd) ?_
      have hi := hinv.copyB e1 e3 e5 (Nat.le_refl lb)
      simp only [Core.get_work, Core.put_work]
      have hlo : (over c2.work d (seg c2.work b (b + lb))).length = c2.work.length :=
        length_over (by rw [length_seg (by omega)]; omega)
      rw [good_mv]
      refine ⟨⟨by omega, by bnd⟩, ⟨by omega, by bnd⟩, ?_⟩
      simp only [Core.get_work, Core.get_temp, Core.put_work]
      rw [show s.ct.toNat = ct by omega, show (s.dest + s.lb).toNat = d + lb by omega,
        show c2.temp.getD ct none = k.T.getD ct none by rw [h5]]
      have := (hi.moveA (d := d + lb) (ct := ct) (la := la) (by sos) (by sos) (by sos) (by omega)).final
        (by simp only; omega)
      exact ⟨this.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩
  · rw [lowRun, good_ite]
    split
    · exact ⟨hinv1, Or.inl (by sos)⟩
    · rw [good_ite]
      split
      · exact ⟨hinv1, by sos, by sos⟩
      · rw [good_bind, good_getMinGallop]
        exact lowLoop_good cmp smiMax hv' _ _ _ e _ hinv1 (by sos) (by sos)

end

end ArraySort
