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

structure LowCtx where
  w0 : List (Option Val)
  T : List (Option Val)
  baseA : Nat
  la0 : Nat
  endPos : Nat
  runs : List Int
  powers : List Int
  size : Int

def LowInv (k : LowCtx) (c : Core) (s : MS) : Prop :=
  ∃ d ct b la lb : Nat, s = ⟨d, ct, b, la, lb⟩ ∧ d + la = b ∧ b + lb = k.endPos ∧ ct + la = k.la0 ∧
    k.baseA ≤ d ∧ c.temp = k.T ∧ k.la0 ≤ k.T.length ∧ c.work.length = k.w0.length ∧
    k.endPos ≤ k.w0.length ∧
    (∀ i, (i < k.baseA ∨ k.endPos ≤ i) → c.work[i]? = k.w0[i]?) ∧
    (seg c.work k.baseA d ++ seg k.T ct (ct + la) ++ seg c.work b k.endPos).Perm
      (seg k.w0 k.baseA k.endPos) ∧
    c.runs = k.runs ∧ c.powers = k.powers ∧ c.size = k.size

theorem LowInv.copyA {k : LowCtx} {c : Core} {d ct b la lb n : Nat}
    (h : LowInv k c ⟨d, ct, b, la, lb⟩) (hn : n ≤ la) :
    LowInv k { c with work := over c.work d (seg k.T ct (ct + n)) }
      ⟨((d + n : Nat) : Int), ((ct + n : Nat) : Int), b, ((la - n : Nat) : Int), lb⟩ := by
  obtain ⟨d', ct', b', la', lb', hs, h1, h2, h3, h4, h5, h6, h7, h8, h9, hp, h10, h11, h12⟩ := h
  simp only [MS.mk.injEq, Int.natCast_inj] at hs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hs
  have hlen : (seg k.T ct (ct + n)).length = n := by rw [length_seg (by omega)]; omega
  refine ⟨d + n, ct + n, b, la - n, lb, rfl, by omega, h2, by omega, by omega, h5, h6, ?_, h8, ?_, ?_,
    h10, h11, h12⟩
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

theorem LowInv.copyB {k : LowCtx} {c : Core} {d ct b la lb n : Nat}
    (h : LowInv k c ⟨d, ct, b, la, lb⟩) (hn : n ≤ lb) :
    LowInv k { c with work := over c.work d (seg c.work b (b + n)) }
      ⟨((d + n : Nat) : Int), ct, ((b + n : Nat) : Int), la, ((lb - n : Nat) : Int)⟩ := by
  obtain ⟨d', ct', b', la', lb', hs, h1, h2, h3, h4, h5, h6, h7, h8, h9, hp, h10, h11, h12⟩ := h
  simp only [MS.mk.injEq, Int.natCast_inj] at hs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hs
  have hlen : (seg c.work b (b + n)).length = n := by rw [length_seg (by omega)]; omega
  refine ⟨d + n, ct, b + n, la, lb - n, rfl, by omega, by omega, h3, by omega, h5, h6, ?_, h8, ?_, ?_,
    h10, h11, h12⟩
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

theorem LowInv.moveA {k : LowCtx} {c : Core} {d ct b la lb : Nat}
    (h : LowInv k c ⟨d, ct, b, la, lb⟩) (hn : 1 ≤ la) :
    LowInv k { c with work := c.work.set d (k.T.getD ct none) }
      ⟨((d : Int) + 1), ((ct : Int) + 1), b, ((la : Int) - 1), lb⟩ := by
  have hl : d < c.work.length := by
    obtain ⟨d', ct', b', la', lb', hs, h1, h2, h3, h4, h5, h6, h7, h8, _⟩ := h
    simp only [MS.mk.injEq, Int.natCast_inj] at hs
    omega
  have hc : ct + 1 ≤ k.T.length := by
    obtain ⟨d', ct', b', la', lb', hs, h1, h2, h3, h4, h5, h6, h7, h8, _⟩ := h
    simp only [MS.mk.injEq, Int.natCast_inj] at hs
    omega
  have := h.copyA (n := 1) hn
  rw [show ((d + 1 : Nat) : Int) = (d : Int) + 1 by omega, show ((ct + 1 : Nat) : Int) = (ct : Int) + 1 by omega,
    show ((la - 1 : Nat) : Int) = (la : Int) - 1 by omega, seg_single hc,
    ← getD_eq_getElem hc, ← set_eq_over hl] at this
  exact this

theorem LowInv.moveB {k : LowCtx} {c : Core} {d ct b la lb : Nat}
    (h : LowInv k c ⟨d, ct, b, la, lb⟩) (hn : 1 ≤ lb) :
    LowInv k { c with work := c.work.set d (c.work.getD b none) }
      ⟨((d : Int) + 1), ct, ((b : Int) + 1), la, ((lb : Int) - 1)⟩ := by
  have hl : d < c.work.length ∧ b < c.work.length := by
    obtain ⟨d', ct', b', la', lb', hs, h1, h2, h3, h4, h5, h6, h7, h8, _⟩ := h
    simp only [MS.mk.injEq, Int.natCast_inj] at hs
    omega
  have := h.copyB (n := 1) hn
  rw [show ((d + 1 : Nat) : Int) = (d : Int) + 1 by omega, show ((b + 1 : Nat) : Int) = (b : Int) + 1 by omega,
    show ((lb - 1 : Nat) : Int) = (lb : Int) - 1 by omega, seg_single hl.2,
    ← getD_eq_getElem hl.2, ← set_eq_over hl.1] at this
  exact this

theorem LowInv.final {k : LowCtx} {c : Core} {d ct b : Nat} (h : LowInv k c ⟨d, ct, b, 0, 0⟩) :
    PermOn k.w0 c.work k.baseA k.endPos ∧ c.temp = k.T ∧ c.runs = k.runs ∧ c.powers = k.powers ∧
      c.size = k.size := by
  obtain ⟨d', ct', b', la', lb', hs, h1, h2, h3, h4, h5, h6, h7, h8, h9, hp, h10, h11, h12⟩ := h
  simp only [MS.mk.injEq, Int.natCast_inj] at hs
  obtain ⟨rfl, rfl, rfl, h0, h0'⟩ := hs
  have e1 : la' = 0 := by omega
  have e2 : lb' = 0 := by omega
  subst e1
  subst e2
  refine ⟨⟨h7, h9, ?_⟩, h5, h10, h11, h12⟩
  rw [Nat.add_zero, seg_self, List.append_nil, show b = k.endPos by omega, seg_self, List.append_nil,
    show d = k.endPos by omega] at hp
  exact hp

theorem LowInv.vals_work {k : LowCtx} {c : Core} {d ct b la lb : Nat}
    (h : LowInv k c ⟨d, ct, b, la, lb⟩) (hv : Vals k.w0 k.baseA k.endPos) : Vals c.work b k.endPos := by
  obtain ⟨d', ct', b', la', lb', hs, h1, h2, h3, h4, h5, h6, h7, h8, h9, hp, _⟩ := h
  simp only [MS.mk.injEq, Int.natCast_inj] at hs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hs
  exact vals_of_allSome (by omega) ((allSome_of_vals hv).perm hp).append_right

theorem LowInv.vals_temp {k : LowCtx} {c : Core} {d ct b la lb : Nat}
    (h : LowInv k c ⟨d, ct, b, la, lb⟩) (hv : Vals k.w0 k.baseA k.endPos) : Vals c.temp ct (ct + la) := by
  obtain ⟨d', ct', b', la', lb', hs, h1, h2, h3, h4, h5, h6, h7, h8, h9, hp, _⟩ := h
  simp only [MS.mk.injEq, Int.natCast_inj] at hs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hs
  rw [h5]
  exact vals_of_allSome (by omega) ((allSome_of_vals hv).perm hp).append_left.append_right

end ArraySort
