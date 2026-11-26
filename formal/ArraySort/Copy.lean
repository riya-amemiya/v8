import ArraySort.Basic

namespace ArraySort

open Torque

theorem getD_eq_getElem {l : List (Option Val)} {i : Nat} (h : i < l.length) :
    l.getD i none = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem seg_snoc_getD {l : List (Option Val)} {lo hi : Nat} (h1 : lo ≤ hi) (h2 : hi < l.length) :
    seg l lo (hi + 1) = seg l lo hi ++ [l.getD hi none] := by
  rw [seg_snoc h1 h2, getD_eq_getElem h2]

theorem seg_cons_getD {l : List (Option Val)} {lo hi : Nat} (h1 : lo < hi) (h2 : lo < l.length) :
    seg l lo hi = l.getD lo none :: seg l (lo + 1) hi := by
  rw [seg_cons h1 h2, getD_eq_getElem h2]

theorem getD_over_out {l s : List (Option Val)} {pos j : Nat} (h : pos + s.length ≤ l.length)
    (hj : j < pos ∨ pos + s.length ≤ j) : (over l pos s).getD j none = l.getD j none := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, getElem?_over_out h hj]

section

variable {ε : Type}

theorem copyFwd_good {src dst : Arr} {sp dp n : Nat} {c0 : Core} {e : ε} {Q : Unit → ε → Core → Prop}
    (hs : sp + n ≤ (c0.get src).length) (hd : dp + n ≤ (c0.get dst).length)
    (hov : src = dst → dp ≤ sp)
    (hQ : Q () e (c0.put dst (over (c0.get dst) dp (seg (c0.get src) sp (sp + n))))) :
    ∀ d k, n = k + d → ∀ c, c = c0.put dst (over (c0.get dst) dp (seg (c0.get src) sp (sp + k))) →
      ((copyFwd src dst ((sp + n : Nat) : Int) ((sp + k : Nat) : Int) ((dp + k : Nat) : Int)) e c).Good Q
  | 0, k, hk, c, hc => by
    rw [copyFwd, dite_eq_right (by omega)]
    subst hc
    have : k = n := by omega
    subst this
    exact hQ
  | d + 1, k, hk, c, hc => by
    have hlen : (seg (c0.get src) sp (sp + k)).length = k := by
      rw [length_seg (by omega)]
      omega
    rw [copyFwd, dite_eq_left (by omega), good_seq, good_mv]
    have hcd : c.get dst = over (c0.get dst) dp (seg (c0.get src) sp (sp + k)) := by
      rw [hc, Core.get_put_same]
    have hread : (c.get src).getD (sp + k) none = (c0.get src).getD (sp + k) none := by
      by_cases h : src = dst
      · subst h
        rw [hcd, getD_over_out (by rw [hlen]; omega) (by rw [hlen]; have := hov rfl; omega)]
      · rw [hc, Core.get_put_ne _ (Ne.symm h)]
    have hlsrc : (c.get src).length = (c0.get src).length := by
      by_cases h : src = dst
      · subst h
        rw [hcd, length_over (by rw [hlen]; omega)]
      · rw [hc, Core.get_put_ne _ (Ne.symm h)]
    have hldst : (c.get dst).length = (c0.get dst).length := by
      rw [hcd, length_over (by rw [hlen]; omega)]
    refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
    simp only [Int.toNat_natCast]
    rw [hread, hcd]
    have := copyFwd_good hs hd hov hQ d (k + 1) (by omega)
      (c0.put dst (over (c0.get dst) dp (seg (c0.get src) sp (sp + (k + 1))))) rfl
    rw [show ((sp + k : Nat) : Int) + 1 = ((sp + (k + 1) : Nat) : Int) by omega,
      show ((dp + k : Nat) : Int) + 1 = ((dp + (k + 1) : Nat) : Int) by omega, hc, Core.put_put]
    have heq : (over (c0.get dst) dp (seg (c0.get src) sp (sp + k))).set (dp + k)
        ((c0.get src).getD (sp + k) none) =
        over (c0.get dst) dp (seg (c0.get src) sp (sp + (k + 1))) := by
      rw [show dp + k = dp + (seg (c0.get src) sp (sp + k)).length by rw [hlen],
        over_snoc (by rw [hlen]; omega), show sp + (k + 1) = sp + k + 1 by omega,
        seg_snoc_getD (by omega) (by omega)]
    rw [heq]
    exact this

theorem copyBwd_good {src dst : Arr} {sp dp n : Nat} {c0 : Core} {e : ε} {Q : Unit → ε → Core → Prop}
    (hs : sp + n ≤ (c0.get src).length) (hd : dp + n ≤ (c0.get dst).length)
    (hov : src = dst → sp ≤ dp)
    (hQ : Q () e (c0.put dst (over (c0.get dst) dp (seg (c0.get src) sp (sp + n))))) :
    ∀ d, d ≤ n → ∀ c,
      c = c0.put dst (over (c0.get dst) (dp + d) (seg (c0.get src) (sp + d) (sp + n))) →
      ((copyBwd src dst (sp : Int) ((sp + d : Nat) - 1 : Int) ((dp + d : Nat) - 1 : Int)) e c).Good Q
  | 0, _, c, hc => by
    rw [copyBwd, dite_eq_right (by omega)]
    subst hc
    exact hQ
  | d + 1, hdn, c, hc => by
    have hlen : (seg (c0.get src) (sp + (d + 1)) (sp + n)).length = n - (d + 1) := by
      rw [length_seg (by omega)]
      omega
    rw [copyBwd, dite_eq_left (by omega), good_seq, good_mv]
    have hcd : c.get dst =
        over (c0.get dst) (dp + (d + 1)) (seg (c0.get src) (sp + (d + 1)) (sp + n)) := by
      rw [hc, Core.get_put_same]
    have hread : (c.get src).getD (sp + d) none = (c0.get src).getD (sp + d) none := by
      by_cases h : src = dst
      · subst h
        rw [hcd, getD_over_out (by rw [hlen]; omega) (by have := hov rfl; omega)]
      · rw [hc, Core.get_put_ne _ (Ne.symm h)]
    have hlsrc : (c.get src).length = (c0.get src).length := by
      by_cases h : src = dst
      · subst h
        rw [hcd, length_over (by rw [hlen]; omega)]
      · rw [hc, Core.get_put_ne _ (Ne.symm h)]
    have hldst : (c.get dst).length = (c0.get dst).length := by
      rw [hcd, length_over (by rw [hlen]; omega)]
    refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
    rw [show (((sp + (d + 1) : Nat) : Int) - 1).toNat = sp + d by omega,
      show (((dp + (d + 1) : Nat) : Int) - 1).toNat = dp + d by omega, hread, hcd]
    have heq : (over (c0.get dst) (dp + (d + 1)) (seg (c0.get src) (sp + (d + 1)) (sp + n))).set
        (dp + d) ((c0.get src).getD (sp + d) none) =
        over (c0.get dst) (dp + d) (seg (c0.get src) (sp + d) (sp + n)) := by
      rw [show dp + d = dp + (d + 1) - 1 by omega, over_cons (by omega) (by rw [hlen]; omega),
        show dp + (d + 1) - 1 = dp + d by omega,
        seg_cons_getD (l := c0.get src) (lo := sp + d) (by omega) (by omega), Nat.add_assoc]
    have := copyBwd_good hs hd hov hQ d (by omega)
      (c0.put dst (over (c0.get dst) (dp + d) (seg (c0.get src) (sp + d) (sp + n)))) rfl
    rw [show (((sp + (d + 1) : Nat) : Int) - 1) - 1 = ((sp + d : Nat) : Int) - 1 by omega,
      show (((dp + (d + 1) : Nat) : Int) - 1) - 1 = ((dp + d : Nat) : Int) - 1 by omega, hc,
      Core.put_put, heq]
    exact this

theorem copy_good {src dst : Arr} {sp dp n : Nat} {e : ε} {c : Core} {Q : Unit → ε → Core → Prop}
    (hs : sp + n ≤ (c.get src).length) (hd : dp + n ≤ (c.get dst).length)
    (hQ : Q () e (c.put dst (over (c.get dst) dp (seg (c.get src) sp (sp + n))))) :
    ((copy src (sp : Int) dst (dp : Int) (n : Int)) e c).Good Q := by
  unfold copy
  simp only [good_bind, good_dcheck, good_getCore]
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  rw [good_ite]
  split
  · have h := copyBwd_good (src := src) (dst := dst) (sp := sp) (dp := dp) (n := n) (c0 := c) (e := e)
      (Q := Q) hs hd (fun _ => by omega) hQ n (Nat.le_refl _) c
      (by rw [show sp + n = sp + n by rfl, seg_self, over_nil, Core.put_get])
    rw [show (sp : Int) + (n : Int) - 1 = ((sp + n : Nat) : Int) - 1 by omega,
      show (dp : Int) + (n : Int) - 1 = ((dp + n : Nat) : Int) - 1 by omega]
    exact h
  · have h := copyFwd_good (src := src) (dst := dst) (sp := sp) (dp := dp) (n := n) (c0 := c) (e := e)
      (Q := Q) hs hd (fun _ => by omega) hQ n 0 (by omega) c
      (by rw [Nat.add_zero, seg_self, over_nil, Core.put_get])
    rw [show (sp : Int) + (n : Int) = ((sp + n : Nat) : Int) by omega,
      show (sp : Int) = ((sp + 0 : Nat) : Int) by omega, show (dp : Int) = ((dp + 0 : Nat) : Int) by omega]
    exact h

end

end ArraySort
