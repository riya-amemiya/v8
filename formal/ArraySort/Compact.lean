import ArraySort.Spec

namespace ArraySort

open Torque

def GInv (g : GFA) (vs : List Val) : Prop :=
  g.capacity = g.array.length ∧ g.length = vs.length ∧ seg g.array 0 g.length = vs.map some

theorem seg_zero {α : Type} (l : List α) (n : Nat) : seg l 0 n = l.take n := by
  simp [seg]

section

variable {ε : Type}

theorem gfaPush_good {g : GFA} {vs : List Val} {v : Val} {e : ε} {c : Core} (hg : GInv g vs)
    (hle : g.length ≤ g.capacity) :
    ((gfaPush g (some v)) e c).Good (fun g' e' c' => e' = e ∧ c' = c ∧ GInv g' (vs ++ [v]) ∧
      g'.length ≤ g'.capacity) := by
  obtain ⟨h1, h2, h3⟩ := hg
  unfold gfaPush gfaGrow
  simp only [good_bind, good_dcheck]
  refine ⟨hle, ?_⟩
  rw [good_ite]
  split
  · next hcl =>
    simp only [good_bind, good_dcheck, good_pure]
    refine ⟨by omega, ?_⟩
    have hlen : (g.array.take g.length ++ List.replicate (g.capacity + g.capacity / 2 + 16 - g.length) none).length =
        g.capacity + g.capacity / 2 + 16 := by
      simp [List.length_take]
      omega
    rw [good_ite, ite_eq_left (by rw [hlen]; omega)]
    refine ⟨rfl, rfl, ⟨by simp [hlen], by simp [h2], ?_⟩, by sos⟩
    rw [seg_set_snoc (Nat.zero_le _) (by rw [hlen]; omega)]
    have : seg (g.array.take g.length ++ List.replicate (g.capacity + g.capacity / 2 + 16 - g.length) none) 0
        g.length = vs.map some := by
      rw [seg_zero, List.take_append_of_le_length (by simp [List.length_take]; omega), List.take_take,
        Nat.min_self, ← seg_zero]
      exact h3
    rw [this]
    simp
  · next hcl =>
    simp only [good_pure]
    rw [good_ite, ite_eq_left (by omega)]
    refine ⟨rfl, rfl, ⟨by simp [h1], by simp [h2], ?_⟩, by simp only; omega⟩
    simp only
    rw [seg_set_snoc (Nat.zero_le _) (by omega), h3]
    simp

theorem fold_take_succ {l : List (Option Val)} {i : Nat} {isToSorted : Bool} {acc : List Val × Nat}
    (h : i < l.length) :
    (l.take (i + 1)).foldl (gstep isToSorted) acc = gstep isToSorted ((l.take i).foldl (gstep isToSorted) acc)
      (l.getD i none) := by
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem h, getD_eq_getElem h]
  rfl

theorem compactFast_good {isToSorted : Bool} {elems : List (Option Val)} {len : Nat} (hl : len ≤ elems.length)
    {e : ε} {c : Core} : ∀ d i g nu, len - i = d → i ≤ len → GInv g ((elems.take i).foldl (gstep isToSorted) ([], 0)).1 →
      g.length ≤ g.capacity → nu = ((elems.take i).foldl (gstep isToSorted) ([], 0)).2 →
      ((compactFast isToSorted elems len i g nu) e c).Good (fun r e' c' => e' = e ∧ c' = c ∧
        GInv r.1 ((elems.take len).foldl (gstep isToSorted) ([], 0)).1 ∧
        r.2 = ((elems.take len).foldl (gstep isToSorted) ([], 0)).2)
  | 0, i, g, nu, hd, hi, hg, hgl, hnu => by
    rw [compactFast, dite_eq_right (by omega)]
    have : i = len := by omega
    subst this
    exact ⟨rfl, rfl, hg, hnu⟩
  | d + 1, i, g, nu, hd, hi, hg, hgl, hnu => by
    rw [compactFast, dite_eq_left (by omega)]
    unfold elemAt
    rw [good_bind, good_ite, ite_eq_left (by omega), good_pure]
    have hstep := fold_take_succ (l := elems) (i := i) (isToSorted := isToSorted) (acc := ([], 0)) (by omega)
    cases hx : elems.getD i none with
    | none =>
      simp only
      apply compactFast_good hl d (i + 1) g _ (by omega) (by omega) ?_ hgl ?_
      · rw [hstep, hx]
        exact hg
      · rw [hstep, hx, hnu]
        rfl
    | some v =>
      simp only
      rw [good_ite]
      split
      · next hv =>
        apply compactFast_good hl d (i + 1) g _ (by omega) (by omega) ?_ hgl ?_
        · rw [hstep, hx]
          simp only [gstep, hv, ite_true]
          exact hg
        · rw [hstep, hx, hnu]
          simp only [gstep, hv, ite_true]
      · next hv =>
        refine good_bind_of (gfaPush_good hg hgl) ?_
        rintro g' e' c' ⟨rfl, rfl, hg', hgl'⟩
        apply compactFast_good hl d (i + 1) g' _ (by omega) (by omega) ?_ hgl' ?_
        · rw [hstep, hx]
          simp only [gstep, hv, ite_false]
          exact hg'
        · rw [hstep, hx, hnu]
          simp only [gstep, hv, ite_false]

end

theorem reach_step {cfg : Cfg} {mp : Maps} {r1 : Recv} {e : Ext} {r : Recv} (h : Reach cfg mp r1 e)
    (hs : RecvStep cfg mp e.recv r) : Reach cfg mp r1 (e.step r) :=
  ⟨hs.ok, fun hp => h.2.1 (hs.prot hp), fun hc => h.2.2 (hs.cow hc)⟩

theorem compactGeneric_good {cfg : Cfg} {mp : Maps} {r1 : Recv} {env : Env} (henv : EnvOK cfg mp env)
    {isToSorted : Bool} {len : Nat} {c : Core} :
    ∀ d i g (e : Ext) (acc : List Val × Nat), len - i = d → GInv g acc.1 → g.length ≤ g.capacity →
      Reach cfg mp r1 e →
      ((compactGeneric env isToSorted len i g acc.2) e c).Good (fun r e' c' => c' = c ∧ e'.log = e.log ∧
        Reach cfg mp r1 e' ∧ ∃ vs u, gatherGen env isToSorted len i e acc = some (vs, u, e') ∧ GInv r.1 vs ∧
          r.2 = u)
  | 0, i, g, e, acc, hd, hg, hgl, hr => by
    rw [compactGeneric, dite_eq_right (by omega)]
    refine ⟨rfl, rfl, hr, acc.1, acc.2, ?_, hg, rfl⟩
    rw [gatherGen, dite_eq_right (by omega)]
  | d + 1, i, g, e, acc, hd, hg, hgl, hr => by
    rw [compactGeneric, dite_eq_left (by omega), good_bind]
    unfold loadGeneric
    cases hl : env.load (!isToSorted) e.tick e.recv i with
    | none =>
      simp only [good_throw]
    | some p =>
      obtain ⟨x, r⟩ := p
      simp only [good_ok]
      have hr' := reach_step hr (henv.2.2.1 _ _ _ _ _ _ hl hr.1)
      have hgg : gatherGen env isToSorted len i e acc =
          gatherGen env isToSorted len (i + 1) (e.step r) (gstep isToSorted acc x) := by
        rw [gatherGen, dite_eq_left (by omega)]
        simp only [hl]
      cases x with
      | none =>
        simp only
        have := compactGeneric_good (isToSorted := isToSorted) (len := len) (c := c) henv d (i + 1) g
          (e.step r) (gstep isToSorted acc none) (by omega)
          (by simpa [gstep] using hg) hgl hr'
        rw [show (if isToSorted = true then acc.2 + 1 else acc.2) = (gstep isToSorted acc none).2 by rfl]
        refine this.mono ?_
        rintro r' e' c' ⟨h1, h2, h3, vs, u, h4, h5, h6⟩
        exact ⟨h1, h2, h3, vs, u, by rw [hgg]; exact h4, h5, h6⟩
      | some v =>
        simp only
        rw [good_ite]
        split
        · next hv =>
          have := compactGeneric_good (isToSorted := isToSorted) (len := len) (c := c) henv d (i + 1) g
            (e.step r) (gstep isToSorted acc (some v)) (by omega) (by simpa [gstep, hv] using hg) hgl hr'
          rw [show acc.2 + 1 = (gstep isToSorted acc (some v)).2 by simp [gstep, hv]]
          refine this.mono ?_
          rintro r' e' c' ⟨h1, h2, h3, vs, u, h4, h5, h6⟩
          exact ⟨h1, h2, h3, vs, u, by rw [hgg]; exact h4, h5, h6⟩
        · next hv =>
          refine good_bind_of (gfaPush_good hg hgl) ?_
          rintro g' e' c' ⟨he', hc', hg', hgl'⟩
          subst e'
          subst c'
          have := compactGeneric_good (isToSorted := isToSorted) (len := len) (c := c) henv d (i + 1) g'
            (e.step r) (gstep isToSorted acc (some v)) (by omega) (by simpa [gstep, hv] using hg') hgl' hr'
          rw [show acc.2 = (gstep isToSorted acc (some v)).2 by simp [gstep, hv]]
          refine this.mono ?_
          rintro r' e2 c2 ⟨h1, h2, h3, vs, u, h4, h5, h6⟩
          exact ⟨h1, h2, h3, vs, u, by rw [hgg]; exact h4, h5, h6⟩

end ArraySort
