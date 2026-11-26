import ArraySort.SortStack

namespace ArraySort

open Torque

def rB (c : Core) (j : Nat) : Int := c.runs.getD (2 * j) 0

def rL (c : Core) (j : Nat) : Int := c.runs.getD (2 * j + 1) 0

structure RunsOK (le : Val → Val → Bool) (w0 : List (Option Val)) (c : Core) (top : Nat) : Prop where
  rlen : c.runs.length = 85
  size : 0 ≤ c.size
  pos : ∀ j, j < c.size.toNat → 0 ≤ rB c j ∧ 0 < rL c j
  cont : ∀ j, j + 1 < c.size.toNat → rB c j + rL c j = rB c (j + 1)
  first : 0 < c.size → rB c 0 = 0
  empty : c.size = 0 → top = 0
  last : 0 < c.size → rB c (c.size.toNat - 1) + rL c (c.size.toNat - 1) = top
  sorted : ∀ j, j < c.size.toNat → seg c.work (rB c j).toNat (rB c j + rL c j).toNat =
    msort le (seg w0 (rB c j).toNat (rB c j + rL c j).toNat)

structure J (le : Val → Val → Bool) (w0 : List (Option Val)) (n : Nat) (c : Core) (top pend : Nat) : Prop where
  runs : RunsOK le w0 c top
  pendR : seg c.work top (top + pend) = msort le (seg w0 top (top + pend))
  rest : ∀ i, top + pend ≤ i → c.work[i]? = w0[i]?
  len : c.work.length = w0.length
  bnd : top + pend ≤ n
  wl : n ≤ w0.length
  vals : Vals w0 0 n

section

variable {le : Val → Val → Bool} {w0 : List (Option Val)} {c : Core} {top : Nat}

theorem RunsOK.end_le (h : RunsOK le w0 c top) :
    ∀ d j, j + d + 1 < c.size.toNat → rB c j + rL c j ≤ rB c (j + d + 1)
  | 0, j, hj => Int.le_of_eq (h.cont j (by omega))
  | d + 1, j, hj => by
    have h1 := RunsOK.end_le h d j (by omega)
    have h2 := h.cont (j + d + 1) (by omega)
    have h3 := (h.pos (j + d + 1) (by omega)).2
    rw [show j + (d + 1) + 1 = j + d + 1 + 1 by omega]
    omega

theorem RunsOK.end_top (h : RunsOK le w0 c top) (j : Nat) (hj : j < c.size.toNat) :
    rB c j + rL c j ≤ top := by
  have hl := h.last (by omega)
  by_cases hjl : j + 1 = c.size.toNat
  · rw [show j = c.size.toNat - 1 by omega]
    omega
  · have := h.end_le (c.size.toNat - 1 - j - 1) j (by omega)
    rw [show j + (c.size.toNat - 1 - j - 1) + 1 = c.size.toNat - 1 by omega] at this
    have := (h.pos (c.size.toNat - 1) (by omega)).2
    omega

theorem RunsOK.frame (h : RunsOK le w0 c top) {c' : Core} (hr : c'.runs = c.runs) (hs : c'.size = c.size)
    (hw : ∀ i, i < top → c'.work[i]? = c.work[i]?) : RunsOK le w0 c' top := by
  have hrB : ∀ j, rB c' j = rB c j := fun j => by simp only [rB, hr]
  have hrL : ∀ j, rL c' j = rL c j := fun j => by simp only [rL, hr]
  refine ⟨by rw [hr]; exact h.rlen, by rw [hs]; exact h.size, fun j hj => by rw [hrB, hrL]; exact h.pos j (by omega),
    fun j hj => by rw [hrB, hrL, hrB]; exact h.cont j (by omega), fun h0 => by rw [hrB]; exact h.first (by omega),
    fun h0 => h.empty (by omega), fun h0 => by rw [hs, hrB, hrL]; exact h.last (by omega), fun j hj => ?_⟩
  rw [hrB, hrL]
  have he := h.end_top j (by omega)
  have hp := h.pos j (by omega)
  rw [← h.sorted j (by omega)]
  exact seg_congr fun i _ hi2 => hw i (by omega)

theorem vals_join {l : List (Option Val)} {a b d : Nat} (h1 : Vals l a b) (h2 : Vals l b d) : Vals l a d := by
  refine ⟨h2.1, fun i hi1 hi2 => ?_⟩
  by_cases hib : i < b
  · exact h1.2 i hi1 hib
  · exact h2.2 i (by omega) hi2

end

section

variable {ε : Type} (cmp : Cmp ε) (smiMax : Nat) {le : Val → Val → Bool}

theorem mergeAt_tail (hle : TotalPreorder le) (hc : CmpOK le cmp) {w0 : List (Option Val)} {n top pend j : Nat}
    {c c2 : Core} {e : ε} (hJ : J le w0 n c top pend) (hs2 : 2 ≤ c.size.toNat)
    (hj : j + 2 = c.size.toNat ∨ j + 3 = c.size.toNat) (hw : c2.work = c.work) (hl : c2.runs.length = 85)
    (hsz : c2.size = c.size - 1)
    (hR2 : ∀ j', j' < c.size.toNat - 1 →
      rB c2 j' = (if j' < j then rB c j' else if j' = j then rB c j else rB c (j' + 1)) ∧
      rL c2 j' = (if j' < j then rL c j' else if j' = j then rL c j + rL c (j + 1) else rL c (j' + 1))) :
    ((mergeAtTail cmp smiMax (rB c j) (rL c j) (rB c (j + 1)) (rL c (j + 1))) e c2).Post
      (fun _ _ c' => J le w0 n c' top pend) := by
  have hR := hJ.runs
  have hp0 := hR.pos j (by omega)
  have hp1 := hR.pos (j + 1) (by omega)
  have hcj := hR.cont j (by omega)
  have he1 := hR.end_top (j + 1) (by omega)
  obtain ⟨bA, hbA⟩ : ∃ bA : Nat, rB c j = bA := ⟨(rB c j).toNat, by omega⟩
  obtain ⟨lA, hlA⟩ : ∃ lA : Nat, rL c j = lA := ⟨(rL c j).toNat, by omega⟩
  obtain ⟨lB, hlB⟩ : ∃ lB : Nat, rL c (j + 1) = lB := ⟨(rL c (j + 1)).toNat, by omega⟩
  have hbB : rB c (j + 1) = ((bA + lA : Nat) : Int) := by omega
  have hsA := hR.sorted j (by omega)
  have hsB := hR.sorted (j + 1) (by omega)
  rw [hbA, hlA, show ((bA : Int) + (lA : Int)).toNat = bA + lA by omega, Int.toNat_natCast] at hsA
  rw [hbB, hlB, show (((bA + lA : Nat) : Int) + (lB : Int)).toNat = bA + lA + lB by omega, Int.toNat_natCast] at hsB
  have hwl := hJ.len
  have hbn := hJ.bnd
  have hwl0 := hJ.wl
  have hvA : Vals c.work bA (bA + lA) :=
    vals_of_msort (by omega) hsA (hJ.vals.mono (Nat.zero_le _) (by have := hJ.bnd; omega))
  have hvB : Vals c.work (bA + lA) (bA + lA + lB) :=
    vals_of_msort (by omega) hsB (hJ.vals.mono (Nat.zero_le _) (by have := hJ.bnd; omega))
  rw [hbA, hlA, hbB, hlB]
  refine (mergeAtTail_post cmp smiMax hle hc (c := c2) (e := e) (bA := bA) (lA := lA) (lB := lB) (by omega)
    (by omega) (by rw [hw]; exact vals_join hvA hvB) (by rw [hw, hsA]; exact pairwise_msort hle _)
    (by rw [hw, hsB]; exact pairwise_msort hle _)).mono ?_
  rintro _ _ c' ⟨hm, hout, hlen, hru, hsi, -⟩
  rw [hw] at hm hout hlen
  have hsize : c'.size.toNat = c.size.toNat - 1 := by rw [hsi, hsz]; omega
  have hrB : ∀ j', rB c' j' = rB c2 j' := fun j' => by simp only [rB, hru]
  have hrL : ∀ j', rL c' j' = rL c2 j' := fun j' => by simp only [rL, hru]
  have hlow : ∀ j', j' < j → rB c j' + rL c j' ≤ bA := by
    intro j' hj'
    have := hR.end_le (j - j' - 1) j' (by omega)
    rw [show j' + (j - j' - 1) + 1 = j by omega] at this
    omega
  refine ⟨⟨by rw [hru]; exact hl, by rw [hsi, hsz]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, hJ.bnd, hJ.wl, hJ.vals⟩
  · intro j' hj'
    rw [hrB, hrL, (hR2 j' (by omega)).1, (hR2 j' (by omega)).2]
    by_cases h1 : j' < j
    · rw [ite_eq_left h1, ite_eq_left h1]
      exact hR.pos j' (by omega)
    · by_cases h2 : j' = j
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h1, ite_eq_left h2]
        omega
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, ite_eq_right h2]
        exact hR.pos (j' + 1) (by omega)
  · intro j' hj'
    rw [hrB, hrL, hrB, (hR2 j' (by omega)).1, (hR2 j' (by omega)).2, (hR2 (j' + 1) (by omega)).1]
    by_cases h1 : j' + 1 < j
    · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left h1]
      exact hR.cont j' (by omega)
    · by_cases h2 : j' + 1 = j
      · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left h2]
        rw [← h2]
        exact hR.cont j' (by omega)
      · by_cases h3 : j' = j
        · subst h3
          rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega)]
          have := hR.cont (j' + 1) (by omega)
          omega
        · rw [ite_eq_right (by omega), ite_eq_right h3, ite_eq_right (by omega), ite_eq_right h3, ite_eq_right (by omega), ite_eq_right (by omega)]
          exact hR.cont (j' + 1) (by omega)
  · intro _
    rw [hrB, (hR2 0 (by omega)).1]
    by_cases h1 : 0 < j
    · rw [ite_eq_left h1]
      exact hR.first (by omega)
    · rw [ite_eq_right h1, ite_eq_left (by omega), show j = 0 by omega]
      exact hR.first (by omega)
  · intro h0
    rw [hsi, hsz] at h0
    omega
  · intro _
    rw [hsize, hrB, hrL, (hR2 _ (by omega)).1, (hR2 _ (by omega)).2]
    have hl0 := hR.last (by omega)
    rcases hj with hj | hj
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      rw [show c.size.toNat - 1 = j + 1 by omega] at hl0
      omega
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        show c.size.toNat - 1 - 1 + 1 = c.size.toNat - 1 by omega]
      exact hl0
  · intro j' hj'
    rw [hrB, hrL, (hR2 j' (by omega)).1, (hR2 j' (by omega)).2]
    by_cases h1 : j' < j
    · rw [ite_eq_left h1, ite_eq_left h1]
      have hpj := hR.pos j' (by omega)
      have := hlow j' h1
      rw [← hR.sorted j' (by omega)]
      exact seg_congr fun i _ hi2 => hout i (Or.inl (by omega))
    · by_cases h2 : j' = j
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h1, ite_eq_left h2, hbA, hlA, hlB,
          show ((bA : Int) + ((lA : Int) + (lB : Int))).toNat = bA + lA + lB by omega, Int.toNat_natCast, hm, hsA, hsB,
          ← msort_append hle, ← seg_split w0 (show bA ≤ bA + lA by omega) (show bA + lA ≤ bA + lA + lB by omega)]
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, ite_eq_right h2]
        have hpj := hR.pos (j' + 1) (by omega)
        have hge : bA + lA + lB ≤ (rB c (j' + 1)).toNat := by
          have := hR.end_le (j' - j - 1) (j + 1) (by omega)
          rw [show j + 1 + (j' - j - 1) + 1 = j' + 1 by omega] at this
          omega
        rw [← hR.sorted (j' + 1) (by omega)]
        exact seg_congr fun i hi1 _ => hout i (Or.inr (by omega))
  · rw [← hJ.pendR]
    exact seg_congr fun i hi1 _ => hout i (Or.inr (by omega))
  · intro i hi
    rw [hout i (Or.inr (by omega))]
    exact hJ.rest i hi
  · rw [hlen]
    exact hwl

theorem mergeAt_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {w0 : List (Option Val)} {n top pend : Nat}
    {i : Int} {c : Core} {e : ε} (hJ : J le w0 n c top pend) :
    ((mergeAt cmp smiMax i) e c).Post (fun _ _ c' => J le w0 n c' top pend) := by
  have hR := hJ.runs
  unfold mergeAt
  simp only [post_bind, post_getSize, post_dcheck, post_runBase, post_runLen, post_setRunLen]
  intro _ h2 h0 hi _ _ _ _ _ _ hb5
  obtain ⟨j, rfl⟩ : ∃ j : Nat, i = j := ⟨i.toNat, by omega⟩
  have hsz := hR.size
  rw [show (2 * (j : Int)).toNat = 2 * j by omega, show (2 * (j : Int) + 1).toNat = 2 * j + 1 by omega,
    show (2 * ((j : Int) + 1)).toNat = 2 * (j + 1) by omega,
    show (2 * ((j : Int) + 1) + 1).toNat = 2 * (j + 1) + 1 by omega]
  have hrl := hR.rlen
  rw [post_doIf]
  split
  · next h3 =>
    simp only [post_bind, post_runBase, post_runLen, post_setRunBase, post_setRunLen, List.length_set]
    intro _ _ _ _
    rw [show (2 * ((j : Int) + 2)).toNat = 2 * (j + 2) by omega,
      show (2 * ((j : Int) + 2) + 1).toNat = 2 * (j + 2) + 1 by omega,
      show (2 * ((j : Int) + 1)).toNat = 2 * (j + 1) by omega,
      show (2 * ((j : Int) + 1) + 1).toNat = 2 * (j + 1) + 1 by omega,
      getD_set_ne (by omega), getD_set_ne (by omega), post_setSize]
    refine mergeAt_tail cmp smiMax hle hc hJ (by omega) (Or.inr (by omega)) rfl (by simp [hrl]) rfl ?_
    intro j' hj'
    simp only [rB, rL]
    by_cases h1 : j' < j
    · rw [ite_eq_left h1, ite_eq_left h1, getD_set_ne (by omega), getD_set_ne (by omega), getD_set_ne (by omega),
        getD_set_ne (by omega), getD_set_ne (by omega), getD_set_ne (by omega)]
      exact ⟨rfl, rfl⟩
    · by_cases h2 : j' = j
      · subst h2
        rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_right h1, ite_eq_left rfl, getD_set_ne (by omega),
          getD_set_ne (by omega), getD_set_ne (by omega), getD_set_ne (by omega), getD_set_ne (by omega),
          getD_set_eq (by omega)]
        exact ⟨rfl, rfl⟩
      · have : j' = j + 1 := by omega
        subst this
        rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, ite_eq_right h2, getD_set_ne (by omega),
          getD_set_eq (by simp; omega), getD_set_eq (by simp; omega)]
        exact ⟨rfl, rfl⟩
  · next h3 =>
    rw [post_setSize]
    refine mergeAt_tail cmp smiMax hle hc hJ (by omega) (Or.inl (by omega)) rfl (by simp [hrl]) rfl ?_
    intro j' hj'
    simp only [rB, rL]
    by_cases h1 : j' < j
    · rw [ite_eq_left h1, ite_eq_left h1, getD_set_ne (by omega), getD_set_ne (by omega)]
      exact ⟨rfl, rfl⟩
    · have : j' = j := by omega
      subst this
      rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_right h1, ite_eq_left rfl, getD_set_ne (by omega),
        getD_set_eq (by omega)]
      exact ⟨rfl, rfl⟩

theorem mergeCollapse_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {w0 : List (Option Val)}
    {n top pend : Nat} (p : Int) :
    ∀ d (stackSize : Int) (e : ε) (c : Core), stackSize.toNat = d → J le w0 n c top pend →
      ((mergeCollapse cmp smiMax p stackSize) e c).Post (fun _ _ c' => J le w0 n c' top pend) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
  intro stackSize e c hd hJ
  rw [mergeCollapse, post_dite]
  split
  · simp only [post_bind, post_getPower]
    intro _
    rw [post_ite]
    split
    · rw [post_bind]
      refine (mergeAt_post cmp smiMax hle hc hJ).mono ?_
      rintro _ e' c' hJ'
      rw [post_bind, post_getSize]
      intro _
      rw [post_dite]
      split
      · exact ih _ (by omega) _ e' c' rfl hJ'
      · trivial
    · exact hJ
  · exact hJ

theorem finalPick_post {s : Int} {e : ε} {c : Core} :
    ((finalPick s : M ε Int) e c).Post (fun _ e' c' => e' = e ∧ c' = c) := by
  unfold finalPick
  rw [post_ite]
  split
  · simp [post_bind, post_runLen, post_pure]
  · exact ⟨rfl, rfl⟩

theorem finalLoop_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {w0 : List (Option Val)} {n top pend : Nat} :
    ∀ d (s : Int) (e : ε) (c : Core), s.toNat = d → J le w0 n c top pend →
      ((finalLoop cmp smiMax s) e c).Post (fun _ _ c' => J le w0 n c' top pend) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
  intro s e c hd hJ
  rw [finalLoop, post_dite]
  split
  · rw [post_bind]
    refine finalPick_post.mono ?_
    rintro _ e1 c1 ⟨rfl, rfl⟩
    rw [post_bind]
    refine (mergeAt_post cmp smiMax hle hc hJ).mono ?_
    rintro _ e' c' hJ'
    rw [post_bind, post_getSize]
    intro _
    rw [post_dite]
    split
    · exact ih _ (by omega) _ e' c' rfl hJ'
    · trivial
  · exact hJ

theorem J.powers {w0 : List (Option Val)} {n top pend : Nat} {c : Core} (hJ : J le w0 n c top pend)
    (ps : List Int) : J le w0 n { c with powers := ps } top pend :=
  ⟨hJ.runs.frame rfl rfl fun _ _ => rfl, hJ.pendR, hJ.rest, hJ.len, hJ.bnd, hJ.wl, hJ.vals⟩

theorem pushRun_post {w0 : List (Option Val)} {n low cur : Nat} {c : Core} {e : ε} (hJ : J le w0 n c low cur)
    (hcur : 0 < cur) :
    ((pushRun (low : Int) (cur : Int) : M ε Unit) e c).Post (fun _ _ c' => J le w0 n c' (low + cur) 0) := by
  have hR := hJ.runs
  have hsz := hR.size
  have hrl := hR.rlen
  unfold pushRun
  simp only [post_bind, post_getSize, post_dcheck, post_setRunBase, post_setRunLen, post_setSize, List.length_set]
  intro _ _ _ _
  obtain ⟨s, hs⟩ : ∃ s : Nat, c.size = s := ⟨c.size.toNat, by omega⟩
  have hst : c.size.toNat = s := by omega
  rw [show (2 * c.size).toNat = 2 * s by omega, show (2 * c.size + 1).toNat = 2 * s + 1 by omega]
  let c' : Core := { c with runs := (c.runs.set (2 * s) (low : Int)).set (2 * s + 1) (cur : Int), size := c.size + 1 }
  have hB : ∀ j, j < s → rB c' j = rB c j := fun j hj => by
    simp only [c', rB]
    rw [getD_set_ne (by omega), getD_set_ne (by omega)]
  have hL : ∀ j, j < s → rL c' j = rL c j := fun j hj => by
    simp only [c', rL]
    rw [getD_set_ne (by omega), getD_set_ne (by omega)]
  have hBs : rB c' s = low := by
    simp only [c', rB]
    rw [getD_set_ne (by omega), getD_set_eq (by omega)]
  have hLs : rL c' s = cur := by
    simp only [c', rL]
    rw [getD_set_eq (by simp; omega)]
  have hst' : c'.size.toNat = s + 1 := by simp only [c']; omega
  show J le w0 n c' (low + cur) 0
  refine ⟨⟨by simp [c', hrl], by simp only [c']; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, hJ.len, ?_, hJ.wl, hJ.vals⟩
  · intro j hj
    rw [hst'] at hj
    by_cases h1 : j < s
    · rw [hB j h1, hL j h1]
      exact hR.pos j (by omega)
    · rw [show j = s by omega, hBs, hLs]
      omega
  · intro j hj
    rw [hst'] at hj
    by_cases h1 : j + 1 < s
    · rw [hB j (by omega), hL j (by omega), hB (j + 1) h1]
      exact hR.cont j (by omega)
    · rw [hB j (by omega), hL j (by omega), show j + 1 = s by omega, hBs]
      have := hR.last (by omega)
      rw [hst, show s - 1 = j by omega] at this
      exact this
  · intro _
    by_cases h0 : s = 0
    · subst h0
      rw [hBs]
      have := hR.empty (by omega)
      omega
    · rw [hB 0 (by omega)]
      exact hR.first (by omega)
  · intro h0
    simp only [c'] at h0
    omega
  · intro _
    rw [hst', show s + 1 - 1 = s by omega, hBs, hLs]
    push_cast
    rfl
  · intro j hj
    rw [hst'] at hj
    by_cases h1 : j < s
    · rw [hB j h1, hL j h1]
      exact hR.sorted j (by omega)
    · rw [show j = s by omega, hBs, hLs, Int.toNat_natCast, show ((low : Int) + (cur : Int)).toNat = low + cur by omega]
      exact hJ.pendR
  · simp only [Nat.add_zero, seg_self]
    simp [msort]
  · intro i hi
    exact hJ.rest i (by omega)
  · have := hJ.bnd
    omega

theorem nodePower_post {s1 n1 n2 n : Int} {e : ε} {c : Core} :
    ((nodePower s1 n1 n2 n : M ε Int) e c).Post (fun _ e' c' => e' = e ∧ c' = c) := by
  unfold nodePower
  simp [post_bind, post_dcheck, post_pure]

theorem collapseAndPush_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {w0 : List (Option Val)}
    {n low cur : Nat} {length : Int} {c : Core} {e : ε} (hJ : J le w0 n c low cur) (hcur : 0 < cur) :
    ((collapseAndPush cmp smiMax length (low : Int) (cur : Int)) e c).Post
      (fun _ _ c' => J le w0 n c' (low + cur) 0) := by
  unfold collapseAndPush
  simp only [post_bind, post_getSize]
  intro _
  rw [post_ite]
  split
  · exact pushRun_post hJ hcur
  · simp only [post_bind, post_runBase, post_runLen]
    intro _ _
    refine nodePower_post.mono ?_
    rintro p e1 c1 ⟨he1, hc1⟩
    subst e1
    subst c1
    refine (mergeCollapse_post cmp smiMax hle hc p c.size.toNat c.size e c rfl hJ).mono ?_
    rintro ss e2 c2 hJ2
    have htail : ∀ (e3 : ε), ((setPower (ss - 1) p : M ε Unit) e3 c2).Post
        (fun _ e4 c4 => ((pushRun (low : Int) (cur : Int) : M ε Unit) e4 c4).Post
          (fun _ _ c' => J le w0 n c' (low + cur) 0)) := by
      intro e3
      rw [post_setPower]
      intro _
      exact pushRun_post (hJ2.powers _) hcur
    rw [post_doIf]
    split
    · simp only [post_bind, post_getPower, post_dcheck]
      intro _ _
      exact htail e2
    · exact htail e2

theorem vals_of_rest {w0 w : List (Option Val)} {lo hi n : Nat} (hv : Vals w0 0 n) (hhi : hi ≤ n)
    (hlen : w.length = w0.length) (hr : ∀ i, lo ≤ i → w[i]? = w0[i]?) : Vals w lo hi := by
  refine ⟨by have := hv.1; omega, fun i h1 h2 => ?_⟩
  obtain ⟨v, hv'⟩ := hv.2 i (Nat.zero_le _) (by omega)
  refine ⟨v, ?_⟩
  rw [List.getD_eq_getElem?_getD, hr i h1, ← List.getD_eq_getElem?_getD, hv']

theorem mainLoop_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {w0 : List (Option Val)} {n : Nat}
    {length mrStep mrRem mrThr : Int} :
    ∀ d (low remaining : Nat) (acc : Int) (e : ε) (c : Core), remaining = d → low + remaining = n →
      J le w0 n c low 0 →
      ((mainLoop cmp smiMax length mrStep mrRem mrThr (low : Int) (remaining : Int) acc) e c).Post
        (fun _ _ c' => J le w0 n c' n 0) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
  intro low remaining acc e c hd hn hJ
  have hR := hJ.runs
  rw [mainLoop, post_dite]
  split
  · next hrem =>
    simp only [post_bind, post_dcheck]
    intro _
    generalize (if mrThr ≤ acc + mrRem then mrStep + 1 else mrStep) = minRun
    generalize (if mrThr ≤ acc + mrRem then acc + mrRem - mrThr else acc + mrRem) = acc'
    have hvals : Vals c.work low (low + remaining) :=
      vals_of_rest hJ.vals (by omega) hJ.len fun i hi => hJ.rest i (by omega)
    rw [show (low : Int) + (remaining : Int) = ((low + remaining : Nat) : Int) by omega]
    refine (post_and (post_of_good (countAndMakeRun_good cmp (e := e) (by omega) hvals))
      (countAndMakeRun_post cmp hle hc (e := e) (by have := hJ.len; have := hJ.wl; omega))).mono ?_
    rintro r e1 c1 ⟨⟨hc1, hp1, k, hk, hk1, hk2⟩, k', hk', -, hlen1, hseg1, hun1⟩
    have hkk : k' = k := by omega
    rw [hkk] at hseg1 hun1
    subst hk
    have hrw : ∀ i, low ≤ i → c.work[i]? = w0[i]? := fun i hi => hJ.rest i (by omega)
    have hcont : ∀ (curN : Nat) (e2 : ε) (c2 : Core), J le w0 n c2 low curN → 0 < curN → curN ≤ remaining →
        ((collapseAndPush cmp smiMax length (low : Int) (curN : Int)) e2 c2).Post (fun _ e3 c3 =>
          ((if _h2 : 0 < (curN : Int) ∧ (curN : Int) ≤ (remaining : Int) then
              mainLoop cmp smiMax length mrStep mrRem mrThr ((low : Int) + curN) ((remaining : Int) - curN) acc'
            else ub) e3 c3).Post (fun _ _ c' => J le w0 n c' n 0)) := by
      intro curN e2 c2 hJ2 hc0 hcr
      refine (collapseAndPush_post cmp smiMax hle hc hJ2 hc0).mono ?_
      rintro _ e3 c3 hJ3
      rw [post_dite, dite_eq_left (show 0 < (curN : Int) ∧ (curN : Int) ≤ (remaining : Int) by omega)]
      rw [show (low : Int) + (curN : Int) = ((low + curN : Nat) : Int) by omega,
        show (remaining : Int) - (curN : Int) = ((remaining - curN : Nat) : Int) by omega]
      exact ih (remaining - curN) (by omega) (low + curN) (remaining - curN) _ e3 c3 rfl (by omega) hJ3
    have hrun1 : RunsOK le w0 c1 low := hR.frame (by rw [hc1]) (by rw [hc1]) fun i hi => hp1.out i (Or.inl hi)
    have hseg0 : seg c.work low (low + k) = seg w0 low (low + k) := seg_congr fun i h1 _ => hrw i h1
    unfold extendRun
    rw [post_ite]
    split
    · next hlt =>
      rw [post_bind]
      obtain ⟨m, hm⟩ : ∃ m : Nat, min minRun (remaining : Int) = (m : Int) :=
        ⟨(min minRun (remaining : Int)).toNat, by omega⟩
      rw [hm, show (low : Int) + (k : Int) = ((low + k : Nat) : Int) by omega,
        show (low : Int) + (m : Int) = ((low + m : Nat) : Int) by omega]
      have hkm : k ≤ m := by omega
      have hmr : m ≤ remaining := by omega
      have hrest1 : ∀ i, low + k ≤ i → c1.work[i]? = w0[i]? := fun i hi => by rw [hun1 i hi]; exact hrw i (by omega)
      have hv1 : Vals c1.work low (low + m) := by
        refine vals_join (b := low + k) (vals_of_msort (w0 := w0) (le := le)
          (by rw [hlen1, hJ.len]; have := hJ.wl; omega) (by rw [hseg1, hseg0]) ?_) ?_
        · exact hJ.vals.mono (Nat.zero_le _) (by omega)
        · exact vals_of_rest hJ.vals (by omega) (by rw [hlen1]; exact hJ.len) hrest1
      refine (post_and (post_of_good (binaryInsertionSort_good cmp (e := e1) (by omega) (by omega) hv1))
        (binaryInsertionSort_post cmp hle hc (e := e1) (by rw [hlen1, hJ.len]; have := hJ.wl; omega)
          (by rw [hseg1]; exact pairwise_msort hle _))).mono ?_
      rintro _ e2 c2 ⟨⟨hc2, hp2⟩, hseg2⟩
      rw [post_pure]
      refine hcont m e2 c2 ⟨hrun1.frame (by rw [hc2]) (by rw [hc2]) fun i hi => hp2.out i (Or.inl hi), ?_, ?_,
        by rw [hp2.len, hlen1]; exact hJ.len, by omega, hJ.wl, hJ.vals⟩ (by omega) hmr
      · rw [hseg2, seg_split c1.work (show low ≤ low + k by omega) (show low + k ≤ low + m by omega), hseg1, hseg0,
          msort_cat hle, seg_congr (l' := c1.work) (l := w0) fun i h1 _ => hrest1 i h1,
          ← seg_split w0 (show low ≤ low + k by omega) (show low + k ≤ low + m by omega)]
      · intro i hi
        rw [hp2.out i (Or.inr hi)]
        exact hrest1 i (by omega)
    · next hlt =>
      rw [post_pure]
      refine hcont k e1 c1 ⟨hrun1, by rw [hseg1, hseg0], fun i hi => by rw [hun1 i hi]; exact hrw i (by omega),
        by rw [hlen1]; exact hJ.len, by omega, hJ.wl, hJ.vals⟩ (by omega) (by omega)
  · next hrem =>
    rw [post_pure]
    have : remaining = 0 := by omega
    subst this
    rw [show low = n by omega] at hJ
    exact hJ

theorem powerSortImpl_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {n : Nat} {e : ε} {c : Core}
    (hv : Vals c.work 0 n) (hsz : c.size = 0) :
    ((powerSortImpl cmp smiMax (n : Int)) e c).Post (fun _ _ c' => seg c'.work 0 n = msort le (seg c.work 0 n)) := by
  have hl := hv.1
  unfold powerSortImpl
  rw [post_ite]
  split
  · rw [post_pure]
    have : n = 0 ∨ n = 1 := by omega
    rcases this with h | h
    · subst h
      simp [seg, msort]
    · subst h
      rw [seg_single (by omega), msort_single]
  · simp only [post_bind, post_getCore, post_setCore]
    have hJ0 : J le c.work n { c with runs := List.replicate 85 0, powers := List.replicate 85 0 } 0 0 := by
      refine ⟨⟨by simp, by simp only; omega, fun j hj => by simp only at hj; omega,
        fun j hj => by simp only at hj; omega, fun h => by simp only at h; omega, fun _ => rfl,
        fun h => by simp only at h; omega, fun j hj => by simp only at hj; omega⟩, by simp [seg, msort],
        fun _ _ => rfl, rfl, by omega, hl, hv⟩
    refine (mainLoop_post cmp smiMax hle hc n 0 n 0 e _ rfl (by omega) hJ0).mono ?_
    rintro _ e1 c1 hJ1
    rw [post_getSize]
    intro _
    refine (finalLoop_post cmp smiMax hle hc _ c1.size e1 c1 rfl hJ1).mono ?_
    rintro _ e3 c3 hJ3
    simp only [post_getSize, post_dcheck, post_runLen]
    intro _ h1 _ h2
    have hR := hJ3.runs
    have hf := hR.first (by omega)
    have hlen0 : rL c3 0 = (n : Int) := by
      simp only [rL]
      rw [show (2 * (0 : Int) + 1).toNat = 2 * 0 + 1 by omega] at h2
      exact h2
    have := hR.sorted 0 (by omega)
    rw [hf, hlen0, show ((0 : Int) + (n : Int)).toNat = n by omega, show (0 : Int).toNat = 0 by rfl] at this
    exact this

theorem sortCore_post (hle : TotalPreorder le) (hc : CmpOK le cmp) {n : Nat} {e : ε} {c : Core}
    (hv : Vals c.work 0 n) (hsz : c.size = 0) :
    ((sortCore cmp smiMax (n : Int)) e c).Post (fun _ _ c' => seg c'.work 0 n = msort le (seg c.work 0 n)) := by
  unfold sortCore
  rw [post_ite]
  split
  · exact binaryInsertionSort_post cmp hle hc (low := 0) (start := 0) (by have := hv.1; omega)
      (by simp [seg, Srt])
  · exact powerSortImpl_post cmp smiMax hle hc hv hsz

end

end ArraySort
