import ArraySort.MergeHigh

namespace ArraySort

open Torque

def Contig : List (Nat × Nat) → Nat → Nat → Prop
  | [], lo, hi => lo = hi
  | r :: rs, lo, hi => r.1 = lo ∧ 0 < r.2 ∧ Contig rs (lo + r.2) hi

theorem contig_append : ∀ (A B : List (Nat × Nat)) (lo hi : Nat),
    Contig (A ++ B) lo hi ↔ ∃ m, Contig A lo m ∧ Contig B m hi
  | [], B, lo, hi => by simp [Contig]
  | r :: A, B, lo, hi => by
    simp only [List.cons_append, Contig]
    rw [contig_append A B (lo + r.2) hi]
    constructor
    · rintro ⟨h1, h2, m, h3, h4⟩
      exact ⟨m, ⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨m, ⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, h2, m, h3, h4⟩

theorem contig_le : ∀ (A : List (Nat × Nat)) (lo hi : Nat), Contig A lo hi → lo ≤ hi
  | [], lo, hi, h => by simp only [Contig] at h; omega
  | r :: A, lo, hi, h => by
    obtain ⟨_, h2, h3⟩ := h
    have := contig_le A _ _ h3
    omega

def RunsRep (runs : List Int) (S : List (Nat × Nat)) : Prop :=
  ∀ j, j < S.length → runs.getD (2 * j) 0 = ((S.reverse.getD j (0, 0)).1 : Int) ∧
    runs.getD (2 * j + 1) 0 = ((S.reverse.getD j (0, 0)).2 : Int)

def PowRep (powers : List Int) (P : List Nat) : Prop :=
  ∀ j, j < P.length → powers.getD j 0 = ((P.reverse.getD j 0 : Nat) : Int)

theorem getD_set_ne {l : List Int} {i j : Nat} {v : Int} (h : i ≠ j) : (l.set i v).getD j 0 = l.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  rw [ite_eq_right h]

theorem getD_set_eq {l : List Int} {i : Nat} {v : Int} (h : i < l.length) : (l.set i v).getD i 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  simp [h]

theorem reverse_split (pre rest : List (Nat × Nat)) (x0 x1 : Nat × Nat) :
    (pre ++ x0 :: x1 :: rest).reverse = rest.reverse ++ x1 :: x0 :: pre.reverse := by
  simp [List.reverse_append, List.reverse_cons, List.append_assoc]

theorem reverse_split1 (pre rest : List (Nat × Nat)) (x : Nat × Nat) :
    (pre ++ x :: rest).reverse = rest.reverse ++ x :: pre.reverse := by
  simp [List.reverse_append, List.reverse_cons, List.append_assoc]

theorem getD_mid {A B : List (Nat × Nat)} {x : Nat × Nat} {j : Nat} :
    (A ++ x :: B).getD j (0, 0) =
      if j < A.length then A.getD j (0, 0) else if j = A.length then x else B.getD (j - A.length - 1) (0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases h1 : j < A.length
  · rw [List.getElem?_append_left h1, ite_eq_left h1]
  · rw [List.getElem?_append_right (by omega), ite_eq_right h1]
    by_cases h2 : j = A.length
    · subst h2
      simp
    · rw [ite_eq_right h2, show j - A.length = (j - A.length - 1) + 1 by omega]
      simp

section

variable {ε : Type} (cmp : Cmp ε) (smiMax : Nat)

theorem mergeAtTail_good {bA lA lB n : Nat} {c : Core} {e : ε} (hla : 0 < lA) (hlb : 0 < lB)
    (hn : bA + lA + lB ≤ n) (hv : Vals c.work 0 n) :
    ((mergeAtTail cmp smiMax (bA : Int) (lA : Int) ((bA + lA : Nat) : Int) (lB : Int)) e c).Good
      (fun _ _ c' => c'.runs = c.runs ∧ c'.powers = c.powers ∧ c'.size = c.size ∧
        PermOn c.work c'.work 0 n) := by
  have hl := hv.1
  unfold mergeAtTail
  simp only [good_bind, good_ld, good_jsAny, Core.get_work, Int.toNat_natCast]
  obtain ⟨v1, hv1⟩ := hv.2 (bA + lA) (by omega) (by omega)
  refine ⟨⟨by omega, by omega⟩, v1, hv1, ?_⟩
  refine (gallop_good_int cmp smiMax (a := .work) (key := v1) (isRight := true) (baseN := bA) (lengthN := lA)
    (hintN := 0) rfl rfl rfl (hv.mono (Nat.zero_le _) (by omega)) hla).mono ?_
  rintro k e2 c2 ⟨hc2, kN, hk, hkN⟩
  subst c2
  subst hk
  simp only [good_dcheck]
  refine ⟨by omega, ?_⟩
  rw [good_ite]
  split
  · exact ⟨rfl, rfl, rfl, PermOn.refl _ _ _⟩
  · simp only [good_bind, good_dcheck, good_ld, good_jsAny, Core.get_work]
    obtain ⟨v2, hv2⟩ := hv.2 (bA + lA - 1) (by omega) (by omega)
    refine ⟨by omega, ⟨by omega, by omega⟩, v2, ?_, ?_⟩
    · rw [show ((bA : Int) + (kN : Int) + ((lA : Int) - (kN : Int)) - 1).toNat = bA + lA - 1 by omega]
      exact hv2
    refine (gallop_good_int cmp smiMax (a := .work) (key := v2) (isRight := false) (baseN := bA + lA)
      (lengthN := lB) (hintN := lB - 1) rfl rfl (by omega) (hv.mono (Nat.zero_le _) (by omega))
      (by omega)).mono ?_
    rintro lb' e3 c3 ⟨hc3, lbN, hlb', hlbN⟩
    subst c3
    subst hlb'
    refine ⟨by omega, ?_⟩
    rw [good_ite]
    split
    · exact ⟨rfl, rfl, rfl, PermOn.refl _ _ _⟩
    · rw [show (bA : Int) + (kN : Int) = ((bA + kN : Nat) : Int) by omega,
        show (lA : Int) - (kN : Int) = ((lA - kN : Nat) : Int) by omega,
        show ((bA + lA : Nat) : Int) = ((bA + kN + (lA - kN) : Nat) : Int) by omega]
      have hv' : Vals c.work (bA + kN) (bA + kN + (lA - kN) + lbN) := hv.mono (Nat.zero_le _) (by omega)
      rw [good_ite]
      split
      · refine (mergeLow_good cmp smiMax (by omega) (by omega) hv').mono ?_
        rintro _ _ c' ⟨hp, h1, h2, h3⟩
        exact ⟨h1, h2, h3, hp.widen (Nat.zero_le _) (by omega) (by omega)⟩
      · refine (mergeHigh_good cmp smiMax (by omega) (by omega) hv').mono ?_
        rintro _ _ c' ⟨hp, h1, h2, h3⟩
        exact ⟨h1, h2, h3, hp.widen (Nat.zero_le _) (by omega) (by omega)⟩

def MergePost (pre rest : List (Nat × Nat)) (x0 x1 : Nat × Nat) (n hi : Nat) (c c' : Core) : Prop :=
  c'.size = (pre ++ (x1.1, x1.2 + x0.2) :: rest).length ∧
    RunsRep c'.runs (pre ++ (x1.1, x1.2 + x0.2) :: rest) ∧ c'.runs.length = 85 ∧ c'.powers = c.powers ∧
    PermOn c.work c'.work 0 n ∧ Contig (pre ++ (x1.1, x1.2 + x0.2) :: rest).reverse 0 hi

theorem mergeAt_good {pre rest : List (Nat × Nat)} {x0 x1 : Nat × Nat} {n hi : Nat} {c : Core} {e : ε}
    (ht : pre.length ≤ 1) (hsize : c.size = (pre ++ x0 :: x1 :: rest).length)
    (hruns : RunsRep c.runs (pre ++ x0 :: x1 :: rest)) (hrl : c.runs.length = 85)
    (hlen : (pre ++ x0 :: x1 :: rest).length ≤ 42)
    (hc : Contig (pre ++ x0 :: x1 :: rest).reverse 0 hi) (hhi : hi ≤ n) (hv : Vals c.work 0 n) :
    ((mergeAt cmp smiMax (rest.length : Int)) e c).Good
      (fun _ _ c' => MergePost pre rest x0 x1 n hi c c') := by
  rw [reverse_split] at hc
  obtain ⟨m, hc1, hc2⟩ := (contig_append _ _ _ _).1 hc
  simp only [Contig] at hc2
  obtain ⟨hx1b, hx1l, hx0b, hx0l, hpre⟩ := hc2
  have hn := contig_le _ _ _ hpre
  have hgetS : ∀ j, (pre ++ x0 :: x1 :: rest).reverse.getD j (0, 0) =
      (rest.reverse ++ x1 :: x0 :: pre.reverse).getD j (0, 0) := by
    intro j
    rw [reverse_split]
  have hr1 := hruns rest.length (by simp <;> omega)
  have hr0 := hruns (rest.length + 1) (by simp <;> omega)
  rw [hgetS, getD_mid, ite_eq_right (by simp), ite_eq_left (by simp)] at hr1
  rw [hgetS, getD_mid, ite_eq_right (by simp), ite_eq_right (by simp), List.length_reverse,
    show rest.length + 1 - rest.length - 1 = 0 by omega, List.getD_cons_zero] at hr0
  have hS : (pre ++ x0 :: x1 :: rest).length = pre.length + rest.length + 2 := by simp <;> omega
  unfold mergeAt
  simp only [good_bind, good_getSize, good_dcheck, good_runBase, good_runLen, good_setRunLen]
  rw [show (2 * (rest.length : Int)).toNat = 2 * rest.length by omega,
    show (2 * (rest.length : Int) + 1).toNat = 2 * rest.length + 1 by omega,
    show (2 * ((rest.length : Int) + 1)).toNat = 2 * (rest.length + 1) by omega,
    show (2 * ((rest.length : Int) + 1) + 1).toNat = 2 * (rest.length + 1) + 1 by omega,
    hr1.1, hr1.2, hr0.1, hr0.2]
  refine ⟨by omega, by omega, by omega, by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega, ⟨by omega, by omega⟩, ?_⟩
  rw [good_doIf]
  have hrl1 : (c.runs.set (2 * rest.length + 1) ((x1.2 : Int) + (x0.2 : Int))).length = 85 := by
    simp [hrl]
  have htail : ∀ (e2 : ε) (c2 : Core), c2.work = c.work → c2.powers = c.powers → c2.runs.length = 85 →
      RunsRep c2.runs (pre ++ (x1.1, x1.2 + x0.2) :: rest) →
      ((setSize (c.size - 1)) e2 c2).Good (fun _ e' c' => ((mergeAtTail cmp smiMax (x1.1 : Int) (x1.2 : Int)
        (x0.1 : Int) (x0.2 : Int)) e' c').Good (fun _ _ c' => MergePost pre rest x0 x1 n hi c c')) := by
    intro e2 c2 hw hp hl2 hrr
    rw [good_setSize, show (x0.1 : Int) = ((x1.1 + x1.2 : Nat) : Int) by omega]
    refine (mergeAtTail_good cmp smiMax (n := n) (c := { c2 with size := c.size - 1 }) (e := e2) hx1l hx0l
      (by omega)
      (by simp only; rw [hw]; exact hv)).mono ?_
    rintro _ _ c' ⟨h1, h2, h3, h4⟩
    refine ⟨by rw [h3]; simp only; rw [hsize]; simp; omega, by rw [h1]; exact hrr, by rw [h1]; exact hl2,
      by rw [h2]; exact hp, by simp only [hw] at h4; exact h4, ?_⟩
    rw [reverse_split1]
    exact (contig_append _ _ _ _).2 ⟨m, hc1, by simp only [Contig]; exact ⟨hx1b, by omega, by
      rw [show m + (x1.2 + x0.2) = m + x1.2 + x0.2 by omega]; exact hpre⟩⟩
  match pre, ht with
  | [], _ =>
    rw [ite_eq_right (by simp at hsize ⊢; omega)]
    refine htail _ _ rfl rfl hrl1 ?_
    intro j hj
    simp only [List.nil_append, List.length_cons] at hj
    have hrev : ((x1.1, x1.2 + x0.2) :: rest).reverse = rest.reverse ++ [(x1.1, x1.2 + x0.2)] := by simp
    simp only [List.nil_append]
    rw [hrev]
    by_cases hj1 : j < rest.length
    · have := hruns j (by simp <;> omega)
      rw [hgetS, getD_mid, ite_eq_left (by simpa using hj1)] at this
      rw [getD_set_ne (by omega), getD_set_ne (by omega), List.getD_eq_getElem?_getD (l := rest.reverse ++ _),
        List.getElem?_append_left (by simpa using hj1), ← List.getD_eq_getElem?_getD]
      exact this
    · have hj2 : j = rest.length := by omega
      subst hj2
      rw [getD_set_ne (by omega), getD_set_eq (by omega), hr1.1, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by simp)]
      simp
  | [p], _ =>
    rw [ite_eq_left (by simp at hsize ⊢; omega)]
    have hrp := hruns (rest.length + 2) (by simp)
    rw [hgetS, getD_mid, ite_eq_right (by simp), ite_eq_right (by simp)] at hrp
    simp only [List.length_reverse, show rest.length + 2 - rest.length - 1 = 1 by omega, List.reverse_singleton,
      List.getD_cons_succ, List.getD_cons_zero] at hrp
    simp only [good_bind, good_runBase, good_runLen, good_setRunBase, good_setRunLen, List.length_set]
    rw [show (2 * ((rest.length : Int) + 2)).toNat = 2 * rest.length + 4 by omega,
      show (2 * ((rest.length : Int) + 2) + 1).toNat = 2 * rest.length + 5 by omega,
      show (2 * ((rest.length : Int) + 1)).toNat = 2 * rest.length + 2 by omega,
      show (2 * ((rest.length : Int) + 1) + 1).toNat = 2 * rest.length + 3 by omega,
      getD_set_ne (by omega), getD_set_ne (by omega)]
    rw [show 2 * (rest.length + 2) = 2 * rest.length + 4 by omega,
      show 2 * rest.length + 4 + 1 = 2 * rest.length + 5 by omega] at hrp
    rw [hrp.1, hrp.2]
    have hL : ([p] ++ x0 :: x1 :: rest).length = rest.length + 3 := by simp <;> omega
    refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
    refine htail _ _ rfl rfl (by simp [hrl]) ?_
    intro j hj
    simp only [List.cons_append, List.nil_append, List.length_cons] at hj
    have hrev : ([p] ++ (x1.1, x1.2 + x0.2) :: rest).reverse = rest.reverse ++ [(x1.1, x1.2 + x0.2), p] := by simp
    rw [hrev]
    by_cases hj1 : j < rest.length
    · have := hruns j (by simp <;> omega)
      rw [hgetS, getD_mid, ite_eq_left (by simpa using hj1)] at this
      rw [getD_set_ne (by omega), getD_set_ne (by omega), getD_set_ne (by omega), getD_set_ne (by omega),
        getD_set_ne (by omega), getD_set_ne (by omega), List.getD_eq_getElem?_getD (l := rest.reverse ++ _),
        List.getElem?_append_left (by simpa using hj1), ← List.getD_eq_getElem?_getD]
      exact this
    · by_cases hj2 : j = rest.length
      · subst hj2
        rw [getD_set_ne (by omega), getD_set_ne (by omega), getD_set_ne (by omega), getD_set_ne (by omega),
          getD_set_ne (by omega), getD_set_eq (by first | omega | (simp <;> omega)), hr1.1,
          List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by simp)]
        simp
      · have hj3 : j = rest.length + 1 := by omega
        subst hj3
        rw [show 2 * (rest.length + 1) = 2 * rest.length + 2 by omega, getD_set_ne (by omega),
          getD_set_eq (by simp <;> omega), show 2 * rest.length + 2 + 1 = 2 * rest.length + 3 by omega,
          getD_set_eq (by simp <;> omega), List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp

end

end ArraySort
