import ArraySort.Power

namespace ArraySort

open Torque

structure SInv (n : Nat) (w0 : List (Option Val)) (c : Core) (S G : List (Nat × Nat)) (P : List Nat)
    (hi : Nat) : Prop where
  size : c.size = S.length
  runs : RunsRep c.runs S
  rlen : c.runs.length = 85
  pows : PowRep c.powers P
  plen : c.powers.length = 85
  contig : Contig S.reverse 0 hi
  hle : hi ≤ n
  perm : PermOn w0 c.work 0 n
  vals : Vals c.work 0 n
  glen : G.length = S.length
  pi : PI n G P
  bnd : Bnd n G

theorem getD_reverse_last (p0 : Nat) (ps : List Nat) : (p0 :: ps).reverse.getD ps.length 0 = p0 := by
  rw [List.reverse_cons, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem powRep_tail {powers : List Int} {p0 : Nat} {ps : List Nat} (h : PowRep powers (p0 :: ps)) :
    PowRep powers ps := by
  intro j hj
  have := h j (by simp; omega)
  rw [this, List.reverse_cons, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj),
    ← List.getD_eq_getElem?_getD]

theorem powRep_push {powers : List Int} {P : List Nat} {p : Nat} (h : PowRep powers P)
    (hl : P.length < powers.length) : PowRep (powers.set P.length (p : Int)) (p :: P) := by
  intro j hj
  simp only [List.length_cons] at hj
  rw [List.reverse_cons]
  by_cases hj1 : j < P.length
  · rw [getD_set_ne (by omega), h j hj1, List.getD_eq_getElem?_getD (l := P.reverse ++ [p]),
      List.getElem?_append_left (by simpa using hj1), ← List.getD_eq_getElem?_getD]
  · have : j = P.length := by omega
    subst this
    rw [getD_set_eq hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp

theorem runsRep_push {runs : List Int} {S : List (Nat × Nat)} {x : Nat × Nat} (h : RunsRep runs S)
    (hl : 2 * S.length + 1 < runs.length) :
    RunsRep ((runs.set (2 * S.length) (x.1 : Int)).set (2 * S.length + 1) (x.2 : Int)) (x :: S) := by
  intro j hj
  simp only [List.length_cons] at hj
  rw [List.reverse_cons]
  by_cases hj1 : j < S.length
  · rw [getD_set_ne (by omega), getD_set_ne (by omega), getD_set_ne (by omega), getD_set_ne (by omega),
      List.getD_eq_getElem?_getD (l := S.reverse ++ [x]), List.getElem?_append_left (by simpa using hj1),
      ← List.getD_eq_getElem?_getD]
    exact h j hj1
  · have : j = S.length := by omega
    subst this
    rw [getD_set_ne (by omega), getD_set_eq (by first | omega | (simp <;> omega)),
      getD_set_eq (by first | omega | (simp <;> omega)),
      List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp

theorem runsRep_top {runs : List Int} {x : Nat × Nat} {S : List (Nat × Nat)} (h : RunsRep runs (x :: S)) :
    runs.getD (2 * S.length) 0 = (x.1 : Int) ∧ runs.getD (2 * S.length + 1) 0 = (x.2 : Int) := by
  have := h S.length (by simp)
  rw [List.reverse_cons, getD_mid, ite_eq_right (by simp), ite_eq_left (by simp)] at this
  exact this

theorem contig_top {x : Nat × Nat} {S : List (Nat × Nat)} {hi : Nat} (h : Contig (x :: S).reverse 0 hi) :
    0 < x.2 ∧ x.1 + x.2 = hi ∧ Contig S.reverse 0 x.1 := by
  rw [List.reverse_cons] at h
  obtain ⟨m, h1, h2⟩ := (contig_append _ _ _ _).1 h
  simp only [Contig] at h2
  obtain ⟨e1, e2, e3⟩ := h2
  subst e1
  exact ⟨e2, e3, h1⟩

theorem contig_push {x : Nat × Nat} {S : List (Nat × Nat)} {lo : Nat} (h : Contig S.reverse 0 lo)
    (h1 : x.1 = lo) (h2 : 0 < x.2) : Contig (x :: S).reverse 0 (lo + x.2) := by
  rw [List.reverse_cons]
  exact (contig_append _ _ _ _).2 ⟨lo, h, h1, h2, rfl⟩

section

variable {ε : Type} (cmp : Cmp ε) (smiMax : Nat)

theorem mergeCollapse_good {n : Nat} {w0 : List (Option Val)} (hn : 0 < n) (hn2 : n < 2 ^ 31)
    {hi lmR m p : Nat} (hm : lmR + 2 ≤ m) (hm2 : m < 2 * n) (hp : p = pw n lmR m) :
    ∀ (d : Nat) (S G : List (Nat × Nat)) (P : List Nat) (e : ε) (c : Core), S.length = d →
      SInv n w0 c S G P hi → S ≠ [] → (G.head?.map Prod.snd) = some lmR →
      ((mergeCollapse cmp smiMax (p : Int) (S.length : Int)) e c).Good
        (fun ss _ c' => ∃ S' G' P', SInv n w0 c' S' G' P' hi ∧ ss = (S'.length : Int) ∧ S' ≠ [] ∧
          (G'.head?.map Prod.snd) = some lmR ∧ (∀ p0, P'.head? = some p0 → p0 < p))
  | d, S, G, P, e, c, hd, hs, hne, hg => by
    rw [mergeCollapse]
    match S, G, P, hs, hne, hg with
    | [x], [g], [], hs, _, hg =>
      rw [dite_eq_right (by simp)]
      exact ⟨[x], [g], [], hs, rfl, by simp, hg, fun _ h => by simp at h⟩
    | x0 :: x1 :: rest, g0 :: g1 :: gs, p0 :: ps, hs, _, hg =>
      have hL : (x0 :: x1 :: rest).length = rest.length + 2 := by simp
      rw [dite_eq_left (by simp; omega)]
      simp only [good_bind, good_getPower]
      have hPl : ps.length = rest.length := by
        have := hs.glen; have := pi_length _ _ (by simp) hs.pi; simp at *; omega
      have hP := hs.pows (rest.length) (by simp; omega)
      rw [show (p0 :: ps).reverse.getD rest.length 0 = p0 by rw [← hPl]; exact getD_reverse_last p0 ps] at hP
      have hsz := pi_size (by simp) hs.pi (pi_head_le hs.pi)
      rw [hs.glen] at hsz
      simp only [List.length_cons] at hsz
      rw [show (((x0 :: x1 :: rest).length : Nat) : Int) - 2 = ((rest.length : Nat) : Int) by simp; omega,
        Int.toNat_natCast, hP]
      have hplen := hs.plen
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [good_ite]
      split
      · next hlt =>
        have hsz := pi_size (by simp) hs.pi (pi_head_le hs.pi)
        rw [hs.glen] at hsz
        refine good_bind_of (mergeAt_good cmp smiMax (pre := []) (rest := rest) (x0 := x0) (x1 := x1) (n := n)
          (e := e) (by simp) (by rw [hs.size]; rfl) hs.runs hs.rlen (by simp; omega) hs.contig hs.hle
          hs.vals) ?_
        rintro _ e2 c2 ⟨h1, h2, h3, h4, h5, h6⟩
        simp only [List.nil_append, List.length_cons] at h1 h2 h6
        simp only [good_bind, good_getSize]
        refine ⟨by omega, ?_⟩
        rw [h1, dite_eq_left (by simp; omega)]
        obtain ⟨hpi, hbnd⟩ := pi_merge hn hn2 hs.pi hs.bnd
        have hp2 := hs.perm.trans h5
        have hs' : SInv n w0 c2 ((x1.1, x1.2 + x0.2) :: rest) ((g1.1, g0.2) :: gs) ps hi :=
          ⟨by simp [h1], h2, h3, by rw [h4]; exact powRep_tail hs.pows, by rw [h4]; exact hs.plen, h6, hs.hle,
            hp2, Vals.of_permOn h5 hs.vals, by have := hs.glen; simp at this ⊢; omega, hpi, hbnd⟩
        have := mergeCollapse_good hn hn2 hm hm2 hp (rest.length + 1) ((x1.1, x1.2 + x0.2) :: rest)
          ((g1.1, g0.2) :: gs) ps e2 c2 (by simp) hs' (by simp) (by simpa using hg)
        rw [show ((rest.length + 1 : Nat) : Int) = (((x1.1, x1.2 + x0.2) :: rest).length : Int) by simp]
        exact this
      · next hge =>
        refine ⟨_, _, _, hs, rfl, by simp, hg, fun p1 hp1 => ?_⟩
        simp only [List.head?_cons, Option.some.injEq] at hp1
        subst hp1
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hg
        have := pi_strict hn hn2 (m := m) hs.pi hs.bnd (by rw [hg]; exact hm) hm2 (by rw [hg, ← hp]; omega)
        rw [hg, ← hp] at this
        exact this
    | [], _, _, _, hne, _ => exact absurd rfl hne

theorem pushRun_good {S : List (Nat × Nat)} {low cur : Nat} {e : ε} {c : Core} (hs : c.size = S.length)
    (hrl : c.runs.length = 85) (hlen : S.length ≤ 41) :
    ((pushRun (low : Int) (cur : Int)) e c).Good (fun _ _ c' =>
      c' = { c with runs := (c.runs.set (2 * S.length) (low : Int)).set (2 * S.length + 1) (cur : Int), size := S.length + 1 }) := by
  unfold pushRun
  simp only [good_bind, good_getSize, good_dcheck, good_setRunBase, good_setRunLen, good_setSize,
    List.length_set, hs, hrl, kMaxMergePending]
  refine ⟨by omega, by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
  rw [show (2 * (S.length : Int)).toNat = 2 * S.length by omega,
    show (2 * (S.length : Int) + 1).toNat = 2 * S.length + 1 by omega]

theorem collapseAndPush_good {n : Nat} {w0 : List (Option Val)} (hn : 0 < n) (hn2 : n < 2 ^ 31)
    {S G : List (Nat × Nat)} {P : List Nat} {low cur : Nat} {e : ε} {c : Core} (hs : SInv n w0 c S G P low)
    (htop : ∀ x, S.head? = some x → G.head? = some (2 * x.1 + x.2, 2 * x.1 + x.2)) (hcur : 0 < cur)
    (hle : low + cur ≤ n) :
    ((collapseAndPush cmp smiMax (n : Int) (low : Int) (cur : Int)) e c).Good (fun _ _ c' =>
      ∃ S' G' P', SInv n w0 c' ((low, cur) :: S') ((2 * low + cur, 2 * low + cur) :: G') P' (low + cur)) := by
  unfold collapseAndPush
  simp only [good_bind, good_getSize]
  refine ⟨by rw [hs.size]; omega, ?_⟩
  rw [good_ite]
  match S, G, P, hs, htop with
  | [], [], [], hs, _ =>
    rw [ite_eq_left (by rw [hs.size]; rfl)]
    refine (pushRun_good (S := []) hs.size hs.rlen (by simp)).mono ?_
    rintro _ _ c' rfl
    have hc0 : low = 0 := by have := hs.contig; simp [Contig] at this; omega
    refine ⟨[], [], [], {
      size := rfl
      runs := runsRep_push hs.runs (by rw [hs.rlen]; simp)
      rlen := by simp [hs.rlen]
      pows := fun j hj => by simp at hj
      plen := hs.plen
      contig := contig_push hs.contig (x := (low, cur)) (by simp) hcur
      hle := hle
      perm := hs.perm
      vals := hs.vals
      glen := rfl
      pi := trivial
      bnd := ?_ }⟩
    intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    simp only
    omega
  | _ :: _, [], _, hs, _ => exact absurd hs.glen (by simp)
  | [], _ :: _, _, hs, _ => exact absurd hs.glen (by simp)
  | [], [], _ :: _, hs, _ => exact absurd hs.pi (by simp [PI])
  | x :: S0, g :: G0, P, hs, htop =>
    rw [ite_eq_right (by rw [hs.size]; simp; omega)]
    have hg := htop x rfl
    simp only [List.head?_cons, Option.some.injEq] at hg
    subst hg
    obtain ⟨hx2, hx12, hc0⟩ := contig_top hs.contig
    have hrt := runsRep_top hs.runs
    have hsz := pi_size (by simp) hs.pi (pi_head_le hs.pi)
    have hglen := hs.glen
    simp only [List.length_cons] at hsz hglen
    simp only [good_bind, good_runBase, good_runLen, hs.size, hs.rlen]
    rw [show (2 * (((x :: S0).length : Nat) - 1 : Int)).toNat = 2 * S0.length by simp; omega,
      show (2 * (((x :: S0).length : Nat) - 1 : Int) + 1).toNat = 2 * S0.length + 1 by simp; omega,
      hrt.1, hrt.2]
    refine ⟨⟨by simp; omega, by simp; omega⟩, ⟨by simp; omega, by simp; omega⟩, ?_⟩
    unfold nodePower
    simp only [good_bind, good_dcheck, good_pure]
    refine ⟨by omega, ⟨by omega, by omega⟩, by omega, ?_⟩
    rw [nodePowerValue_eq]
    have hlm : 2 * x.1 + x.2 + 2 ≤ 2 * x.1 + x.2 + x.2 + cur := by omega
    have hmn : 2 * x.1 + x.2 + x.2 + cur < 2 * n := by omega
    have hcol := mergeCollapse_good cmp smiMax (w0 := w0) (hi := low) hn hn2 hlm hmn rfl (x :: S0).length
      (x :: S0) ((2 * x.1 + x.2, 2 * x.1 + x.2) :: G0) P e c rfl hs (by simp) (by simp)
    refine hcol.mono ?_
    rintro ss e2 c2 ⟨S', G', P', hs', hss, hne, hgl, hhd⟩
    subst hss
    match S', G', P', hs', hne, hgl, hhd with
    | y :: S1, h :: G1, P1, hs', _, hgl, hhd =>
      have hsz' := pi_size (by simp) hs'.pi (pi_head_le hs'.pi)
      have hpl := (pi_length _ _ (by simp) hs'.pi).1
      have hgl2 := hs'.glen
      simp only [List.length_cons] at hsz' hpl hgl2
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hgl
      have hplen := hs'.plen
      have hyl : (y :: S1).length = S1.length + 1 := rfl
      have hP1 : P1.length = S1.length := by omega
      refine Res.Good.mono (Q := fun _ e3 c3 => e3 = e2 ∧ c3 = c2) ?_ ?_
      · rintro _ e3 c3 ⟨rfl, rfl⟩
        simp only [good_setPower]
        rw [show ((((y :: S1).length : Nat) : Int) - 1).toNat = P1.length by rw [hyl]; omega]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        refine (pushRun_good (S := y :: S1) (by simp only; rw [hs'.size]) (by simp only; rw [hs'.rlen])
          (by simp; omega)).mono ?_
        rintro _ _ c4 rfl
        have hm' : 2 * low + cur = 2 * x.1 + x.2 + x.2 + cur := by omega
        obtain ⟨hpi, hbnd⟩ := pi_push (m := 2 * low + cur) hn hn2 hs'.pi hs'.bnd (by rw [hgl]; omega) (by omega)
          (fun p0 hp0 => by rw [hgl, hm']; exact hhd p0 hp0)
        rw [hgl, hm'] at hpi
        rw [hm'] at hbnd
        refine ⟨y :: S1, h :: G1, pw n (2 * x.1 + x.2) (2 * x.1 + x.2 + x.2 + cur) :: P1, {
          size := by simp
          runs := runsRep_push hs'.runs (by rw [hs'.rlen]; simp; omega)
          rlen := by simp [hs'.rlen]
          pows := powRep_push hs'.pows (by omega)
          plen := by simp [hplen]
          contig := contig_push hs'.contig (x := (low, cur)) rfl hcur
          hle := hle
          perm := hs'.perm
          vals := hs'.vals
          glen := by simp; omega
          pi := ?_
          bnd := ?_ }⟩
        · rw [hm']
          exact hpi
        · rw [hm']
          exact hbnd
      · rw [good_doIf]
        split
        · next h2 =>
          simp only [good_bind, good_getPower, good_dcheck]
          match P1, hhd, hpl with
          | q :: Q, hhd, hpl =>
            have hq := hs'.pows Q.length (by simp)
            rw [getD_reverse_last] at hq
            have hQ : Q.length + 1 = S1.length := by simp at hP1; omega
            rw [show ((((y :: S1).length : Nat) : Int) - 2).toNat = Q.length by rw [hyl]; omega, hq]
            refine ⟨⟨by omega, by omega⟩, by have := hhd q rfl; omega, ?_⟩
            simp
          | [], _, hpl => exact absurd h2 (by simp at hP1; rw [hyl]; omega)
        · exact ⟨rfl, rfl⟩
    | [], _, _, _, hne, _, _ => exact absurd rfl hne
    | _ :: _, [], _, hs', _, _, _ => exact absurd hs'.glen (by simp)

theorem SInv.withWork {n : Nat} {w0 : List (Option Val)} {c : Core} {S G : List (Nat × Nat)} {P : List Nat}
    {hi : Nat} {w : List (Option Val)} (hs : SInv n w0 c S G P hi) (hp : PermOn c.work w 0 n) :
    SInv n w0 { c with work := w } S G P hi :=
  { size := hs.size, runs := hs.runs, rlen := hs.rlen, pows := hs.pows, plen := hs.plen,
    contig := hs.contig, hle := hs.hle, perm := hs.perm.trans hp, vals := Vals.of_permOn hp hs.vals,
    glen := hs.glen, pi := hs.pi, bnd := hs.bnd }

theorem mainLoop_good {n : Nat} {w0 : List (Option Val)} (hn : 2 ≤ n) (hn2 : n < 2 ^ 31)
    {mrStep mrRem mrThr : Int} (hmr : (n : Int) < 64 ∨ (32 ≤ mrStep ∧ mrStep < 64)) (hms : 1 ≤ mrStep) :
    ∀ (remaining low : Nat) (acc : Int) (S G : List (Nat × Nat)) (P : List Nat) (e : ε) (c : Core),
      low + remaining = n → SInv n w0 c S G P low →
      (∀ x, S.head? = some x → G.head? = some (2 * x.1 + x.2, 2 * x.1 + x.2)) →
      ((mainLoop cmp smiMax (n : Int) mrStep mrRem mrThr (low : Int) (remaining : Int) acc) e c).Good
        (fun _ _ c' => ∃ S G P, SInv n w0 c' S G P n)
  | 0, low, acc, S, G, P, e, c, h, hs, _ => by
    rw [mainLoop, dite_eq_right (by omega)]
    exact ⟨S, G, P, by rw [show n = low by omega] at hs ⊢; exact hs⟩
  | remaining + 1, low, acc, S, G, P, e, c, h, hs, htop => by
    rw [mainLoop, dite_eq_left (by omega)]
    simp only [good_bind, good_dcheck]
    refine ⟨by split <;> omega, ?_⟩
    have hmin1 : 1 ≤ (if mrThr ≤ acc + mrRem then mrStep + 1 else mrStep) := by split <;> omega
    generalize (if mrThr ≤ acc + mrRem then mrStep + 1 else mrStep) = minRun at hmin1 ⊢
    rw [show (low : Int) + ((remaining + 1 : Nat) : Int) = ((low + (remaining + 1) : Nat) : Int) by omega]
    refine (countAndMakeRun_good cmp (lowArg := low) (high := low + (remaining + 1)) (e := e) (c := c)
      (by omega) (hs.vals.mono (Nat.zero_le _) (by omega))).mono ?_
    rintro r e1 c1 ⟨hc1, hp1, k, hk, hk1, hk2⟩
    subst hk
    have hs1 : SInv n w0 c1 S G P low := by
      rw [hc1]
      exact hs.withWork (hp1.widen (Nat.zero_le _) (by omega) (by omega))
    refine Res.Good.mono (Q := fun cur e2 c2 => ∃ curN : Nat, cur = (curN : Int) ∧ 1 ≤ curN ∧
      curN ≤ remaining + 1 ∧ SInv n w0 c2 S G P low) ?_ ?_
    · rintro cur e2 c2 ⟨curN, rfl, hc1', hc2', hs2⟩
      refine (collapseAndPush_good cmp smiMax (e := e2) (by omega) hn2 hs2 htop hc1' (by omega)).mono ?_
      rintro _ e3 c3 ⟨S', G', P', hs3⟩
      rw [dite_eq_left (by omega), show (low : Int) + (curN : Int) = ((low + curN : Nat) : Int) by omega,
        show ((remaining + 1 : Nat) : Int) - (curN : Int) = ((remaining + 1 - curN : Nat) : Int) by omega]
      exact mainLoop_good hn hn2 hmr hms (remaining + 1 - curN) (low + curN) _ _ _ _ e3 c3 (by omega) hs3
        (fun x hx => by simp only [List.head?_cons, Option.some.injEq] at hx; subst hx; rfl)
    · rw [extendRun, good_ite]
      split
      · next hlt =>
        simp only [good_bind, good_pure]
        have hmin : ∃ f : Nat, min minRun ((remaining + 1 : Nat) : Int) = (f : Int) ∧ k ≤ f ∧ 1 ≤ f ∧
            f ≤ remaining + 1 :=
          ⟨(min minRun ((remaining + 1 : Nat) : Int)).toNat, by omega, by omega, by omega, by omega⟩
        obtain ⟨f, hf, hf1, hf2, hf3⟩ := hmin
        rw [hf, show (low : Int) + (k : Int) = ((low + k : Nat) : Int) by omega,
          show (low : Int) + (f : Int) = ((low + f : Nat) : Int) by omega]
        refine (binaryInsertionSort_good cmp (low := low) (start := low + k) (high := low + f) (e := e1) (c := c1)
          (by omega) (by omega) (hs1.vals.mono (Nat.zero_le _) (by omega))).mono ?_
        rintro _ e2 c2 ⟨hc2, hp2⟩
        refine ⟨f, rfl, hf2, hf3, ?_⟩
        rw [hc2]
        exact hs1.withWork (hp2.widen (Nat.zero_le _) (by omega) (by omega))
      · exact ⟨k, rfl, hk1, by omega, hs1⟩
termination_by remaining => remaining

theorem mrLoop_spec : ∀ (m : Nat) (k : Int), ((m : Int) < 64 → (mrLoop m k).1 = m) ∧
    (32 ≤ m → 32 ≤ (mrLoop m k).1 ∧ (mrLoop m k).1 < 64)
  | m, k => by
    by_cases h : 64 ≤ m
    · rw [mrLoop, dite_eq_left (by omega)]
      have := mrLoop_spec (m / 2) (2 * k + 1)
      rw [show (m : Int) / 2 = ((m / 2 : Nat) : Int) by omega]
      exact ⟨fun h' => by omega, fun _ => this.2 (by omega)⟩
    · rw [mrLoop, dite_eq_right (by omega)]
      exact ⟨fun _ => rfl, fun h' => ⟨by simp; omega, by simp; omega⟩⟩
termination_by m => m

theorem finalLoop_good {n : Nat} {w0 : List (Option Val)} :
    ∀ (d : Nat) (S : List (Nat × Nat)) (e : ε) (c : Core), S.length = d → c.size = S.length →
      RunsRep c.runs S → c.runs.length = 85 → S.length ≤ 42 → Contig S.reverse 0 n →
      PermOn w0 c.work 0 n → Vals c.work 0 n →
      ((finalLoop cmp smiMax (S.length : Int)) e c).Good (fun _ _ c' => ∃ S' : List (Nat × Nat),
        S'.length ≤ 1 ∧ c'.size = S'.length ∧ RunsRep c'.runs S' ∧ c'.runs.length = 85 ∧ Contig S'.reverse 0 n ∧
        PermOn w0 c'.work 0 n) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro S e c hd hsz hr hrl hlen hc hp hv
    rw [finalLoop]
    match S, hsz, hr, hlen, hc with
    | [], hsz, hr, _, hc =>
      rw [dite_eq_right (by simp)]
      exact ⟨[], by simp, hsz, hr, hrl, hc, hp⟩
    | [x], hsz, hr, _, hc =>
      rw [dite_eq_right (by simp)]
      exact ⟨[x], by simp, hsz, hr, hrl, hc, hp⟩
    | x0 :: x1 :: rest, hsz, hr, hlen, hc =>
      rw [dite_eq_left (by simp; omega)]
      have hL : (x0 :: x1 :: rest).length = rest.length + 2 := by simp
      have hcont : ∀ (pre rest' : List (Nat × Nat)) (y0 y1 : Nat × Nat),
          pre ++ y0 :: y1 :: rest' = x0 :: x1 :: rest → pre.length ≤ 1 → ∀ e2,
          ((mergeAt cmp smiMax (rest'.length : Int) >>= fun _ => getSize >>= fun s' =>
            if _h2 : s' < ((x0 :: x1 :: rest).length : Int) then finalLoop cmp smiMax s' else ub) e2 c).Good
            (fun _ _ c' => ∃ S' : List (Nat × Nat), S'.length ≤ 1 ∧ c'.size = S'.length ∧ RunsRep c'.runs S' ∧
              c'.runs.length = 85 ∧ Contig S'.reverse 0 n ∧ PermOn w0 c'.work 0 n) := by
        intro pre rest' y0 y1 heq hpre e2
        rw [← heq] at hsz hr hc hlen
        refine good_bind_of (mergeAt_good cmp smiMax (e := e2) hpre hsz hr hrl hlen hc (Nat.le_refl n) hv) ?_
        rintro _ e3 c3 ⟨h1, h2, h3, _, h5, h6⟩
        simp only [good_bind, good_getSize]
        have hl' : (pre ++ (y1.1, y1.2 + y0.2) :: rest').length + 1 = (x0 :: x1 :: rest).length := by
          rw [← heq]; simp; omega
        refine ⟨by omega, ?_⟩
        rw [h1, dite_eq_left (by omega)]
        exact ih _ (by rw [← hd, ← hl']; omega) _ e3 c3 rfl h1 h2 h3 (by rw [← heq] at hl'; omega) h6
          (hp.trans h5) (Vals.of_permOn h5 hv)
      rw [good_bind]
      refine Res.Good.mono (Q := fun r e2 c2 => c2 = c ∧ (r = (rest.length : Int) ∨
        (r = (rest.length : Int) - 1 ∧ 0 < rest.length ∧ ∃ x2 rest', rest = x2 :: rest'))) ?_ ?_
      · rintro r e2 c2 ⟨rfl, hr'⟩
        rcases hr' with rfl | ⟨rfl, _, x2, rest', rfl⟩
        · exact hcont [] rest x0 x1 rfl (by simp) e2
        · rw [show ((x2 :: rest').length : Int) - 1 = (rest'.length : Int) by simp]
          exact hcont [x0] rest' x1 x2 rfl (by simp) e2
      · rw [finalPick, good_ite]
        split
        · next h0 =>
          match rest, hr, h0 with
          | x2 :: rest', hr, _ =>
            simp only [good_bind, good_runLen, good_pure]
            have hl3 : (x0 :: x1 :: x2 :: rest').length = rest'.length + 3 := by simp
            have hr2 := hr rest'.length (by omega)
            have hr0 := hr (rest'.length + 2) (by omega)
            rw [show (x0 :: x1 :: x2 :: rest').reverse = rest'.reverse ++ x2 :: x1 :: x0 :: [] by simp,
              getD_mid, ite_eq_right (by simp), ite_eq_left (by simp)] at hr2
            rw [show (x0 :: x1 :: x2 :: rest').reverse = rest'.reverse ++ x2 :: x1 :: x0 :: [] by simp,
              getD_mid, ite_eq_right (by simp), ite_eq_right (by simp),
              show rest'.length + 2 - rest'.reverse.length - 1 = 1 by simp] at hr0
            simp only [List.getD_cons_succ, List.getD_cons_zero] at hr0
            rw [show (2 * (((x0 :: x1 :: x2 :: rest').length : Int) - 2 - 1) + 1).toNat = 2 * rest'.length + 1 by
                simp; omega,
              show (2 * (((x0 :: x1 :: x2 :: rest').length : Int) - 2 + 1) + 1).toNat =
                2 * (rest'.length + 2) + 1 by simp; omega, hr2.2, hr0.2]
            refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
            try simp only [true_and]
            split
            · right
              exact ⟨by simp; omega, by simp, x2, rest', rfl⟩
            · left
              simp only [List.length_cons]
              omega
          | [], _, h0 => exact absurd h0 (by simp)
        · exact ⟨rfl, Or.inl (by simp; omega)⟩

theorem powerSortImpl_good {n : Nat} (hn : 2 ≤ n) (hn2 : n < 2 ^ 31) {e : ε} {c : Core}
    (hv : Vals c.work 0 n) (hsz : c.size = 0) :
    ((powerSortImpl cmp smiMax (n : Int)) e c).Good (fun _ _ c' => PermOn c.work c'.work 0 n) := by
  unfold powerSortImpl
  rw [ite_eq_right (by omega)]
  simp only [good_bind, good_getCore, good_setCore]
  have hmr := mrLoop_spec n 0
  have hinv0 : SInv n c.work { c with runs := List.replicate 85 0, powers := List.replicate 85 0 } [] [] [] 0 :=
    { size := hsz, runs := fun j hj => by simp at hj, rlen := by simp, pows := fun j hj => by simp at hj,
      plen := by simp, contig := rfl, hle := Nat.zero_le _, perm := PermOn.refl _ _ _, vals := hv,
      glen := rfl, pi := trivial, bnd := fun _ h => by simp at h }
  refine (mainLoop_good cmp smiMax hn hn2 (mrStep := (mrLoop n 0).1) (by
      by_cases h : (n : Int) < 64
      · exact Or.inl h
      · exact Or.inr (hmr.2 (by omega))) (by
      by_cases h : (n : Int) < 64
      · rw [hmr.1 h]; omega
      · have := hmr.2 (by omega); omega) n 0 0 [] [] [] e _ (by omega) hinv0
      (fun x h => by simp at h)).mono ?_
  rintro _ e2 c2 ⟨S, G, P, hs⟩
  simp only [good_getSize, good_dcheck, good_runLen]
  refine ⟨by rw [hs.size]; omega, ?_⟩
  rw [hs.size]
  have hsz32 : S.length ≤ 42 := by
    cases S with
    | nil => simp
    | cons x S0 =>
      have := pi_size (by intro h; have := hs.glen; rw [h] at this; simp at this) hs.pi (pi_head_le hs.pi)
      rw [hs.glen] at this
      omega
  refine (finalLoop_good cmp smiMax _ S e2 c2 rfl hs.size hs.runs hs.rlen hsz32 (by
      have := hs.contig; exact this) hs.perm hs.vals).mono ?_
  rintro _ e3 c3 ⟨S', hS1, hsz', hr', hrl', hc', hp'⟩
  match S', hS1, hc', hr', hsz' with
  | [], _, hc', _, _ => exact absurd hc' (by simp [Contig]; omega)
  | [x], _, hc', hr', hsz' =>
    simp only [List.reverse_singleton, Contig] at hc'
    obtain ⟨hx1, hx2, hx3⟩ := hc'
    have := hr' 0 (by simp)
    simp only [List.reverse_singleton, List.getD_cons_zero, Nat.mul_zero, Nat.zero_add] at this
    simp only [hsz', List.length_singleton, Int.reduceMul, Int.reduceAdd]
    refine ⟨by omega, by simp, ⟨by omega, by omega⟩, ?_, hp'⟩
    show c3.runs.getD 1 0 = (n : Int)
    rw [this.2]
    omega

theorem sortCore_good {n : Nat} (hn : n ≤ smiMax) (hsm : smiMax < 2 ^ 31) {e : ε} {c : Core}
    (hv : Vals c.work 0 n) (hsz : c.size = 0) :
    ((sortCore cmp smiMax (n : Int)) e c).Good (fun _ _ c' => PermOn c.work c'.work 0 n) := by
  unfold sortCore
  rw [good_ite]
  split
  · exact (binaryInsertionSort_good cmp (low := 0) (start := 0) (high := n) (Nat.le_refl _) (Nat.zero_le _)
      hv).mono fun _ _ _ h => h.2
  · exact powerSortImpl_good cmp smiMax (by simp [kMaxBinaryInsertionSortLength] at *; omega) (by omega) hv hsz

end

end ArraySort
