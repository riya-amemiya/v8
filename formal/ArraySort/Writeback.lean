import ArraySort.Compact

namespace ArraySort

open Torque

def ValOK (cfg : Cfg) : Acc → Val → Prop
  | .smi, v => v.isSmi = true
  | .dbl, v => (∃ k, v = .num k) ∨ (v = .undef ∧ cfg.ud = true)
  | _, _ => True

def Shape (r r' : Recv) : Prop :=
  r'.arr.fast = r.arr.fast ∧ r'.arr.kind = r.arr.kind ∧ r'.arr.cow = r.arr.cow ∧
    r'.arr.store.length = r.arr.store.length

theorem Shape.refl (r : Recv) : Shape r r := ⟨rfl, rfl, rfl, rfl⟩

theorem Shape.trans {r1 r2 r3 : Recv} (h1 : Shape r1 r2) (h2 : Shape r2 r3) : Shape r1 r3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

theorem fastWrite_good {b : Bool} {e : Ext} {c : Core} {i : Nat} {x : Option Val}
    (hi : i < e.recv.arr.store.length) (hc : e.recv.arr.cow = false) :
    (fastWrite b e c i x).Good (fun _ e' c' => c' = c ∧ e'.log = e.log ∧ Shape e.recv e'.recv) := by
  simp [fastWrite, hi, hc, Shape, putElem]

theorem storeTo_good {cfg : Cfg} {env : Env} {acc : Acc} {i : Nat} {v : Val} {e : Ext} {c : Core}
    (hv : ValOK cfg acc v) (hf : acc = .generic ∨ (i < e.recv.arr.store.length ∧ e.recv.arr.cow = false)) :
    ((storeTo cfg env acc i v) e c).Good (fun _ e' c' => c' = c ∧ e'.log = e.log ++ [.store i v] ∧
      (acc = .generic ∨ Shape e.recv e'.recv)) := by
  unfold storeTo
  cases acc with
  | generic =>
    simp only
    split
    · simp [Ext.step]
    · simp
  | smi =>
    obtain hf | ⟨hi, hc⟩ := hf
    · cases hf
    simp only [ValOK] at hv
    simp only [hv, ite_true]
    exact (fastWrite_good (e := { e with log := e.log ++ [.store i v] }) hi hc).mono
      fun _ e' c' ⟨h1, h2, h3⟩ => ⟨h1, h2, Or.inr h3⟩
  | obj =>
    obtain hf | ⟨hi, hc⟩ := hf
    · cases hf
    exact (fastWrite_good (e := { e with log := e.log ++ [.store i v] }) hi hc).mono
      fun _ e' c' ⟨h1, h2, h3⟩ => ⟨h1, h2, Or.inr h3⟩
  | dbl =>
    obtain hf | ⟨hi, hc⟩ := hf
    · cases hf
    have hne : e.recv.arr.store ≠ [] := by
      intro h
      rw [h] at hi
      simp at hi
    simp only [hne, ite_false]
    simp only [ValOK] at hv
    rcases hv with ⟨k, rfl⟩ | ⟨rfl, hu⟩
    · exact (fastWrite_good (e := { e with log := e.log ++ [.store i (.num k)] }) hi hc).mono
        fun _ e' c' ⟨h1, h2, h3⟩ => ⟨h1, h2, Or.inr h3⟩
    · simp only [hu, ite_true]
      exact (fastWrite_good (e := { e with log := e.log ++ [.store i .undef] }) hi hc).mono
        fun _ e' c' ⟨h1, h2, h3⟩ => ⟨h1, h2, Or.inr h3⟩

theorem deleteAt_good {env : Env} {acc : Acc} {i : Nat} {e : Ext} {c : Core}
    (hf : acc = .generic ∨ (i < e.recv.arr.store.length ∧ e.recv.arr.cow = false ∧
      e.recv.arr.kind.isHoley = true)) :
    ((deleteAt env acc i) e c).Good (fun _ e' c' => c' = c ∧ e'.log = e.log ++ [.del i] ∧
      (acc = .generic ∨ Shape e.recv e'.recv)) := by
  unfold deleteAt
  cases acc with
  | generic =>
    simp only
    split
    · simp [Ext.step]
    · simp
  | dbl =>
    obtain hf | ⟨hi, hc, hh⟩ := hf
    · cases hf
    have hne : e.recv.arr.store ≠ [] := by
      intro h
      rw [h] at hi
      simp at hi
    simp only [hh, hne, ite_true, ite_false]
    exact (fastWrite_good (e := { e with log := e.log ++ [.del i] }) hi hc).mono
      fun _ e' c' ⟨h1, h2, h3⟩ => ⟨h1, h2, Or.inr h3⟩
  | smi =>
    obtain hf | ⟨hi, hc, hh⟩ := hf
    · cases hf
    simp only [hh, ite_true]
    exact (fastWrite_good (e := { e with log := e.log ++ [.del i] }) hi hc).mono
      fun _ e' c' ⟨h1, h2, h3⟩ => ⟨h1, h2, Or.inr h3⟩
  | obj =>
    obtain hf | ⟨hi, hc, hh⟩ := hf
    · cases hf
    simp only [hh, ite_true]
    exact (fastWrite_good (e := { e with log := e.log ++ [.del i] }) hi hc).mono
      fun _ e' c' ⟨h1, h2, h3⟩ => ⟨h1, h2, Or.inr h3⟩

theorem fastPre_shape {acc : Acc} {r r' : Recv} {P P' : Prop}
    (h : acc = .generic ∨ P) (hs : acc = .generic ∨ Shape r r') (hP : Shape r r' → P → P') :
    acc = .generic ∨ P' := by
  rcases h with h | h
  · exact Or.inl h
  · rcases hs with hs | hs
    · exact Or.inl hs
    · exact Or.inr (hP hs h)

theorem shape_or_trans {acc : Acc} {r1 r2 r3 : Recv} (h1 : acc = .generic ∨ Shape r1 r2)
    (h2 : acc = .generic ∨ Shape r2 r3) : acc = .generic ∨ Shape r1 r3 := by
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · rcases h2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (h1.trans h2)

theorem getD_seg_map {l : List (Option Val)} {vs : List Val} {n j : Nat} (hn : n ≤ l.length)
    (hw : seg l 0 n = vs.map some) (hj : j < n) : l.getD j none = some (vs.getD j .undef) := by
  have h1 := getElem?_seg l 0 n j
  rw [hw, ite_eq_left (show j < n - 0 by omega), Nat.zero_add] at h1
  have hl : vs.length = n := by
    have := congrArg List.length hw
    rw [length_seg hn, List.length_map] at this
    omega
  rw [List.getD_eq_getElem?_getD, ← h1, List.getElem?_map, List.getElem?_eq_getElem (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < vs.length by omega)]

theorem storeLoop_good {cfg : Cfg} {env : Env} {acc : Acc} {n : Nat} {vs : List Val} {c : Core}
    (hn : n ≤ c.work.length) (hw : seg c.work 0 n = vs.map some) (hv : ∀ v ∈ vs, ValOK cfg acc v) :
    ∀ d i (e : Ext), n - i = d → i ≤ n →
      (acc = .generic ∨ (n ≤ e.recv.arr.store.length ∧ e.recv.arr.cow = false)) →
      ((storeLoop cfg env acc n i) e c).Good (fun _ e' c' => c' = c ∧
        e'.log = e.log ++ (List.range' i (n - i)).map (fun j => WB.store j (vs.getD j .undef)) ∧
        (acc = .generic ∨ Shape e.recv e'.recv))
  | 0, i, e, hd, hi, hf => by
    rw [storeLoop, dite_eq_right (by omega), good_pure]
    refine ⟨rfl, ?_, Or.inr (Shape.refl _)⟩
    simp [show n - i = 0 by omega]
  | d + 1, i, e, hd, hi, hf => by
    rw [storeLoop, dite_eq_left (by omega)]
    have hj := getD_seg_map hn hw (show i < n by omega)
    have hvl : vs.length = n := by
      have := congrArg List.length hw
      rw [length_seg hn, List.length_map] at this
      omega
    simp only [good_bind, good_ld, Core.get_work]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    simp only [Int.toNat_natCast, hj, good_jsAny]
    refine ⟨_, rfl, ?_⟩
    refine (storeTo_good ?_ ?_).mono ?_
    · apply hv
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    · rcases hf with hf | hf
      · exact Or.inl hf
      · exact Or.inr ⟨by omega, hf.2⟩
    · rintro _ e' c' ⟨h1, h2, h3⟩
      subst c'
      have := storeLoop_good (env := env) hn hw hv d (i + 1) e' (by omega) (by omega)
        (fastPre_shape hf h3 fun hs h => ⟨by rw [hs.2.2.2]; exact h.1, by rw [hs.2.2.1]; exact h.2⟩)
      refine this.mono ?_
      rintro _ e2 c2 ⟨g1, g2, g3⟩
      refine ⟨g1, ?_, shape_or_trans h3 g3⟩
      rw [g2, h2, show n - i = (n - (i + 1)) + 1 by omega, List.range'_succ]
      simp

theorem undefLoop_good {cfg : Cfg} {env : Env} {acc : Acc} {n : Nat} {c : Core} :
    ∀ d i (e : Ext), n - i = d → i ≤ n → (i < n → ValOK cfg acc .undef) →
      (acc = .generic ∨ (n ≤ e.recv.arr.store.length ∧ e.recv.arr.cow = false)) →
      ((undefLoop cfg env acc n i) e c).Good (fun _ e' c' => c' = c ∧
        e'.log = e.log ++ (List.range' i (n - i)).map (fun j => WB.store j .undef) ∧
        (acc = .generic ∨ Shape e.recv e'.recv))
  | 0, i, e, hd, hi, hu, hf => by
    rw [undefLoop, dite_eq_right (by omega), good_pure]
    refine ⟨rfl, ?_, Or.inr (Shape.refl _)⟩
    simp [show n - i = 0 by omega]
  | d + 1, i, e, hd, hi, hu, hf => by
    rw [undefLoop, dite_eq_left (by omega)]
    refine good_bind_of (storeTo_good (hu (by omega)) ?_) ?_
    · rcases hf with hf | hf
      · exact Or.inl hf
      · exact Or.inr ⟨by omega, hf.2⟩
    · rintro _ e' c' ⟨h1, h2, h3⟩
      subst c'
      have := undefLoop_good (cfg := cfg) (env := env) (acc := acc) (n := n) (c := c) d (i + 1) e'
        (by omega) (by omega) (fun h => hu (by omega))
        (fastPre_shape hf h3 fun hs h => ⟨by rw [hs.2.2.2]; exact h.1, by rw [hs.2.2.1]; exact h.2⟩)
      refine this.mono ?_
      rintro _ e2 c2 ⟨g1, g2, g3⟩
      refine ⟨g1, ?_, shape_or_trans h3 g3⟩
      rw [g2, h2, show n - i = (n - (i + 1)) + 1 by omega, List.range'_succ]
      simp

theorem deleteLoop_good {env : Env} {acc : Acc} {n : Nat} {c : Core} :
    ∀ d i (e : Ext), n - i = d → i ≤ n →
      (acc = .generic ∨ (n ≤ e.recv.arr.store.length ∧ e.recv.arr.cow = false ∧
        (i < n → e.recv.arr.kind.isHoley = true))) →
      ((deleteLoop env acc n i) e c).Good (fun _ e' c' => c' = c ∧
        e'.log = e.log ++ (List.range' i (n - i)).map WB.del)
  | 0, i, e, hd, hi, hf => by
    rw [deleteLoop, dite_eq_right (by omega), good_pure]
    refine ⟨rfl, ?_⟩
    simp [show n - i = 0 by omega]
  | d + 1, i, e, hd, hi, hf => by
    rw [deleteLoop, dite_eq_left (by omega)]
    refine good_bind_of (deleteAt_good ?_) ?_
    · rcases hf with hf | hf
      · exact Or.inl hf
      · exact Or.inr ⟨by omega, hf.2.1, hf.2.2 (by omega)⟩
    · rintro _ e' c' ⟨h1, h2, h3⟩
      subst c'
      have := deleteLoop_good (env := env) (acc := acc) (n := n) (c := c) d (i + 1) e' (by omega) (by omega)
        (fastPre_shape hf h3 fun hs h => ⟨by rw [hs.2.2.2]; exact h.1, by rw [hs.2.2.1]; exact h.2.1,
          fun _ => by rw [hs.2.1]; exact h.2.2 (by omega)⟩)
      refine this.mono ?_
      rintro _ e2 c2 ⟨g1, g2⟩
      refine ⟨g1, ?_⟩
      rw [g2, h2, show n - i = (n - (i + 1)) + 1 by omega, List.range'_succ]
      simp

def AccFacts (cfg : Cfg) (acc : Acc) (r : Recv) (vs : List Val) (nu sortLength : Nat) : Prop :=
  (∀ v ∈ vs, ValOK cfg acc v) ∧ (0 < nu → ValOK cfg acc .undef) ∧
    (acc = .generic ∨ (sortLength ≤ r.arr.store.length ∧ r.arr.cow = false ∧
      (vs.length + nu < sortLength → r.arr.kind.isHoley = true)))

theorem selectAcc_generic_iff {reset : Bool} {r : Recv} :
    selectAcc reset r = .generic ↔ (reset = true ∨ r.arr.fast = false) := by
  unfold selectAcc
  by_cases h : reset = true ∨ r.arr.fast = false
  · simp [h]
  · rw [ite_eq_right h]
    split
    · simp_all
    · split <;> simp_all

theorem selectAcc_shape {reset : Bool} {r r' : Recv} (h : Shape r r') : selectAcc reset r' = selectAcc reset r := by
  unfold selectAcc
  rw [h.1, h.2.1]

theorem copyBack_good {cfg : Cfg} {env : Env} {reset : Bool} {n nu sortLength : Nat} {vs : List Val}
    {e : Ext} {c : Core} (hn : n ≤ c.work.length) (hw : seg c.work 0 n = vs.map some)
    (hs : n + nu ≤ sortLength) (hreset : reset = false → e.recv.arr.fast = true)
    (hf : AccFacts cfg (selectAcc reset e.recv) e.recv vs nu sortLength) :
    ((copyBack cfg env reset n nu sortLength) e c).Good (fun _ e' c' => c' = c ∧
      e'.log = e.log ++ writeLog vs nu sortLength) := by
  have hvl : vs.length = n := by
    have := congrArg List.length hw
    rw [length_seg hn, List.length_map] at this
    omega
  obtain ⟨hv, hu, hp⟩ := hf
  unfold copyBack
  simp only [good_bind, good_getExt, good_getCore, good_dcheck]
  refine ⟨hn, hs, ?_⟩
  refine (storeLoop_good hn hw hv n 0 e (by omega) (Nat.zero_le _) ?_).mono ?_
  · rcases hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr ⟨by omega, hp.2.1⟩
  rintro _ e1 c1 ⟨h1, h2, h3⟩
  subst c1
  rw [good_ite]
  split
  · next heq =>
    refine ⟨rfl, ?_⟩
    rw [h2, writeLog, hvl, show nu = 0 by omega, show sortLength - n - 0 = 0 by omega, List.range'_zero,
      List.range'_zero, ← List.range_eq_range']
    simp
  · next hne =>
    refine good_bind_of (undefLoop_good (nu + n - n) n e1 rfl (by omega) (fun h => hu (by omega)) ?_) ?_
    · exact fastPre_shape hp h3 fun hs h => ⟨by rw [hs.2.2.2]; omega, by rw [hs.2.2.1]; exact h.2.1⟩
    rintro _ e2 c2 ⟨g1, g2, g3⟩
    subst c2
    simp only [good_bind, good_getExt]
    have hacc : selectAcc reset e2.recv = selectAcc reset e.recv := by
      cases reset with
      | true => simp [selectAcc]
      | false =>
        have hne : selectAcc false e.recv ≠ .generic := by
          rw [Ne, selectAcc_generic_iff]
          simp [hreset rfl]
        rcases shape_or_trans h3 g3 with hg | hg
        · exact absurd hg hne
        · exact selectAcc_shape hg
    rw [hacc]
    refine (deleteLoop_good (sortLength - (nu + n)) (nu + n) e2 rfl (by omega) ?_).mono ?_
    · rcases hp with hp | hp
      · exact Or.inl hp
      · rcases shape_or_trans h3 g3 with hg | hg
        · exact Or.inl hg
        · refine Or.inr ⟨by rw [hg.2.2.2]; exact hp.1, by rw [hg.2.2.1]; exact hp.2.1, fun h => ?_⟩
          rw [hg.2.1]
          exact hp.2.2 (by omega)
    · rintro _ e3 c3 ⟨k1, k2⟩
      refine ⟨k1, ?_⟩
      rw [k2, g2, h2, writeLog, hvl, ← List.range_eq_range', show nu + n - n = nu by omega,
        show n + nu = nu + n by omega, show sortLength - n - nu = sortLength - (nu + n) by omega]
      simp

end ArraySort
