import ArrayJoin.BufferSafety

namespace ArrayJoin

theorem fold_inv {l : Limits} {sep : List Nat} {b : Buf} {C : List Nat} (hi : Inv l sep b C)
    {sl : Nat} (hsl : C.length ≤ sl) :
    ∃ last, fold sl sep b.flat = some ⟨C, if b.cur = [] then 0 else 1, last⟩ := by
  obtain ⟨⟨o, ns, last⟩, hf, ho, hns⟩ := hi.write sl hsl
  dsimp only at ho hns
  subst ho hns
  exact ⟨last, hf⟩

theorem fold_inv_str {l : Limits} {sep : List Nat} {b : Buf} {C : List Nat} (hi : Inv l sep b C)
    {n : Nat} (hn : b.cur ≠ [] → 1 ≤ n) (h0 : n = 0 ∨ sep.length = 0) {s : Str} {sl : Nat}
    (hsl : (C ++ s.chars).length ≤ sl) :
    fold sl sep (b.flat ++ [.str s]) = some ⟨C ++ s.chars, 1, some s⟩ := by
  obtain ⟨last, hf⟩ := fold_inv hi (sl := sl) (by simp at hsl; omega)
  rw [fold_snoc, hf, Option.bind]
  by_cases hc : b.cur = []
  · rw [ite_eq_left hc]
    exact wItem_str_zero (by simpa [Str.len] using hsl)
  · rw [ite_eq_right hc]
    have hsep : sep = [] := by
      rcases h0 with h | h
      · have := hn hc
        omega
      · exact List.eq_nil_of_length_eq_zero h
    subst hsep
    simpa using wItem_str_one (sl := sl) (sep := []) (o := C) (last := last) (s := s)
      (by simpa [Str.len] using hsl)

theorem add_spec {l : Limits} (hl : l.OK) {sep : List Nat} {b : Buf} {C : List Nat}
    (hi : Inv l sep b C) {s : Str} (hs : s.chars ≠ []) {n : Nat} (hn : b.cur ≠ [] → 1 ≤ n)
    (hsep : sep.length * n ≤ l.strMax) :
    add l b s n sep.length = .throws ∨
      ∃ b', add l b s n sep.length = .ok b' ∧ Inv l sep b' (C ++ sepRun sep n ++ s.chars) ∧
        b'.last = some s ∧ b'.cur ≠ [] := by
  unfold add
  by_cases h0 : n = 0 ∨ sep.length = 0
  · rw [sepRun_nil h0, List.append_nil]
    have ha : addSeparators l b n sep.length (b.cur.isEmpty || decide (1 < n)) = .ok b := by
      unfold addSeparators
      rw [ite_eq_left h0]
    rw [ha, Res.ok_bind]
    unfold addLen
    by_cases ht : b.total + s.len ≤ l.strMax
    · rw [ite_eq_left ht, Res.ok_bind]
      by_cases hls : b.last = some s
      · rw [ite_eq_left hls]
        have hcur : b.cur ≠ [] := fun h => by
          have := (hi.empty h).2
          rw [this] at hls
          cases hls
        have hsepnil : sep = [] := by
          rcases h0 with h | h
          · have := hn hcur
            omega
          · exact List.eq_nil_of_length_eq_zero h
        subst hsepnil
        have heq : b.total + s.len = (C ++ [] ++ s.chars).length := by
          rw [hi.total]
          simp [Str.len]
        rw [heq]
        obtain ⟨b', h1, h2, h3, h4⟩ := repeat_case hl hi hls (by rw [← heq]; exact ht)
        exact Or.inr ⟨b', h1, by simpa using h2, h3, h4⟩
      · rw [ite_eq_right hls]
        have heq : b.total + s.len = (C ++ s.chars).length := by
          rw [hi.total]
          simp [Str.len]
        rw [heq]
        exact Or.inr (append_case hl hi.chunk hs (by rw [← heq]; exact ht)
          (fun sl hsl => fold_inv_str hi hn h0 hsl))
    · rw [ite_eq_right ht]
      exact Or.inl rfl
  · have hn0 : n ≠ 0 := fun h => h0 (Or.inl h)
    have hs0 : sep.length ≠ 0 := fun h => h0 (Or.inr h)
    have hnle : n ≤ sep.length * n := Nat.le_mul_of_pos_left n (by omega)
    unfold addSeparators
    rw [ite_eq_right h0, ite_eq_right (by have := hl.int; omega)]
    unfold addLen
    by_cases ht1 : b.total + sep.length * n ≤ l.strMax
    · rw [ite_eq_left ht1, Res.ok_bind]
      by_cases hw : (b.cur.isEmpty || decide (1 < n)) = true
      · rw [ite_eq_left hw, ite_eq_right (by have := hl.smi; omega)]
        obtain ⟨b1, he, hc1, hf1, _, ht1', _, _⟩ :=
          appendToChunk_spec hl (b := { b with total := b.total + sep.length * n }) hi.chunk (.seps n)
        rw [he, Res.ok_bind, Res.ok_bind]
        by_cases ht2 : b1.total + s.len ≤ l.strMax
        · rw [ite_eq_left ht2, Res.ok_bind, ite_eq_right (by simp)]
          have heq : b1.total + s.len = (C ++ sepRun sep n ++ s.chars).length := by
            rw [ht1']
            show b.total + sep.length * n + s.len = _
            rw [hi.total]
            simp [sepRun_length, Str.len, Nat.mul_comm]
            omega
          rw [heq]
          refine Or.inr (append_case hl (b0 := { b1 with last := none }) hc1 hs
            (by rw [← heq]; exact ht2) ?_)
          intro sl hsl
          have hf1' : ({ b1 with last := none } : Buf).flat = b.flat ++ [.seps n] := hf1
          have hsl' : (C ++ sepRun sep n).length ≤ sl := by simp at hsl ⊢; omega
          obtain ⟨last, hf⟩ := fold_inv hi (sl := sl) (by simp at hsl'; omega)
          rw [hf1', fold_snoc, fold_snoc, hf, Option.bind,
            wItem_seps (by omega) (by omega) (by simp only [List.length_append, sepRun_length] at hsl'; omega),
            Option.bind, wItem_str_zero (by simp only [List.length_append, Str.len] at hsl ⊢; omega)]
        · rw [ite_eq_right ht2]
          exact Or.inl rfl
      · rw [ite_eq_right hw, Res.ok_bind]
        simp only [Bool.or_eq_true, List.isEmpty_iff, decide_eq_true_eq, not_or] at hw
        have hcur : b.cur ≠ [] := hw.1
        have hn1 : n = 1 := by
          have := hn hcur
          omega
        subst hn1
        rw [sepRun_one]
        by_cases ht2 : b.total + sep.length * 1 + s.len ≤ l.strMax
        · rw [ite_eq_left ht2, Res.ok_bind]
          have heq : b.total + sep.length * 1 + s.len = (C ++ sep ++ s.chars).length := by
            rw [hi.total]
            simp [Str.len]
            omega
          by_cases hls : b.last = some s
          · rw [ite_eq_left hls, heq]
            obtain ⟨b', h1, h2, h3, h4⟩ := repeat_case hl hi hls (by rw [← heq]; exact ht2)
            exact Or.inr ⟨b', h1, h2, h3, h4⟩
          · rw [ite_eq_right hls, heq]
            refine Or.inr (append_case hl (b0 := { b with total := b.total + sep.length * 1 })
              hi.chunk hs (by rw [← heq]; exact ht2) ?_)
            intro sl hsl
            obtain ⟨last, hf⟩ := fold_inv hi (sl := sl) (by simp at hsl; omega)
            show fold sl sep (b.flat ++ [.str s]) = _
            rw [fold_snoc, hf, Option.bind, ite_eq_right hcur]
            exact wItem_str_one (by simpa [Str.len, Nat.add_assoc] using hsl)
        · rw [ite_eq_right ht2]
          exact Or.inl rfl
    · rw [ite_eq_right ht1]
      exact Or.inl rfl

theorem finish_spec {l : Limits} (hl : l.OK) {sep : List Nat} {b : Buf} {C : List Nat}
    (hi : Inv l sep b C) {n : Nat} (hsep : sep.length * n ≤ l.strMax) :
    addSeparators l b n sep.length true = .throws ∨
      ∃ b', addSeparators l b n sep.length true = .ok b' ∧ ChunkOK b' ∧
        b'.total = (C ++ sepRun sep n).length ∧
        ∀ sl, (C ++ sepRun sep n).length ≤ sl →
          ∃ w, fold sl sep b'.flat = some w ∧ w.out = C ++ sepRun sep n := by
  unfold addSeparators
  by_cases h0 : n = 0 ∨ sep.length = 0
  · rw [ite_eq_left h0, sepRun_nil h0, List.append_nil]
    refine Or.inr ⟨b, rfl, hi.chunk, hi.total, fun sl hsl => ?_⟩
    obtain ⟨w, hf, ho, _⟩ := hi.write sl hsl
    exact ⟨w, hf, ho⟩
  · have hnle : n ≤ sep.length * n := Nat.le_mul_of_pos_left n (by omega)
    rw [ite_eq_right h0, ite_eq_right (by have := hl.int; omega)]
    unfold addLen
    by_cases ht : b.total + sep.length * n ≤ l.strMax
    · rw [ite_eq_left ht, Res.ok_bind, ite_eq_left rfl, ite_eq_right (by have := hl.smi; omega)]
      obtain ⟨b1, he, hc1, hf1, _, ht1, _, _⟩ :=
        appendToChunk_spec hl (b := { b with total := b.total + sep.length * n }) hi.chunk (.seps n)
      rw [he, Res.ok_bind]
      refine Or.inr ⟨_, rfl, hc1, ?_, fun sl hsl => ?_⟩
      · show b1.total = _
        rw [ht1]
        show b.total + sep.length * n = _
        rw [hi.total]
        simp [sepRun_length, Nat.mul_comm]
      · obtain ⟨last, hf⟩ := fold_inv hi (sl := sl) (by simp at hsl; omega)
        refine ⟨⟨C ++ sepRun sep n, 0, none⟩, ?_, rfl⟩
        show fold sl sep b1.flat = _
        rw [hf1]
        show fold sl sep (b.flat ++ [.seps n]) = _
        rw [fold_snoc, hf, Option.bind,
          wItem_seps (by omega) (by omega) (by rw [List.length_append, sepRun_length] at hsl; omega)]
    · rw [ite_eq_right ht]
      exact Or.inl rfl

theorem fold_single (sl : Nat) (sep : List Nat) (x : Item) :
    fold sl sep [x] = wItem sl sep WS.init x := by
  simp [fold]

theorem init_str {sl : Nat} {sep : List Nat} {s : Str} {w : WS}
    (h : wItem sl sep WS.init (.str s) = some w) : w.out = s.chars := by
  simp [wItem, writeSeps, WS.init] at h
  rw [← h.2]

theorem init_rep {sl : Nat} {sep : List Nat} {m : Nat} {w : WS}
    (h : wItem sl sep WS.init (.rep m) = some w) : w.out = [] := by
  simp [wItem, writeSeps, WS.init, repStep] at h
  rw [← h.2]

theorem init_seps {sl : Nat} {sep : List Nat} {m : Nat} {w : WS}
    (h : wItem sl sep WS.init (.seps m) = some w) :
    w.out = [] ∨ (0 < m ∧ w.out = sepRun sep m) := by
  by_cases hm : 0 < m
  · by_cases hs : 0 < sep.length
    · simp [wItem, writeSeps, WS.init, hm, hs] at h
      exact Or.inr ⟨hm, by rw [← h.2]⟩
    · simp [wItem, writeSeps, WS.init, hm, hs] at h
      exact Or.inl (by rw [← h])
  · simp [wItem, writeSeps, WS.init, hm] at h
    exact Or.inl (by rw [← h])

theorem bufferJoin_spec {b : Buf} {sep : Str} {C : List Nat} (hc : ChunkOK b)
    (ht : b.total = C.length)
    (hw : ∀ sl, C.length ≤ sl → ∃ w, fold sl sep.chars b.flat = some w ∧ w.out = C) :
    bufferJoin b sep = .ok C := by
  unfold bufferJoin
  by_cases h0 : b.total = 0
  · rw [ite_eq_left h0]
    rw [h0] at ht
    rw [List.eq_nil_of_length_eq_zero ht.symm]
  rw [ite_eq_right h0]
  by_cases h1 : b.cur.length = 1 ∧ b.full = []
  · rw [ite_eq_left h1]
    obtain ⟨w, hf, ho⟩ := hw C.length (Nat.le_refl _)
    have hflat : b.flat = b.cur := by simp [Buf.flat, h1.2]
    rw [hflat] at hf
    match hcur : b.cur, h1 with
    | [x], _ =>
      rw [hcur, fold_single] at hf
      have hne : C ≠ [] := fun h => h0 (by rw [ht, h]; rfl)
      cases x with
      | str s =>
        show Res.ok s.chars = Res.ok C
        rw [← init_str hf, ho]
      | seps m =>
        show (if 0 < m then Res.ok (sepRun sep.chars m) else Res.ub) = Res.ok C
        rcases init_seps hf with h | ⟨hm, h⟩
        · exact absurd (by rw [← ho, h]) hne
        · rw [ite_eq_left hm, ← ho, h]
      | rep r => exact absurd (by rw [← ho, init_rep hf]) hne
  · rw [ite_eq_right h1, writeChunks_eq hc]
    obtain ⟨w, hf, ho⟩ := hw b.total (by omega)
    simp only [fold] at hf
    rw [hf]
    dsimp only
    rw [ho, ite_eq_left ht.symm]

end ArrayJoin
