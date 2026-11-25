import ArrayFlat.Machine

namespace ArrayFlat

open Torque

def Covers (s : P1) (out : List Val) : Prop :=
  ∀ v ∈ out, v.isSmi = true ∨ (s.seenDouble = true ∧ v.isNumber = true) ∨ s.seenObject = true

def Inv1 (cfg : Config) (H : Heap) (L : List Val) (s : P1) : Prop :=
  ∃ out, out ++ pendingAll H s.cur s.stack = L ∧ s.tl = out.length ∧ Covers s out ∧
    s.tl ≤ cfg.maxLen

theorem step1_inv {cfg : Config} {H : Heap} (hH : HeapWF H) {L : List Val} (s t : P1)
    (hi : Inv1 cfg H L s) (h : step1 cfg H s = .cont t) : Inv1 cfg H L t := by
  obtain ⟨out, hsplit, htl, hcov, hmax⟩ := hi
  unfold step1 at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hs : s.stack with
    | nil => simp [hs] at h
    | cons g rest =>
      simp only [hs] at h
      split at h
      · cases h
        refine ⟨out, ?_, htl, hcov, hmax⟩
        rw [← hsplit, hs, pendingAll_pop g rest hf]
      · cases h
  | bail => simp [hf] at h
  | oob => simp [hf] at h
  | elem x =>
    cases x with
    | none =>
      simp only [hf] at h
      cases h
      exact ⟨out, by rw [← hsplit, pendingAll_hole _ hf], htl, hcov, hmax⟩
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        refine ⟨out ++ [v], ?_, ?_, ?_, ?_⟩
        · rw [← hsplit, pendingAll_leaf _ hf hd]
          simp
        · simp [htl]
        · intro w hw
          simp only [List.mem_append, List.mem_singleton] at hw
          rcases hw with hw | rfl
          · rcases hcov w hw with h1 | ⟨h2, h3⟩ | h4
            · exact Or.inl h1
            · exact Or.inr (Or.inl ⟨by simp [h2], h3⟩)
            · exact Or.inr (Or.inr (by simp [h4]))
          · cases w <;> simp [Val.isSmi, Val.isNumber]
        · dsimp only
          omega
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        · have hk : (H q).kind = .packedSmi ∨ (H q).kind = .packedDouble :=
            Or.inl ‹(H q).kind = .packedSmi›
          refine ⟨out ++ leaves H d (H q).elems, ?_, ?_, ?_, ?_⟩
          · rw [← hsplit, pendingAll_skip _ hf hd, List.append_assoc]
          · simp [htl, leaves_numeric_length H d (hH q) hk]
          · intro w hw
            simp only [List.mem_append] at hw
            rcases hw with hw | hw
            · exact hcov w hw
            · rw [leaves_numeric H d (hH q) hk, mem_filterMap_id] at hw
              obtain ⟨u, hu, hs⟩ := packedSmi_elem (hH q) ‹(H q).kind = .packedSmi› hw
              cases hu
              exact Or.inl hs
          · dsimp only
            omega
        · have hk : (H q).kind = .packedSmi ∨ (H q).kind = .packedDouble :=
            Or.inr ‹(H q).kind = .packedDouble›
          refine ⟨out ++ leaves H d (H q).elems, ?_, ?_, ?_, ?_⟩
          · rw [← hsplit, pendingAll_skip _ hf hd, List.append_assoc]
          · simp [htl, leaves_numeric_length H d (hH q) hk]
          · intro w hw
            simp only [List.mem_append] at hw
            rcases hw with hw | hw
            · rcases hcov w hw with h1 | ⟨_, h3⟩ | h4
              · exact Or.inl h1
              · exact Or.inr (Or.inl ⟨rfl, h3⟩)
              · exact Or.inr (Or.inr h4)
            · rw [leaves_numeric H d (hH q) hk, mem_filterMap_id] at hw
              obtain ⟨u, hu, hs⟩ := packedDouble_elem (hH q) ‹(H q).kind = .packedDouble› hw
              cases hu
              exact Or.inr (Or.inl ⟨rfl, hs⟩)
          · dsimp only
            omega
        · exact ⟨out, by rw [← hsplit, pendingAll_descend _ hf hd], htl, hcov, hmax⟩

theorem step1_ne_ub {cfg : Config} {H : Heap} (hH : HeapWF H) (s : P1) :
    step1 cfg H s ≠ .ub := by
  intro h
  unfold step1 at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hs : s.stack with
    | nil => simp [hs] at h
    | cons g rest =>
      simp only [hs] at h
      split at h <;> cases h
  | bail => simp [hf] at h
  | oob => exact fetch_ne_oob (hH s.cur.arr) hf
  | elem x =>
    cases x with
    | none => simp [hf] at h
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        repeat' split at h
        all_goals cases h

theorem covers_conforms (s : P1) (out : List Val) (h : Covers s out) :
    Conforms s.targetKind out := by
  unfold P1.targetKind
  by_cases ho : s.seenObject = true
  · simp [ho, Conforms]
  · by_cases hd : s.seenDouble = true
    · simp only [ho, hd, Conforms]
      intro v hv
      rcases h v hv with h1 | ⟨_, h3⟩ | h4
      · exact isNumber_of_isSmi h1
      · exact h3
      · exact absurd h4 ho
    · simp only [ho, hd, Conforms]
      intro v hv
      rcases h v hv with h1 | ⟨h2, _⟩ | h4
      · exact h1
      · exact absurd h2 hd
      · exact absurd h4 ho

theorem step1_done {cfg : Config} {H : Heap} {L : List Val} {s : P1} {r : Nat × Kind}
    (hi : Inv1 cfg H L s) (h : step1 cfg H s = .done r) :
    r.1 = L.length ∧ Conforms r.2 L ∧ r.1 ≤ cfg.maxLen := by
  obtain ⟨out, hsplit, htl, hcov, hmax⟩ := hi
  unfold step1 at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hs : s.stack with
    | nil =>
      simp only [hs] at h
      cases h
      rw [hs, pendingAll_done hf, List.append_nil] at hsplit
      subst hsplit
      exact ⟨htl, covers_conforms s out hcov, hmax⟩
    | cons g rest =>
      simp only [hs] at h
      split at h <;> cases h
  | bail => simp [hf] at h
  | oob => simp [hf] at h
  | elem x =>
    cases x with
    | none => simp [hf] at h
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        repeat' split at h
        all_goals cases h

theorem init1_inv (cfg : Config) (H : Heap) (root srcLen depth : Nat) :
    Inv1 cfg H (flatSpec H root srcLen depth) (init1 root srcLen depth) := by
  refine ⟨[], ?_, rfl, by simp [Covers], Nat.zero_le _⟩
  simp [init1, pendingAll, Frame.pending, Frame.rest, flatSpec]

theorem run1_ok {cfg : Config} {H : Heap} (hH : HeapWF H) {root srcLen depth : Nat}
    {r : Nat × Kind} (h : run1 cfg H (init1 root srcLen depth) = .ok r) :
    r.1 = (flatSpec H root srcLen depth).length ∧
      Conforms r.2 (flatSpec H root srcLen depth) ∧ r.1 ≤ cfg.maxLen := by
  obtain ⟨t, ht, hd⟩ := run_ok h
  exact step1_done (ht.invariant (step1_inv hH) (init1_inv cfg H root srcLen depth)) hd

theorem run1_ne_ub {cfg : Config} {H : Heap} (hH : HeapWF H) (s : P1) :
    run1 cfg H s ≠ .ub := by
  intro h
  obtain ⟨t, _, ht⟩ := run_ub h
  exact step1_ne_ub hH t ht

theorem flatSpec_numeric {H : Heap} (hH : HeapWF H) {root srcLen depth : Nat}
    (hk : (H root).kind = .packedSmi ∨ (H root).kind = .packedDouble) :
    flatSpec H root srcLen depth = ((H root).elems.take srcLen).filterMap id := by
  unfold flatSpec
  apply leaves_of_noArr
  intro x hx
  obtain ⟨v, rfl, hv⟩ := numeric_elems (hH root) hk x (List.mem_of_mem_take hx)
  exact ⟨v, rfl, not_arr_of_isNumber hv⟩

theorem conforms_root {H : Heap} (hH : HeapWF H) {root srcLen depth : Nat}
    (hk : (H root).kind = .packedSmi ∨ (H root).kind = .packedDouble) :
    Conforms (H root).kind (flatSpec H root srcLen depth) := by
  rw [flatSpec_numeric hH hk]
  rcases hk with hk | hk
  · rw [hk]
    intro v hv
    rw [mem_filterMap_id] at hv
    obtain ⟨u, hu, hs⟩ := packedSmi_elem (hH root) hk (List.mem_of_mem_take hv)
    cases hu
    exact hs
  · rw [hk]
    intro v hv
    rw [mem_filterMap_id] at hv
    obtain ⟨u, hu, hs⟩ := packedDouble_elem (hH root) hk (List.mem_of_mem_take hv)
    cases hu
    exact hs

theorem calcLength_ok {cfg : Config} {H : Heap} (hH : HeapWF H) {root srcLen depth len : Nat}
    {k : Kind} (h : calcLength cfg H root srcLen depth = .ok (len, k)) :
    Conforms k (flatSpec H root srcLen depth) ∧
      ((len = (flatSpec H root srcLen depth).length ∧ len ≤ cfg.maxLen) ∨
        (((H root).kind = .packedSmi ∨ (H root).kind = .packedDouble) ∧ len = srcLen)) := by
  unfold calcLength at h
  split at h
  · rename_i hk
    cases h
    exact ⟨conforms_root hH hk, Or.inr ⟨hk, rfl⟩⟩
  · split at h
    · cases h
    · obtain ⟨h1, h2, h3⟩ := run1_ok hH h
      exact ⟨h2, Or.inl ⟨h1, h3⟩⟩

theorem calcLength_ne_ub {cfg : Config} {H : Heap} (hH : HeapWF H) (root srcLen depth : Nat) :
    calcLength cfg H root srcLen depth ≠ .ub := by
  unfold calcLength
  split
  · simp
  · split
    · simp
    · exact run1_ne_ub hH _

theorem calcLength_ne_fatal (cfg : Config) (H : Heap) (root srcLen depth : Nat) :
    calcLength cfg H root srcLen depth ≠ .fatal := by
  unfold calcLength
  split
  · simp
  · split
    · simp
    · exact run_ne_fatal _ _ _ _

def Inv2 (H : Heap) (L : List Val) (cap : Nat) (s : P2) : Prop :=
  ∃ out, out ++ pendingAll H s.cur s.stack = L ∧ s.ti = out.length ∧
    s.buf = out.map some ++ List.replicate (cap - out.length) none ∧ out.length ≤ cap

theorem Inv2.buf_length {H : Heap} {L : List Val} {cap : Nat} {s : P2} (hi : Inv2 H L cap s) :
    s.buf.length = cap := by
  obtain ⟨out, _, _, hbuf, hle⟩ := hi
  rw [hbuf]
  simp
  omega

theorem inv2_copy {H : Heap} (hH : HeapWF H) {L : List Val} {cap : Nat} {s : P2}
    {f : Frame} {v : Val} {d q : Nat} (hi : Inv2 H L cap s) (hcur : s.cur = f)
    (hf : fetch H f = .elem (some v)) (hd : descend? f.depth v = some (d, q))
    (hk : (H q).kind = .packedSmi ∨ (H q).kind = .packedDouble)
    (hfit : ¬ s.buf.length < s.ti + (H q).length) :
    Inv2 H L cap { s with
      cur := f.next
      ti := s.ti + (H q).length
      buf := blit s.buf s.ti ((H q).store.take (H q).length) } := by
  have hlen := hi.buf_length
  obtain ⟨out, hsplit, hti, hbuf, hle⟩ := hi
  subst hcur
  have hl := leaves_numeric_length H d (hH q) hk
  refine ⟨out ++ leaves H d (H q).elems, ?_, ?_, ?_, ?_⟩
  · rw [← hsplit, pendingAll_skip _ hf hd, List.append_assoc]
  · simp [hti, hl]
  · show blit s.buf s.ti (H q).elems = _
    rw [hbuf, hti, blit_spec, List.map_append, List.length_append, hl,
      leaves_numeric_map_some H d (hH q) hk, JSArr.elems_length (hH q), Nat.sub_sub,
      List.append_assoc]
  · simp [hl]
    omega

theorem inv2_write {H : Heap} {L : List Val} {cap : Nat} {s : P2} {f : Frame} {v : Val}
    (hi : Inv2 H L cap s) (hcur : s.cur = f) (hf : fetch H f = .elem (some v))
    (hd : descend? f.depth v = none) (hfit : ¬ s.buf.length ≤ s.ti) :
    Inv2 H L cap { s with cur := f.next, ti := s.ti + 1, buf := blit s.buf s.ti [some v] } := by
  have hlen := hi.buf_length
  obtain ⟨out, hsplit, hti, hbuf, hle⟩ := hi
  subst hcur
  refine ⟨out ++ [v], ?_, ?_, ?_, ?_⟩
  · rw [← hsplit, pendingAll_leaf _ hf hd]
    simp
  · simp [hti]
  · show blit s.buf s.ti [some v] = _
    rw [hbuf, hti, blit_spec]
    simp [Nat.sub_sub]
  · simp
    omega

theorem inv2_hole {H : Heap} {L : List Val} {cap : Nat} {s : P2}
    (hi : Inv2 H L cap s) (hf : fetch H s.cur = .elem none) :
    Inv2 H L cap { s with cur := s.cur.next } := by
  obtain ⟨out, hsplit, hti, hbuf, hle⟩ := hi
  exact ⟨out, by rw [← hsplit, pendingAll_hole _ hf], hti, hbuf, hle⟩

theorem inv2_descend {H : Heap} {L : List Val} {cap : Nat} {s : P2} {v : Val} {d q : Nat}
    (hi : Inv2 H L cap s) (hf : fetch H s.cur = .elem (some v))
    (hd : descend? s.cur.depth v = some (d, q)) :
    Inv2 H L cap { s with cur := ⟨q, (H q).length, 0, d⟩, stack := s.cur.next :: s.stack } := by
  obtain ⟨out, hsplit, hti, hbuf, hle⟩ := hi
  exact ⟨out, by rw [← hsplit, pendingAll_descend _ hf hd], hti, hbuf, hle⟩

theorem inv2_pop {H : Heap} {L : List Val} {cap : Nat} {s : P2} {g : Frame} {rest : List Frame}
    (hi : Inv2 H L cap s) (hf : fetch H s.cur = .exhausted) (hs : s.stack = g :: rest) :
    Inv2 H L cap { s with cur := g, stack := rest } := by
  obtain ⟨out, hsplit, hti, hbuf, hle⟩ := hi
  exact ⟨out, by rw [← hsplit, hs, pendingAll_pop g rest hf], hti, hbuf, hle⟩

theorem stepGen_inv {cfg : Config} {H : Heap} (hH : HeapWF H) {L : List Val} {cap : Nat}
    (s t : P2) (hi : Inv2 H L cap s) (h : stepGen cfg H s = .cont t) : Inv2 H L cap t := by
  unfold stepGen at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hs : s.stack with
    | nil => simp [hs] at h
    | cons g rest =>
      simp only [hs] at h
      split at h
      · cases h
        exact inv2_pop hi hf hs
      · cases h
  | bail => simp [hf] at h
  | oob => simp [hf] at h
  | elem x =>
    cases x with
    | none =>
      simp only [hf] at h
      cases h
      exact inv2_hole hi hf
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        exact inv2_write hi rfl hf hd ‹_›
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        · exact inv2_copy hH hi rfl hf hd (Or.inl ‹_›) ‹_›
        · exact inv2_descend hi hf hd

theorem stepGen_ne_ub {cfg : Config} {H : Heap} (hH : HeapWF H) (s : P2) :
    stepGen cfg H s ≠ .ub := by
  intro h
  unfold stepGen at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hs : s.stack with
    | nil => simp [hs] at h
    | cons g rest =>
      simp only [hs] at h
      split at h <;> cases h
  | bail => simp [hf] at h
  | oob => exact fetch_ne_oob (hH s.cur.arr) hf
  | elem x =>
    cases x with
    | none => simp [hf] at h
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals first | (cases h; done) | omega
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        have := (hH q).length_le
        repeat' split at h
        all_goals first | (cases h; done) | omega

theorem stepDbl_inv {cfg : Config} {H : Heap} (hH : HeapWF H) {L : List Val} {cap : Nat}
    (s t : P2) (hi : Inv2 H L cap s) (h : stepDbl cfg H s = .cont t) : Inv2 H L cap t := by
  unfold stepDbl at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hs : s.stack with
    | nil => simp [hs] at h
    | cons g rest =>
      simp only [hs] at h
      split at h
      · cases h
        exact inv2_pop hi hf hs
      · cases h
  | bail => simp [hf] at h
  | oob => simp [hf] at h
  | elem x =>
    cases x with
    | none =>
      simp only [hf] at h
      cases h
      exact inv2_hole hi hf
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        exact inv2_write hi rfl hf hd ‹_›
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        · exact inv2_copy hH hi rfl hf hd (Or.inr ‹_›) ‹_›
        · exact inv2_descend hi hf hd

theorem stepDbl_ne_ub {cfg : Config} {H : Heap} (hH : HeapWF H) {L : List Val} {cap : Nat}
    (hL : ∀ v ∈ L, v.isNumber = true) (s : P2) (hi : Inv2 H L cap s) :
    stepDbl cfg H s ≠ .ub := by
  intro h
  unfold stepDbl at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hs : s.stack with
    | nil => simp [hs] at h
    | cons g rest =>
      simp only [hs] at h
      split at h <;> cases h
  | bail => simp [hf] at h
  | oob => exact fetch_ne_oob (hH s.cur.arr) hf
  | elem x =>
    cases x with
    | none => simp [hf] at h
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        have hv : v.isNumber = true := by
          obtain ⟨out, hsplit, _, _, _⟩ := hi
          apply hL
          rw [← hsplit, pendingAll_leaf _ hf hd]
          simp
        repeat' split at h
        all_goals first | (cases h; done) | omega | simp_all
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        have := (hH q).length_le
        repeat' split at h
        all_goals first | (cases h; done) | omega

theorem step2_done {H : Heap} {L : List Val} {cap : Nat} {s r : P2}
    (hi : Inv2 H L cap s) (hf : fetch H s.cur = .exhausted) (hs : s.stack = []) (hr : s = r) :
    r.ti = L.length ∧ r.buf = L.map some ++ List.replicate (cap - L.length) none := by
  subst hr
  obtain ⟨out, hsplit, hti, hbuf, _⟩ := hi
  rw [hs, pendingAll_done hf, List.append_nil] at hsplit
  subst hsplit
  exact ⟨hti, hbuf⟩

theorem stepGen_done {cfg : Config} {H : Heap} {L : List Val} {cap : Nat} {s r : P2}
    (hi : Inv2 H L cap s) (h : stepGen cfg H s = .done r) :
    r.ti = L.length ∧ r.buf = L.map some ++ List.replicate (cap - L.length) none := by
  unfold stepGen at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hs : s.stack with
    | nil =>
      simp only [hs] at h
      cases h
      exact step2_done hi hf hs rfl
    | cons g rest =>
      simp only [hs] at h
      split at h <;> cases h
  | bail => simp [hf] at h
  | oob => simp [hf] at h
  | elem x =>
    cases x with
    | none => simp [hf] at h
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        repeat' split at h
        all_goals cases h

theorem stepDbl_done {cfg : Config} {H : Heap} {L : List Val} {cap : Nat} {s r : P2}
    (hi : Inv2 H L cap s) (h : stepDbl cfg H s = .done r) :
    r.ti = L.length ∧ r.buf = L.map some ++ List.replicate (cap - L.length) none := by
  unfold stepDbl at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hs : s.stack with
    | nil =>
      simp only [hs] at h
      cases h
      exact step2_done hi hf hs rfl
    | cons g rest =>
      simp only [hs] at h
      split at h <;> cases h
  | bail => simp [hf] at h
  | oob => simp [hf] at h
  | elem x =>
    cases x with
    | none => simp [hf] at h
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        repeat' split at h
        all_goals cases h

theorem init2_inv (H : Heap) (root srcLen depth len : Nat) :
    Inv2 H (flatSpec H root srcLen depth) len (init2 root srcLen depth len) := by
  refine ⟨[], ?_, rfl, by simp [init2], Nat.zero_le _⟩
  simp [init2, pendingAll, Frame.pending, Frame.rest, flatSpec]

theorem runGen_ok {cfg : Config} {H : Heap} (hH : HeapWF H) {root srcLen depth len : Nat}
    {r : P2} (h : runGen cfg H (init2 root srcLen depth len) = .ok r) :
    r.ti = (flatSpec H root srcLen depth).length ∧
      r.buf = (flatSpec H root srcLen depth).map some ++
        List.replicate (len - (flatSpec H root srcLen depth).length) none := by
  obtain ⟨t, ht, hd⟩ := run_ok h
  exact stepGen_done (ht.invariant (stepGen_inv hH) (init2_inv H root srcLen depth len)) hd

theorem runDbl_ok {cfg : Config} {H : Heap} (hH : HeapWF H) {root srcLen depth len : Nat}
    {r : P2} (h : runDbl cfg H (init2 root srcLen depth len) = .ok r) :
    r.ti = (flatSpec H root srcLen depth).length ∧
      r.buf = (flatSpec H root srcLen depth).map some ++
        List.replicate (len - (flatSpec H root srcLen depth).length) none := by
  obtain ⟨t, ht, hd⟩ := run_ok h
  exact stepDbl_done (ht.invariant (stepDbl_inv hH) (init2_inv H root srcLen depth len)) hd

theorem runGen_ne_ub {cfg : Config} {H : Heap} (hH : HeapWF H) (s : P2) :
    runGen cfg H s ≠ .ub := by
  intro h
  obtain ⟨t, _, ht⟩ := run_ub h
  exact stepGen_ne_ub hH t ht

theorem runDbl_ne_ub {cfg : Config} {H : Heap} (hH : HeapWF H) {root srcLen depth len : Nat}
    (hL : ∀ v ∈ flatSpec H root srcLen depth, v.isNumber = true) :
    runDbl cfg H (init2 root srcLen depth len) ≠ .ub := by
  intro h
  obtain ⟨t, hr, ht⟩ := run_ub h
  exact stepDbl_ne_ub hH hL t (hr.invariant (stepDbl_inv hH) (init2_inv H root srcLen depth len)) ht

theorem conforms_kind {k : Kind} {L : List Val} (h : Conforms k L) :
    (k = .packedSmi ∨ k = .packedDouble ∨ k = .packedElem) ∧
      ∀ x ∈ L.map some, kindOk k x = true := by
  cases k with
  | packedSmi =>
    refine ⟨Or.inl rfl, ?_⟩
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    simpa [kindOk] using h v hv
  | packedDouble =>
    refine ⟨Or.inr (Or.inl rfl), ?_⟩
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    simpa [kindOk] using h v hv
  | packedElem =>
    refine ⟨Or.inr (Or.inr rfl), ?_⟩
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨v, _, rfl⟩ := hx
    rfl
  | _ => exact absurd h id

theorem result_wf {k : Kind} {L : List Val} (h : Conforms k L) :
    (⟨k, true, true, true, false, L.length, L.map some⟩ : JSArr).WF := by
  obtain ⟨hk, hok⟩ := conforms_kind h
  refine ⟨by simp, ?_, ?_, fun _ => rfl, fun _ => rfl, fun h => by cases h⟩
  · intro x hx
    simp only [JSArr.elems] at hx
    exact hok x (List.mem_of_mem_take hx)
  · intro _
    rcases hk with rfl | rfl | rfl <;> rfl

theorem flatSpec_zero {cfg : Config} {H : Heap} (hH : HeapWF H) {root srcLen depth : Nat}
    {k : Kind} (h : calcLength cfg H root srcLen depth = .ok (0, k)) :
    flatSpec H root srcLen depth = [] := by
  rcases (calcLength_ok hH h).2 with ⟨h0, _⟩ | ⟨_, h0⟩
  · exact List.eq_nil_of_length_eq_zero h0.symm
  · subst h0
    simp [flatSpec, leaves_nil]

theorem finish_ok {len : Nat} {k : Kind} {o : Outcome P2} {A : JSArr} {L : List Val}
    (hfin : finish len k o = .ok A)
    (hspec : ∀ r, o = .ok r → r.ti = L.length ∧
      r.buf = L.map some ++ List.replicate (len - L.length) none) :
    A = ⟨k, true, true, true, false, L.length, L.map some⟩ := by
  cases o with
  | ok r =>
    simp only [finish] at hfin
    split at hfin
    · rename_i hti
      cases hfin
      obtain ⟨h1, h2⟩ := hspec r rfl
      rw [h2, ← hti, h1]
      simp
    · cases hfin
  | _ => simp [finish] at hfin

theorem tryFastFlat_ok {cfg : Config} {H : Heap} (hH : HeapWF H) {root srcLen depth : Nat}
    {A : JSArr} (h : tryFastFlat cfg H root srcLen depth = .ok A) :
    A.WF ∧ (A.kind = .packedSmi ∨ A.kind = .packedDouble ∨ A.kind = .packedElem) ∧
      A.length = A.store.length ∧ A.store = (flatSpec H root srcLen depth).map some := by
  unfold tryFastFlat at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · rename_i len k hc
    have hconf := (calcLength_ok hH hc).1
    split at h
    · rename_i h0
      subst h0
      cases h
      rw [flatSpec_zero hH hc]
      exact ⟨⟨by simp, by simp [JSArr.elems], fun _ => rfl, fun _ => rfl, fun _ => rfl,
        fun h => by cases h⟩, Or.inl rfl, rfl, rfl⟩
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · have hA := finish_ok h (fun r hr => runDbl_ok hH hr)
      subst hA
      exact ⟨result_wf hconf, (conforms_kind hconf).1, by simp, rfl⟩
    · have hA := finish_ok h (fun r hr => runGen_ok hH hr)
      subst hA
      exact ⟨result_wf hconf, (conforms_kind hconf).1, by simp, rfl⟩
  all_goals cases h

theorem finish_ne_ub {len : Nat} {k : Kind} {o : Outcome P2} (h : o ≠ .ub) :
    finish len k o ≠ .ub := by
  unfold finish
  split
  · split <;> simp
  all_goals simp_all

theorem finish_ne_fatal {len : Nat} {k : Kind} {o : Outcome P2} (h : o ≠ .fatal) :
    finish len k o ≠ .fatal := by
  unfold finish
  split
  · split <;> simp
  all_goals simp_all

theorem tryFastFlat_ne_ub {cfg : Config} {H : Heap} (hH : HeapWF H) (root srcLen depth : Nat) :
    tryFastFlat cfg H root srcLen depth ≠ .ub := by
  unfold tryFastFlat
  split
  · simp
  split
  · simp
  split
  · rename_i len k hc
    have hconf := (calcLength_ok hH hc).1
    split
    · simp
    split
    · simp
    split
    · simp
    split
    · rename_i hk
      subst hk
      exact finish_ne_ub (runDbl_ne_ub hH hconf)
    · exact finish_ne_ub (runGen_ne_ub hH _)
  · simp
  · simp
  · rename_i hc
    exact absurd hc (calcLength_ne_ub hH root srcLen depth)
  · simp

theorem tryFastFlat_ne_fatal {cfg : Config} {H : Heap} (hH : HeapWF H) {root srcLen depth : Nat}
    (hStale : ((H root).kind = .packedSmi ∨ (H root).kind = .packedDouble) →
      srcLen ≤ cfg.maxLen) :
    tryFastFlat cfg H root srcLen depth ≠ .fatal := by
  unfold tryFastFlat
  split
  · simp
  split
  · simp
  split
  · rename_i len k hc
    split
    · simp
    split
    · rename_i hgt
      rcases (calcLength_ok hH hc).2 with ⟨_, hle⟩ | ⟨hk, rfl⟩
      · omega
      · have := hStale hk
        omega
    split
    · simp
    split
    · exact finish_ne_fatal (run_ne_fatal _ _ _ _)
    · exact finish_ne_fatal (run_ne_fatal _ _ _ _)
  · simp
  · simp
  · simp
  · rename_i hc
    exact absurd hc (calcLength_ne_fatal cfg H root srcLen depth)

end ArrayFlat
