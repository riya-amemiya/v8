import ArrayFrom.Model

namespace ArrayFrom

open Torque ArrayBuild

def CreateOK (create : Nat → JSArr) : Prop :=
  ∀ n, (create n).WF ∧ (create n).SlackHoles ∧ (create n).length = n

def EmptyOK (a0 : JSArr) : Prop := a0.WF ∧ a0.SlackHoles ∧ a0.length = 0

theorem any_hole_false {xs : List (Option Val)} (h : ∀ x ∈ xs, x ≠ none) :
    xs.any (· == none) = false := by
  rw [List.any_eq_false]
  intro x hx
  have := h x hx
  cases x <;> simp_all

theorem fromFastArray_spec {a : JSArr} (hw : a.WF) (hsl : a.SlackHoles) (hr : a.forRead = true) :
    ∃ a', fromFastArray a = .done a' ∧ a'.WF ∧ a'.SlackHoles ∧ a'.elems = iterated a ∧
      a'.length = a.length := by
  cases hc : cloneFastJSArray true a with
  | ub => exact absurd hc (clone_ne_ub hw)
  | done a' =>
    have hs := clone_spec (c := true) hw hsl hr (fun h => by cases h) hc
    refine ⟨a', by simp [fromFastArray, hc, ofClone], hs.wf, hs.slack, ?_, hs.length⟩
    rw [hs.elems]
    unfold cloneElems iterated
    split
    · rfl
    · rename_i hn
      have hh : a.kind.isHoley = false := by
        cases hk : a.kind.isHoley
        · rfl
        · exact absurd ⟨rfl, hk⟩ hn
      rw [map_holeToUndef_of_no_hole (any_hole_false (packed_no_hole hw (hw.forRead_fast hr) hh))]

theorem writeAt_step {n m : Nat} (hm : 0 < m) :
    writeAt (List.replicate n (some Val.other) ++ List.replicate m none) n =
      some (List.replicate (n + 1) (some Val.other) ++ List.replicate (m - 1) none) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold writeAt
  rw [ite_eq_left (by simp)]
  rw [List.set_append_right _ _ (by simp), List.length_replicate, Nat.sub_self,
    List.replicate_succ (n := m'), List.set_cons_zero, Nat.add_sub_cancel,
    List.replicate_succ' (n := n), List.append_assoc, List.singleton_append]

theorem codePoints_length_le : ∀ units : List Nat, (codePoints units).length ≤ units.length
  | [] => by simp [codePoints]
  | [u] => by simp [codePoints]
  | u :: w :: rest => by
    unfold codePoints
    split
    · have := codePoints_length_le rest
      simp only [List.length_cons]
      omega
    · have := codePoints_length_le (w :: rest)
      simp only [List.length_cons] at this ⊢
      omega

theorem stringLoop_spec :
    ∀ (units : List Nat) (n m : Nat) (out : List (List Nat)), units.length ≤ m →
      stringLoop units n (List.replicate n (some Val.other) ++ List.replicate m none) out =
        some (n + (codePoints units).length,
          List.replicate (n + (codePoints units).length) (some Val.other) ++
            List.replicate (m - (codePoints units).length) none,
          out ++ codePoints units)
  | [], n, m, out, _ => by simp [stringLoop, codePoints]
  | [u], n, m, out, h => by
    simp only [List.length_singleton] at h
    simp only [stringLoop, writeAt_step (show 0 < m by omega), Option.map_some, codePoints,
      List.length_singleton]
  | u :: w :: rest, n, m, out, h => by
    simp only [List.length_cons] at h
    simp only [stringLoop, writeAt_step (show 0 < m by omega)]
    unfold codePoints
    split
    · rw [stringLoop_spec rest (n + 1) (m - 1) _ (by omega)]
      have e1 : n + 1 + (codePoints rest).length = n + ((codePoints rest).length + 1) := by omega
      have e2 : m - 1 - (codePoints rest).length = m - ((codePoints rest).length + 1) := by omega
      simp only [List.length_cons, List.append_assoc, List.singleton_append, e1, e2]
    · rw [stringLoop_spec (w :: rest) (n + 1) (m - 1) _ (by simp only [List.length_cons]; omega)]
      have e1 : n + 1 + (codePoints (w :: rest)).length =
          n + ((codePoints (w :: rest)).length + 1) := by omega
      have e2 : m - 1 - (codePoints (w :: rest)).length =
          m - ((codePoints (w :: rest)).length + 1) := by omega
      simp only [List.length_cons, List.append_assoc, List.singleton_append, e1, e2]

theorem stringToList_spec (c : Config) (units : List Nat) :
    ∃ a, stringToList c units = (.done a, codePoints units) ∧ a.WF ∧ a.SlackHoles ∧
      a.length = (codePoints units).length ∧
      a.elems = List.replicate (codePoints units).length (some .other) := by
  have hle := codePoints_length_le units
  have h := stringLoop_spec units 0 units.length [] (Nat.le_refl _)
  simp only [List.replicate_zero, List.nil_append, Nat.zero_add] at h
  refine ⟨⟨.packedElem, c.noElements, c.noElements, false, false, (codePoints units).length,
    List.replicate (codePoints units).length (some Val.other) ++
      List.replicate (units.length - (codePoints units).length) none⟩,
    by simp only [stringToList, h], ?_, ?_, rfl, ?_⟩
  · refine ⟨by simp, ?_, fun _ => rfl, id, nofun, nofun⟩
    intro x hx
    simp only [JSArr.elems, List.take_append_of_le_length (by simp : (codePoints units).length ≤
      (List.replicate (codePoints units).length (some Val.other)).length),
      List.take_replicate, Nat.min_self] at hx
    rw [List.eq_of_mem_replicate hx]
    rfl
  · intro x hx
    simp only [List.drop_left' (List.length_replicate ..)] at hx
    exact List.eq_of_mem_replicate hx
  · simp only [JSArr.elems]
    rw [List.take_left' (List.length_replicate ..)]

theorem allocated_ok (c : Config) (n : Nat) : EmptyOK (allocated c n) := by
  refine ⟨⟨Nat.zero_le _, by simp [allocated, JSArr.elems], fun _ => rfl, id, nofun, nofun⟩,
    ?_, rfl⟩
  intro x hx
  simp only [allocated, List.drop_zero] at hx
  exact List.eq_of_mem_replicate hx

theorem fromIterable_spec {c : Config} {rt : JSArr → Nat → Val → JSArr} {ctor : Ctor}
    {a0 : JSArr} {values : List Val} (hrt : RuntimeOK rt) (h0 : EmptyOK a0)
    (hctor : ctor ≠ .otherConstructor) :
    ∃ a, fromIterable c rt ctor a0 values = .done a ∧ a.WF ∧ a.SlackHoles ∧
      a.elems = values.map some ∧ a.length = values.length := by
  obtain ⟨a, hrun, hw, hsl, he, hl⟩ := createLoop_ne (env := c.store) (vs := values) hrt h0.1 h0.2.1
    h0.2.2
  refine ⟨a, ?_, hw, hsl, he, hl⟩
  unfold fromIterable
  rw [ite_eq_right hctor, hrun]
  rfl

theorem fromArrayLike_spec {c : Config} {rt : JSArr → Nat → Val → JSArr} {ctor : Ctor}
    {create : Nat → JSArr} {values : List Val} (hrt : RuntimeOK rt) (hc : CreateOK create)
    (hctor : ctor ≠ .otherConstructor) :
    ∃ a, fromArrayLike c rt ctor create values = .done a ∧ a.WF ∧ a.SlackHoles ∧
      a.elems = values.map some ∧ a.length = values.length := by
  unfold fromArrayLike
  rw [ite_eq_right hctor]
  split
  · obtain ⟨a, hrun, hw, hsl, he, hl⟩ := createLoop_ne (env := c.store) (vs := values) hrt
      (allocated_ok c values.length).1 (allocated_ok c values.length).2.1
      (allocated_ok c values.length).2.2
    exact ⟨a, by rw [hrun]; rfl, hw, hsl, he, hl⟩
  · obtain ⟨hw, hsl, hl⟩ := hc values.length
    have he : (create values.length).elems =
        ([] : List Val).map some ++ (create values.length).elems := rfl
    obtain ⟨a, hrun, hw', hsl', he', hl'⟩ :=
      createLoop_spec (env := c.store) hrt values [] _ _ hw hsl he
    refine ⟨a, ?_, hw', hsl', ?_, ?_⟩
    · simp only [List.length_nil] at hrun
      rw [hrun]
      rfl
    · rw [he']
      have : (create values.length).elems.length = values.length := by
        rw [JSArr.elems_length hw, hl]
      simp [List.drop_eq_nil_of_le (Nat.le_of_eq this)]
    · rw [hl', hl]
      simp

end ArrayFrom
