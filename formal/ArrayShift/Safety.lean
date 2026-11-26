import ArrayShift.Model

namespace ArrayShift

open Torque InPlace

theorem shiftElements_ok {b : JSArr} (hl : b.length ≤ b.store.length) (hcow : b.cow = false)
    (hpos : 0 < b.length) :
    shiftElements b = .ok (b.store.getD 0 none,
      (moveElements b.store 0 1 (b.length - 1)).set (b.length - 1) none) := by
  have hne : b.store ≠ [] := by
    intro h
    rw [h] at hl
    simp at hl
    omega
  have hml : (moveElements b.store 0 1 (b.length - 1)).length = b.store.length :=
    length_moveElements (by omega)
  have hne' : moveElements b.store 0 1 (b.length - 1) ≠ [] := by
    intro h
    rw [h] at hml
    simp at hml
    omega
  unfold shiftElements
  rw [castElements_ok (fun _ => hne), Res.ok_bind,
    show ((0 : Int)) = ((0 : Nat) : Int) from rfl, loadSlot_nat (by omega), Res.ok_bind,
    Res.ok_bind, hcow, memmove_ok (by omega) (by omega),
    Res.ok_bind, castElements_ok (fun _ => hne'), Res.ok_bind, storeSlot_nat (by omega),
    Res.ok_bind]
  rfl

theorem tryFast_eq {c : Config} {m : MapInfo} {a : JSArr} (hw : a.WF)
    (hcap : a.store.length ≤ c.maxLen) (hc : c.maxLen ≤ c.smiMax) (hf : a.fast = true)
    (hp : m.pushable = true) :
    tryFast c m a =
      let b := ensureWritable a
      if b.length = 0 then .done b .undef
      else if 2 * (b.length - 1) + kMinAddedElementsCapacity < b.store.length then .slow
      else if kMaxCopyElements < b.length - 1 then .slow
      else .done { b with
          length := b.length - 1
          store := (moveElements b.store 0 1 (b.length - 1)).set (b.length - 1) none }
        ((b.store.getD 0 none).getD .undef) := by
  have hew := ensureWritable_wf hw
  unfold tryFast
  rw [ite_eq_right (by simp [hf]), ite_eq_right (by simp [hp]), ensureWritableChecked_ok hw hcap hc,
    Res.ok_then]
  dsimp only
  split
  · rfl
  split
  · rfl
  split
  · rfl
  rename_i h0 _ _
  rw [shiftElements_ok hew.length_le (ensureWritable_cow a) (by omega), Res.ok_then]

theorem tryFast_cases {c : Config} {m : MapInfo} {a : JSArr} (hw : a.WF) :
    tryFast c m a = .slow ∨ tryFast c m a = .abort ∨
      (a.fast = true ∧ m.pushable = true ∧ ensureWritableChecked c a = .ok (ensureWritable a) ∧
        tryFast c m a =
          let b := ensureWritable a
          if b.length = 0 then .done b .undef
          else if 2 * (b.length - 1) + kMinAddedElementsCapacity < b.store.length then .slow
          else if kMaxCopyElements < b.length - 1 then .slow
          else .done { b with
              length := b.length - 1
              store := (moveElements b.store 0 1 (b.length - 1)).set (b.length - 1) none }
            ((b.store.getD 0 none).getD .undef)) := by
  have hew := ensureWritable_wf hw
  unfold tryFast
  cases hf : a.fast
  · left
    rfl
  cases hp : m.pushable
  · left
    rfl
  rcases ensureWritableChecked_cases c a with h | h
  · right
    left
    rw [h]
    rfl
  · right
    right
    refine ⟨rfl, rfl, h, ?_⟩
    rw [ite_eq_right (by decide), ite_eq_right (by decide), h, Res.ok_then]
    dsimp only
    split
    · rfl
    split
    · rfl
    split
    · rfl
    rename_i h0 _ _
    rw [shiftElements_ok hew.length_le (ensureWritable_cow a) (by omega), Res.ok_then]

theorem tryFast_ne_ub {c : Config} {m : MapInfo} {a : JSArr} (hw : a.WF) :
    tryFast c m a ≠ .ub := by
  rcases tryFast_cases (c := c) (m := m) hw with h | h | ⟨_, _, _, h⟩ <;> rw [h]
  · nofun
  · nofun
  · dsimp only
    split
    · nofun
    split
    · nofun
    split
    · nofun
    · nofun

theorem tryFast_ne_abort {c : Config} {m : MapInfo} {a : JSArr} (hw : a.WF)
    (hcap : a.store.length ≤ c.maxLen) (hc : c.maxLen ≤ c.smiMax) : tryFast c m a ≠ .abort := by
  cases hf : a.fast
  · unfold tryFast
    rw [ite_eq_left hf]
    nofun
  cases hp : m.pushable
  · unfold tryFast
    rw [ite_eq_right (by simp [hf]), ite_eq_left hp]
    nofun
  rw [tryFast_eq hw hcap hc hf hp]
  dsimp only
  split
  · nofun
  split
  · nofun
  split
  · nofun
  · nofun

theorem shifted_props {b : JSArr} (hw : b.WF) (hsl : b.SlackHoles) (hcow : b.cow = false)
    (hpos : 0 < b.length) :
    let b' : JSArr := { b with
      length := b.length - 1
      store := (moveElements b.store 0 1 (b.length - 1)).set (b.length - 1) none }
    b'.cow = false ∧ b'.kind = b.kind ∧ b'.length = b.length - 1 ∧ b'.WF ∧ b'.SlackHoles ∧
      (b'.elems, (b.store.getD 0 none).getD .undef) = specShift b.elems := by
  have hl := hw.length_le
  have hml : (moveElements b.store 0 1 (b.length - 1)).length = b.store.length :=
    length_moveElements (by omega)
  have hget : ∀ j, ((moveElements b.store 0 1 (b.length - 1)).set (b.length - 1) none)[j]? =
      if j < b.length - 1 then b.store[j + 1]?
      else if j = b.length - 1 then some none else b.store[j]? := by
    intro j
    rw [List.getElem?_set, getElem?_moveElements (by omega) (by omega)]
    by_cases h1 : j < b.length - 1
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left h1]
      congr 1
      omega
    · by_cases h2 : j = b.length - 1
      · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right h1, ite_eq_left h2]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h1, ite_eq_right h2]
  obtain ⟨first, rest, hfr⟩ : ∃ first rest, b.elems = first :: rest := by
    cases he : b.elems with
    | nil =>
      have := JSArr.elems_length hw
      rw [he] at this
      simp at this
      omega
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hfirst : b.store.getD 0 none = first := by
    have : b.elems[0]? = some first := by rw [hfr]; rfl
    simp only [JSArr.elems, List.getElem?_take] at this
    rw [ite_eq_left hpos] at this
    rw [List.getD_eq_getElem?_getD, this]
    rfl
  have hrest : ∀ j, rest[j]? = if j < b.length - 1 then b.store[j + 1]? else none := by
    intro j
    have : rest[j]? = b.elems[j + 1]? := by rw [hfr]; rfl
    rw [this]
    simp only [JSArr.elems, List.getElem?_take]
    by_cases hj : j < b.length - 1
    · rw [ite_eq_left (by omega), ite_eq_left hj]
    · rw [ite_eq_right (by omega), ite_eq_right hj]
  have helems : ({ b with
      length := b.length - 1
      store := (moveElements b.store 0 1 (b.length - 1)).set (b.length - 1) none } : JSArr).elems =
      rest := by
    apply List.ext_getElem?
    intro j
    show (List.take (b.length - 1) _)[j]? = _
    rw [List.getElem?_take, hget, hrest]
    by_cases hj : j < b.length - 1
    · rw [ite_eq_left hj, ite_eq_left hj, ite_eq_left hj]
    · rw [ite_eq_right hj, ite_eq_right hj]
  refine ⟨hcow, rfl, rfl, ⟨?_, ?_, hw.forRead_fast, hw.fast_forRead, hw.forCopy_fast,
    hw.cow_not_double⟩, ?_, ?_⟩
  · show b.length - 1 ≤ (List.set _ _ _).length
    rw [List.length_set, hml]
    omega
  · intro x hx
    rw [helems] at hx
    apply hw.kind_ok
    rw [hfr]
    exact List.mem_cons_of_mem _ hx
  · intro x hx
    change x ∈ (List.set _ _ _).drop (b.length - 1) at hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    rw [List.getElem?_drop, hget, ite_eq_right (by omega)] at hi
    by_cases h0 : i = 0
    · rw [ite_eq_left (by omega)] at hi
      exact (Option.some.inj hi).symm
    · rw [ite_eq_right (by omega)] at hi
      apply hsl x
      apply List.mem_iff_getElem?.mpr
      refine ⟨i - 1, ?_⟩
      rw [List.getElem?_drop]
      rw [show b.length + (i - 1) = b.length - 1 + i by omega]
      exact hi
  · rw [helems, hfr, hfirst]
    rfl

theorem tryFast_done {c : Config} {m : MapInfo} {a a' : JSArr} {r : Val} (hw : a.WF)
    (hsl : a.SlackHoles) (h : tryFast c m a = .done a' r) :
    a'.cow = false ∧ a'.kind = a.kind ∧ a'.length = a.length - 1 ∧ a'.WF ∧ a'.SlackHoles ∧
      (a'.elems, r) = specShift a.elems := by
  have hew := ensureWritable_wf hw
  have hesl := ensureWritable_slack hsl
  have hk := ensureWritable_kind a
  have hl := ensureWritable_length a
  have he := ensureWritable_elems a
  rcases tryFast_cases (c := c) (m := m) hw with h' | h' | ⟨_, _, _, h'⟩ <;> rw [h'] at h
  · cases h
  · cases h
  dsimp only at h
  split at h
  · rename_i h0
    cases h
    refine ⟨ensureWritable_cow a, hk, by omega, hew, hesl, ?_⟩
    have : (ensureWritable a).elems = [] := by
      have := JSArr.elems_length hew
      rw [h0] at this
      exact List.eq_nil_of_length_eq_zero this
    rw [← he, this]
    rfl
  split at h
  · cases h
  split at h
  · cases h
  rename_i h0 _ _
  cases h
  obtain ⟨hcw, hk', hl', hwf, hs, hspec⟩ :=
    shifted_props hew hesl (ensureWritable_cow a) (by omega)
  refine ⟨hcw, hk'.trans hk, hl'.trans (by rw [hl]), hwf, hs, ?_⟩
  rw [← he]
  exact hspec

theorem tryFast_handles {c : Config} {m : MapInfo} {a : JSArr} (hw : a.WF)
    (hcap : a.store.length ≤ c.maxLen) (hc : c.maxLen ≤ c.smiMax) (hf : a.fast = true)
    (hp : m.pushable = true) (hshort : a.length ≤ kMaxCopyElements + 1)
    (htrim : a.store.length ≤ 2 * (a.length - 1) + kMinAddedElementsCapacity) :
    ∃ a' r, tryFast c m a = .done a' r := by
  rw [tryFast_eq hw hcap hc hf hp]
  have hst := ensureWritable_store_length a
  have hl := ensureWritable_length a
  dsimp only
  split
  · exact ⟨_, _, rfl⟩
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  exact ⟨_, _, rfl⟩

end ArrayShift
