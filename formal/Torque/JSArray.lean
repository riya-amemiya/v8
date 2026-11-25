import Torque.ElementsKind

namespace Torque

structure JSArr where
  kind : Kind
  forRead : Bool
  fast : Bool
  forCopy : Bool
  cow : Bool
  length : Nat
  store : List (Option Val)
  deriving Repr

def JSArr.elems (a : JSArr) : List (Option Val) := a.store.take a.length

structure JSArr.WF (a : JSArr) : Prop where
  length_le : a.length ≤ a.store.length
  kind_ok : ∀ x ∈ a.elems, kindOk a.kind x = true
  forRead_fast : a.forRead = true → a.kind.isFast = true
  fast_forRead : a.fast = true → a.forRead = true
  forCopy_fast : a.forCopy = true → a.fast = true
  cow_not_double : a.cow = true → a.kind.isDouble = false

abbrev Heap := Nat → JSArr

def HeapWF (H : Heap) : Prop := ∀ p, (H p).WF

structure Config where
  smiMax : Nat
  maxLen : Nat

theorem map_some_filterMap_id :
    ∀ l : List (Option Val), (∀ x ∈ l, x ≠ none) → (l.filterMap id).map some = l
  | [], _ => rfl
  | x :: l, hl => by
    cases x with
    | none => exact absurd rfl (hl none (by simp))
    | some v =>
      simp only [List.filterMap_cons, id, List.map_cons]
      rw [map_some_filterMap_id l (fun y hy => hl y (by simp [hy]))]

theorem length_filterMap_id_of_all_some (l : List (Option Val)) (hl : ∀ x ∈ l, x ≠ none) :
    (l.filterMap id).length = l.length := by
  have := congrArg List.length (map_some_filterMap_id l hl)
  simpa using this

theorem mem_filterMap_id {v : Val} {l : List (Option Val)} :
    v ∈ l.filterMap id ↔ some v ∈ l := by
  simp

theorem JSArr.elems_length {a : JSArr} (hw : a.WF) : a.elems.length = a.length := by
  simp [JSArr.elems, List.length_take]
  exact Nat.min_eq_left hw.length_le

theorem packedSmi_elem {a : JSArr} (hw : a.WF) (hk : a.kind = .packedSmi) {x : Option Val}
    (hx : x ∈ a.elems) : ∃ v, x = some v ∧ v.isSmi = true := by
  have := hw.kind_ok x hx
  rw [hk] at this
  cases x with
  | none => simp [kindOk] at this
  | some v => exact ⟨v, rfl, by simpa [kindOk] using this⟩

theorem packedDouble_elem {a : JSArr} (hw : a.WF) (hk : a.kind = .packedDouble)
    {x : Option Val} (hx : x ∈ a.elems) : ∃ v, x = some v ∧ v.isNumber = true := by
  have := hw.kind_ok x hx
  rw [hk] at this
  cases x with
  | none => simp [kindOk] at this
  | some v => exact ⟨v, rfl, by simpa [kindOk] using this⟩

theorem numeric_elems {a : JSArr} (hw : a.WF)
    (hk : a.kind = .packedSmi ∨ a.kind = .packedDouble) :
    ∀ x ∈ a.elems, ∃ v, x = some v ∧ v.isNumber = true := by
  intro x hx
  rcases hk with hk | hk
  · obtain ⟨v, rfl, hv⟩ := packedSmi_elem hw hk hx
    exact ⟨v, rfl, isNumber_of_isSmi hv⟩
  · exact packedDouble_elem hw hk hx

theorem numeric_elems_some {a : JSArr} (hw : a.WF)
    (hk : a.kind = .packedSmi ∨ a.kind = .packedDouble) : ∀ x ∈ a.elems, x ≠ none := by
  intro x hx
  obtain ⟨v, rfl, _⟩ := numeric_elems hw hk x hx
  simp

end Torque
