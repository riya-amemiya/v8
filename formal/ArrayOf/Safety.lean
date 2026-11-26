import ArrayOf.Model

namespace ArrayOf

open Torque ArrayBuild

def CreateOK (create : Nat → JSArr) : Prop :=
  ∀ n, (create n).WF ∧ (create n).SlackHoles ∧ (create n).length = n

theorem filledWithZero_ok (c : Config) (n : Nat) :
    (filledWithZero c n).WF ∧ (filledWithZero c n).SlackHoles ∧ (filledWithZero c n).length = n := by
  unfold filledWithZero
  split
  · rename_i h
    subst h
    refine ⟨⟨Nat.le_refl _, by simp [JSArr.elems], fun _ => rfl, id, nofun, nofun⟩, ?_, rfl⟩
    intro x hx
    simp at hx
  · refine ⟨⟨by simp, ?_, fun _ => rfl, id, nofun, nofun⟩, ?_, rfl⟩
    · intro x hx
      simp only [JSArr.elems, List.take_replicate, Nat.min_self] at hx
      rw [List.eq_of_mem_replicate hx]
      rfl
    · intro x hx
      rw [List.drop_eq_nil_of_le (by simp)] at hx
      simp at hx

theorem initial_ok {c : Config} {ctor : Ctor} {create : Nat → JSArr} (hc : CreateOK create)
    (n : Nat) :
    (initial c ctor create n).WF ∧ (initial c ctor create n).SlackHoles ∧
      (initial c ctor create n).length = n := by
  unfold initial
  split
  · exact filledWithZero_ok c n
  · exact hc n

theorem arrayOf_spec {c : Config} {rt : JSArr → Nat → Val → JSArr} {ctor : Ctor}
    {create : Nat → JSArr} {items : List Val} (hrt : RuntimeOK rt) (hc : CreateOK create)
    (hctor : ctor ≠ .otherConstructor) :
    ∃ a, arrayOf c rt ctor create items = .done a ∧ a.WF ∧ a.SlackHoles ∧
      a.elems = items.map some ∧ a.length = items.length := by
  obtain ⟨hw, hsl, hl⟩ := initial_ok (c := c) (ctor := ctor) hc items.length
  have he : (initial c ctor create items.length).elems =
      ([] : List Val).map some ++ (initial c ctor create items.length).elems := rfl
  obtain ⟨a, hrun, hw', hsl', he', hl'⟩ := createLoop_spec (env := c.store) hrt items [] _ _ hw hsl he
  refine ⟨a, ?_, hw', hsl', ?_, ?_⟩
  · unfold arrayOf
    rw [ite_eq_right hctor]
    simp only [List.length_nil] at hrun
    rw [hrun]
    rfl
  · rw [he']
    have : (initial c ctor create items.length).elems.length = items.length := by
      rw [JSArr.elems_length hw, hl]
    simp [List.drop_eq_nil_of_le (Nat.le_of_eq this)]
  · rw [hl', hl]
    simp

theorem arrayOf_safe {c : Config} {rt : JSArr → Nat → Val → JSArr} {ctor : Ctor}
    {create : Nat → JSArr} {items : List Val} (hrt : RuntimeOK rt) (hc : CreateOK create) :
    arrayOf c rt ctor create items ≠ .ub ∧ arrayOf c rt ctor create items ≠ .fatal := by
  by_cases hctor : ctor = .otherConstructor
  · unfold arrayOf
    rw [ite_eq_left hctor]
    exact ⟨nofun, nofun⟩
  · obtain ⟨a, h, _⟩ := arrayOf_spec (c := c) (items := items) hrt hc hctor
    rw [h]
    exact ⟨nofun, nofun⟩

end ArrayOf
