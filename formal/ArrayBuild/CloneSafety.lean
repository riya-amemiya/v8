import ArrayBuild.Clone

namespace ArrayBuild

open Torque

theorem map_holeToUndef_of_no_hole {xs : List (Option Val)} (h : xs.any (· == none) = false) :
    xs.map holeToUndef = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | none => simp at h
    | some v =>
      simp only [List.any_cons, Bool.or_eq_false_iff] at h
      simp only [List.map_cons, holeToUndef, ih h.2]

theorem mem_map_holeToUndef {xs : List (Option Val)} {x : Option Val}
    (h : x ∈ xs.map holeToUndef) : x ≠ none := by
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp h
  cases y <;> simp [holeToUndef]

theorem packed_no_hole {a : JSArr} (hw : a.WF) (hf : a.kind.isFast = true)
    (hh : a.kind.isHoley = false) : ∀ x ∈ a.elems, x ≠ none := by
  intro x hx hn
  have := hw.kind_ok x hx
  rw [hn] at this
  cases hk : a.kind <;> simp_all [Kind.isHoley, Kind.isFast, kindOk]

theorem clone_ne_ub {c : Bool} {a : JSArr} (hw : a.WF) : cloneFastJSArray c a ≠ .ub := by
  have hl := hw.length_le
  unfold cloneFastJSArray
  split
  · nofun
  split
  · rw [ite_eq_right (by omega)]
    nofun
  split
  · nofun
  rw [ite_eq_right (by omega)]
  nofun

theorem drop_nil_of_length {xs : List (Option Val)} {n : Nat} (h : xs.length = n) :
    ∀ x ∈ xs.drop n, x = none := by
  intro x hx
  rw [List.drop_eq_nil_of_le (by omega)] at hx
  simp at hx

structure Cloned (c : Bool) (a a' : JSArr) : Prop where
  wf : a'.WF
  slack : a'.SlackHoles
  elems : a'.elems = cloneElems c a
  length : a'.length = a.length
  forRead : a'.forRead = true
  fast : a'.fast = true
  cow : a'.cow = true → a.cow = true

theorem clone_spec {c : Bool} {a a' : JSArr} (hw : a.WF) (hsl : a.SlackHoles)
    (hr : a.forRead = true) (hf : c = false → a.fast = true)
    (h : cloneFastJSArray c a = .done a') : Cloned c a a' := by
  have hl := hw.length_le
  have hfast : a.kind.isFast = true := hw.forRead_fast hr
  have helen : a.elems.length = a.length := JSArr.elems_length hw
  have hkind : ∀ conv : Bool, (cloneKind a conv).isFast = true := by
    intro conv
    unfold cloneKind
    split
    · rfl
    · exact hfast
  have hplain : ¬(c = true ∧ a.kind.isHoley = true) → ∀ x ∈ a.elems,
      kindOk (cloneKind a false) x = true := by
    intro hn x hx
    unfold cloneKind
    by_cases hfa : a.fast = false
    · rw [ite_eq_left (Or.inr hfa)]
      have hc : c = true := by
        cases hc : c
        · rw [hf hc] at hfa
          exact absurd hfa (by decide)
        · rfl
      have hh : a.kind.isHoley = false := by
        cases hk : a.kind.isHoley
        · rfl
        · exact absurd ⟨hc, hk⟩ hn
      have := packed_no_hole hw hfast hh x hx
      cases x with
      | none => exact absurd rfl this
      | some v => rfl
    · rw [ite_eq_right (by simpa using hfa)]
      exact hw.kind_ok x hx
  have hwf : ∀ (k : Kind) (cw : Bool) (n : Nat) (st : List (Option Val)),
      n ≤ st.length → k.isFast = true → (cw = true → k.isDouble = false) →
      (∀ x ∈ st.take n, kindOk k x = true) →
      (⟨k, true, true, a.forCopy, cw, n, st⟩ : JSArr).WF := by
    intro k cw n st hst hk hcw hok
    exact {
      length_le := hst
      kind_ok := hok
      forRead_fast := fun _ => hk
      fast_forRead := fun _ => rfl
      forCopy_fast := fun _ => rfl
      cow_not_double := hcw }
  unfold cloneFastJSArray at h
  split at h
  · rename_i h0
    cases h
    have hz : a.elems = [] := by
      rw [← List.length_eq_zero_iff, helen, h0]
    refine ⟨?_, ?_, ?_, h0.symm, rfl, rfl, fun h => by cases h⟩
    · exact hwf _ false 0 [] (by omega) (hkind false) nofun (by simp)
    · exact drop_nil_of_length rfl
    · show List.take 0 [] = cloneElems c a
      unfold cloneElems
      split <;> simp [hz]
  split at h
  · rename_i _ hch
    rw [ite_eq_right (by omega)] at h
    cases h
    have hst : (a.elems.map holeToUndef).length = a.length := by simp [helen]
    have htake : (a.elems.map holeToUndef).take a.length = a.elems.map holeToUndef := by
      rw [List.take_of_length_le (by omega)]
    refine ⟨?_, drop_nil_of_length hst, ?_, rfl, rfl, rfl, fun h => by cases h⟩
    · refine hwf _ false _ _ (by omega) (hkind _) nofun ?_
      rw [htake]
      intro x hx
      unfold cloneKind
      by_cases hconv : a.elems.any (· == none) = true ∨ a.fast = false
      · rw [ite_eq_left hconv]
        cases x with
        | none => exact absurd rfl (mem_map_holeToUndef hx)
        | some v => rfl
      · rw [ite_eq_right hconv]
        have hno : a.elems.any (· == none) = false := by
          cases hany : a.elems.any (· == none)
          · rfl
          · exact absurd (Or.inl hany) hconv
        rw [map_holeToUndef_of_no_hole hno] at hx
        exact hw.kind_ok x hx
    · show List.take a.length _ = cloneElems c a
      unfold cloneElems
      rw [ite_eq_left hch, htake]
  · rename_i _ hch
    split at h
    · rename_i hcow
      cases h
      refine ⟨?_, hsl, ?_, rfl, rfl, rfl, fun _ => hcow⟩
      · refine hwf _ true _ _ hl (hkind false) ?_ (hplain hch)
        intro _
        unfold cloneKind
        split
        · rfl
        · exact hw.cow_not_double hcow
      · show a.elems = cloneElems c a
        unfold cloneElems
        rw [ite_eq_right hch]
    · rw [ite_eq_right (by omega)] at h
      cases h
      have htake : a.elems.take a.length = a.elems := by
        rw [List.take_of_length_le (by omega)]
      refine ⟨?_, drop_nil_of_length helen, ?_, rfl, rfl, rfl, fun h => by cases h⟩
      · refine hwf _ false _ _ (by omega) (hkind false) nofun ?_
        rw [htake]
        exact hplain hch
      · show a.elems.take a.length = cloneElems c a
        unfold cloneElems
        rw [ite_eq_right hch, htake]

end ArrayBuild
