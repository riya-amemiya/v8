import ArrayFlatMap.Model

namespace ArrayFlatMap

open Torque ArrayWitness

theorem innerLoop_eq {e : JSArr} (hw : e.WF) :
    ∀ ks : List Nat, (∀ k ∈ ks, k < e.length) →
      innerLoop e ks = some (ks.flatMap fun k => (e.elems.getD k none).toList)
  | [], _ => rfl
  | k :: ks, h => by
    have hk := h k (by simp)
    have hs : k < e.store.length := Nat.lt_of_lt_of_le hk hw.length_le
    rw [innerLoop, innerLoad, ite_eq_left hk, List.getElem?_eq_getElem hs]
    dsimp only
    rw [innerLoop_eq hw ks (fun j hj => h j (by simp [hj]))]
    simp only [List.flatMap_cons]
    congr 2
    simp [JSArr.elems, List.getD_eq_getElem?_getD, hk, List.getElem?_eq_getElem hs]

theorem flatMap_getD_filterMap (xs : List (Option Val)) :
    ((List.range' 0 xs.length).flatMap fun k => (xs.getD k none).toList) = xs.filterMap id := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons, List.range'_succ, List.flatMap_cons]
    have : ((List.range' 1 xs.length).flatMap fun k => ((x :: xs).getD k none).toList) =
        (List.range' 0 xs.length).flatMap fun k => (xs.getD k none).toList := by
      rw [List.range'_eq_map_range, List.range'_eq_map_range, List.flatMap_map, List.flatMap_map]
      congr 1
      funext k
      simp [List.getD_eq_getElem?_getD, Nat.add_comm]
    rw [this, ih]
    cases x <;> simp [List.getD_eq_getElem?_getD]

theorem innerFlatten_eq {e : JSArr} (hw : e.WF) : innerFlatten e = some (e.elems.filterMap id) := by
  unfold innerFlatten
  split
  · rw [innerLoop_eq hw (forward e.length) (fun k hk => by simpa [forward] using hk)]
    have := flatMap_getD_filterMap e.elems
    rw [JSArr.elems_length hw] at this
    simpa [forward] using this
  · rfl

theorem appended_eq {m : Mapped} (hm : MappedOK m) : appended m = some (specAppended m) := by
  cases m with
  | value v => rfl
  | array e => exact innerFlatten_eq hm
  | proxy vals => rfl

def CallbackFits (cb : Callback) : Prop := ∀ k v a, MappedOK (cb k v a).res

theorem sim {K : Kind} {cb : Callback} (hcb : CallbackOk K cb) (hf : CallbackFits cb) :
    Sim K (body cb) (specBody cb) (fun s => .done s.acc) (fun out _ => out) (fun _ => Eq) Eq where
  step := by
    intro k ks acc b a hr hw hk _
    subst hr
    cases hg : get a k with
    | none => exact ⟨rfl, rfl, inv_same hw hk _⟩
    | some v =>
      simp only [body, specBody, appended_eq (hf k v a)]
      exact ⟨rfl, rfl, inv_post hcb k v a _⟩
  fin := fun _ _ hr => hr

theorem fastFlatMap_safe {smiMax : Nat} {cb : Callback} {a : JSArr} (hw : a.WF)
    (hcb : CallbackOk a.kind cb) (hf : CallbackFits cb) :
    fastFlatMap smiMax cb a ≠ .fatal ∧ fastFlatMap smiMax cb a ≠ .ub := by
  unfold fastFlatMap
  split
  · exact ⟨nofun, nofun⟩
  have hs := sim hcb hf
  split
  · exact ⟨nofun, nofun⟩
  · exact ⟨nofun, nofun⟩
  · rename_i h
    exact absurd h (loop_ne_fatal hs (b := []) (inv_start hw []) rfl)
  · rename_i h
    exact absurd h (loop_ne_ub hs (b := []) (inv_start hw []) rfl)

theorem fastFlatMap_done {smiMax : Nat} {cb : Callback} {a : JSArr} {r : List Val} (hw : a.WF)
    (hcb : CallbackOk a.kind cb) (hf : CallbackFits cb) (h : fastFlatMap smiMax cb a = .done r) :
    r = specFlatMap cb a := by
  unfold fastFlatMap at h
  split at h
  · cases h
  split at h
  · rename_i r' hd
    cases h
    exact loop_done (sim hcb hf) (b := []) (inv_start hw []) rfl hd
  · cases h
  · cases h
  · cases h

theorem fastFlatMap_bailout {smiMax : Nat} {cb : Callback} {a arr : JSArr} {ks : List Nat}
    {out : List Val} (hw : a.WF) (hcb : CallbackOk a.kind cb) (hf : CallbackFits cb)
    (h : fastFlatMap smiMax cb a = .bailout ks out arr) :
    ∃ k, k ≤ a.length ∧ ks = List.range' k (a.length - k) ∧
      Reaches (specBody cb) (forward a.length) [] a ks out arr ∧
      spec (specBody cb) (fun out _ => out) ks out arr = specFlatMap cb a := by
  unfold fastFlatMap at h
  split at h
  · cases h
    exact ⟨0, Nat.zero_le _, rfl, .refl _ _ _, rfl⟩
  split at h
  · cases h
  · rename_i ks' s hb
    cases h
    obtain ⟨k, b', hk, hks, hreach, hR, _⟩ :=
      forward_bailout (sim hcb hf) (b := []) (inv_start hw []) rfl hb
    subst hR
    exact ⟨k, hk, hks, hreach, (Reaches.spec_eq hreach).symm⟩
  · cases h
  · cases h

end ArrayFlatMap
