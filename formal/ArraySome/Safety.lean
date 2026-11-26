import ArraySome.Model

namespace ArraySome

open Torque ArrayWitness

theorem sim {K : Kind} {cb : Callback} (hcb : CallbackOk K cb) :
    Sim K (body cb) (specBody cb) (fun _ => .done false) (fun _ _ => false) (fun _ _ _ => True)
      Eq where
  step := by
    intro k ks acc b a _ hw hk _
    cases get a k with
    | none => exact ⟨trivial, rfl, inv_same hw hk ()⟩
    | some v =>
      simp only [body, specBody]
      split
      · rfl
      · exact ⟨trivial, rfl, inv_post hcb k v a ()⟩
  fin := fun _ _ _ => rfl

theorem fastSome_safe {cfg : Config} {cb : Callback} {a : JSArr} (hw : a.WF)
    (hcb : CallbackOk a.kind cb) : fastSome cfg cb a ≠ .fatal ∧ fastSome cfg cb a ≠ .ub := by
  unfold fastSome
  split
  · exact ⟨nofun, nofun⟩
  split
  · exact ⟨nofun, nofun⟩
  exact ⟨loop_ne_fatal (sim hcb) (b := ()) (inv_start hw ()) trivial,
    loop_ne_ub (sim hcb) (b := ()) (inv_start hw ()) trivial⟩

theorem fastSome_done {cfg : Config} {cb : Callback} {a : JSArr} {r : Bool} (hw : a.WF)
    (hcb : CallbackOk a.kind cb) (h : fastSome cfg cb a = .done r) : r = specSome cb a := by
  unfold fastSome at h
  split at h
  · cases h
  split at h
  · cases h
  exact loop_done (sim hcb) (b := ()) (inv_start hw ()) trivial h

theorem fastSome_bailout {cfg : Config} {cb : Callback} {a : JSArr} {ks : List Nat}
    {s : St Unit} (hw : a.WF) (hcb : CallbackOk a.kind cb)
    (h : fastSome cfg cb a = .bailout ks s) :
    ∃ k, k ≤ a.length ∧ ks = List.range' k (a.length - k) ∧
      Reaches (specBody cb) (forward a.length) () a ks () s.arr ∧
      spec (specBody cb) (fun _ _ => false) ks () s.arr = specSome cb a := by
  unfold fastSome at h
  split at h
  · cases h
    exact ⟨0, Nat.zero_le _, rfl, .refl _ _ _, rfl⟩
  split at h
  · cases h
    exact ⟨0, Nat.zero_le _, rfl, .refl _ _ _, rfl⟩
  obtain ⟨k, _, hk, hks, hreach, _, _⟩ :=
    forward_bailout (sim hcb) (b := ()) (inv_start hw ()) trivial h
  exact ⟨k, hk, hks, hreach, (Reaches.spec_eq hreach).symm⟩

end ArraySome
