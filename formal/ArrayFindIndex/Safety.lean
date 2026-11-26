import ArrayFindIndex.Model

namespace ArrayFindIndex

open Torque ArrayWitness

theorem sim {K : Kind} {cb : Callback} (hcb : CallbackOk K cb) :
    Sim K (body cb) (specBody cb) (fun _ => .done (-1)) (fun _ _ => -1) (fun _ _ _ => True)
      Eq where
  step := by
    intro k ks acc b a _ _ _ _
    simp only [body, specBody]
    split
    · rfl
    · exact ⟨trivial, rfl, inv_post hcb k _ a ()⟩
  fin := fun _ _ _ => rfl

theorem fastFindIndex_safe {cfg : Config} {cb : Callback} {a : JSArr} (hw : a.WF)
    (hcb : CallbackOk a.kind cb) :
    fastFindIndex cfg cb a ≠ .fatal ∧ fastFindIndex cfg cb a ≠ .ub := by
  unfold fastFindIndex
  split
  · exact ⟨nofun, nofun⟩
  split
  · exact ⟨nofun, nofun⟩
  exact ⟨loop_ne_fatal (sim hcb) (b := ()) (inv_start hw ()) trivial,
    loop_ne_ub (sim hcb) (b := ()) (inv_start hw ()) trivial⟩

theorem fastFindIndex_done {cfg : Config} {cb : Callback} {a : JSArr} {r : Int} (hw : a.WF)
    (hcb : CallbackOk a.kind cb) (h : fastFindIndex cfg cb a = .done r) :
    r = specFindIndex cb a := by
  unfold fastFindIndex at h
  split at h
  · cases h
  split at h
  · cases h
  exact loop_done (sim hcb) (b := ()) (inv_start hw ()) trivial h

theorem fastFindIndex_bailout {cfg : Config} {cb : Callback} {a : JSArr} {ks : List Nat}
    {s : St Unit} (hw : a.WF) (hcb : CallbackOk a.kind cb)
    (h : fastFindIndex cfg cb a = .bailout ks s) :
    ∃ k, k ≤ a.length ∧ ks = List.range' k (a.length - k) ∧
      Reaches (specBody cb) (forward a.length) () a ks () s.arr ∧
      spec (specBody cb) (fun _ _ => -1) ks () s.arr = specFindIndex cb a := by
  unfold fastFindIndex at h
  split at h
  · cases h
    exact ⟨0, Nat.zero_le _, rfl, .refl _ _ _, rfl⟩
  split at h
  · cases h
    exact ⟨0, Nat.zero_le _, rfl, .refl _ _ _, rfl⟩
  obtain ⟨k, _, hk, hks, hreach, _, _⟩ :=
    forward_bailout (sim hcb) (b := ()) (inv_start hw ()) trivial h
  exact ⟨k, hk, hks, hreach, (Reaches.spec_eq hreach).symm⟩

end ArrayFindIndex
