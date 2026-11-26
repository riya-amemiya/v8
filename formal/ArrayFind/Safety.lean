import ArrayFind.Model

namespace ArrayFind

open Torque ArrayWitness

theorem sim {K : Kind} {cb : Callback} (hcb : CallbackOk K cb) :
    Sim K (body cb) (specBody cb) (fun _ => .done none) (fun _ _ => none) (fun _ _ _ => True)
      Eq where
  step := by
    intro k ks acc b a _ _ _ _
    simp only [body, specBody]
    split
    · rfl
    · exact ⟨trivial, rfl, inv_post hcb k _ a ()⟩
  fin := fun _ _ _ => rfl

theorem fastFind_safe {cfg : Config} {cb : Callback} {a : JSArr} (hw : a.WF)
    (hcb : CallbackOk a.kind cb) : fastFind cfg cb a ≠ .fatal ∧ fastFind cfg cb a ≠ .ub := by
  unfold fastFind
  split
  · exact ⟨nofun, nofun⟩
  split
  · exact ⟨nofun, nofun⟩
  exact ⟨loop_ne_fatal (sim hcb) (b := ()) (inv_start hw ()) trivial,
    loop_ne_ub (sim hcb) (b := ()) (inv_start hw ()) trivial⟩

theorem fastFind_done {cfg : Config} {cb : Callback} {a : JSArr} {r : Option Val} (hw : a.WF)
    (hcb : CallbackOk a.kind cb) (h : fastFind cfg cb a = .done r) : r = specFind cb a := by
  unfold fastFind at h
  split at h
  · cases h
  split at h
  · cases h
  exact loop_done (sim hcb) (b := ()) (inv_start hw ()) trivial h

theorem fastFind_bailout {cfg : Config} {cb : Callback} {a : JSArr} {ks : List Nat}
    {s : St Unit} (hw : a.WF) (hcb : CallbackOk a.kind cb)
    (h : fastFind cfg cb a = .bailout ks s) :
    ∃ k, k ≤ a.length ∧ ks = List.range' k (a.length - k) ∧
      Reaches (specBody cb) (forward a.length) () a ks () s.arr ∧
      spec (specBody cb) (fun _ _ => none) ks () s.arr = specFind cb a := by
  unfold fastFind at h
  split at h
  · cases h
    exact ⟨0, Nat.zero_le _, rfl, .refl _ _ _, rfl⟩
  split at h
  · cases h
    exact ⟨0, Nat.zero_le _, rfl, .refl _ _ _, rfl⟩
  obtain ⟨k, _, hk, hks, hreach, _, _⟩ :=
    forward_bailout (sim hcb) (b := ()) (inv_start hw ()) trivial h
  exact ⟨k, hk, hks, hreach, (Reaches.spec_eq hreach).symm⟩

end ArrayFind
