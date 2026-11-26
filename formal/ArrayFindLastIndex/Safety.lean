import ArrayFindLastIndex.Model

namespace ArrayFindLastIndex

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

theorem fastFindLastIndex_safe {cfg : Config} {cb : Callback} {a : JSArr} (hw : a.WF)
    (hcb : CallbackOk a.kind cb) :
    fastFindLastIndex cfg cb a ≠ .fatal ∧ fastFindLastIndex cfg cb a ≠ .ub := by
  unfold fastFindLastIndex
  split
  · exact ⟨nofun, nofun⟩
  split
  · exact ⟨nofun, nofun⟩
  exact ⟨loop_ne_fatal (sim hcb) (b := ()) (inv_start hw ()) trivial,
    loop_ne_ub (sim hcb) (b := ()) (inv_start hw ()) trivial⟩

theorem fastFindLastIndex_done {cfg : Config} {cb : Callback} {a : JSArr} {r : Int} (hw : a.WF)
    (hcb : CallbackOk a.kind cb) (h : fastFindLastIndex cfg cb a = .done r) :
    r = specFindLastIndex cb a := by
  unfold fastFindLastIndex at h
  split at h
  · cases h
  split at h
  · cases h
  exact loop_done (sim hcb) (b := ()) (inv_start hw ()) trivial h

theorem fastFindLastIndex_bailout {cfg : Config} {cb : Callback} {a : JSArr} {ks : List Nat}
    {s : St Unit} (hw : a.WF) (hcb : CallbackOk a.kind cb)
    (h : fastFindLastIndex cfg cb a = .bailout ks s) :
    ∃ m, m ≤ a.length ∧ ks = backward m ∧
      Reaches (specBody cb) (backward a.length) () a ks () s.arr ∧
      spec (specBody cb) (fun _ _ => -1) ks () s.arr = specFindLastIndex cb a := by
  unfold fastFindLastIndex at h
  split at h
  · cases h
    exact ⟨a.length, Nat.le_refl _, rfl, .refl _ _ _, rfl⟩
  split at h
  · cases h
    exact ⟨a.length, Nat.le_refl _, rfl, .refl _ _ _, rfl⟩
  obtain ⟨m, _, hm, hks, hreach, _, _⟩ :=
    backward_bailout (sim hcb) (b := ()) (inv_start hw ()) trivial h
  exact ⟨m, hm, hks, hreach, (Reaches.spec_eq hreach).symm⟩

end ArrayFindLastIndex
