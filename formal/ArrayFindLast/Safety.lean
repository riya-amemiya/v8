import ArrayFindLast.Model

namespace ArrayFindLast

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

theorem fastFindLast_safe {cfg : Config} {cb : Callback} {a : JSArr} (hw : a.WF)
    (hcb : CallbackOk a.kind cb) :
    fastFindLast cfg cb a ≠ .fatal ∧ fastFindLast cfg cb a ≠ .ub := by
  unfold fastFindLast
  split
  · exact ⟨nofun, nofun⟩
  split
  · exact ⟨nofun, nofun⟩
  exact ⟨loop_ne_fatal (sim hcb) (b := ()) (inv_start hw ()) trivial,
    loop_ne_ub (sim hcb) (b := ()) (inv_start hw ()) trivial⟩

theorem fastFindLast_done {cfg : Config} {cb : Callback} {a : JSArr} {r : Option Val}
    (hw : a.WF) (hcb : CallbackOk a.kind cb) (h : fastFindLast cfg cb a = .done r) :
    r = specFindLast cb a := by
  unfold fastFindLast at h
  split at h
  · cases h
  split at h
  · cases h
  exact loop_done (sim hcb) (b := ()) (inv_start hw ()) trivial h

theorem fastFindLast_bailout {cfg : Config} {cb : Callback} {a : JSArr} {ks : List Nat}
    {s : St Unit} (hw : a.WF) (hcb : CallbackOk a.kind cb)
    (h : fastFindLast cfg cb a = .bailout ks s) :
    ∃ m, m ≤ a.length ∧ ks = backward m ∧
      Reaches (specBody cb) (backward a.length) () a ks () s.arr ∧
      spec (specBody cb) (fun _ _ => none) ks () s.arr = specFindLast cb a := by
  unfold fastFindLast at h
  split at h
  · cases h
    exact ⟨a.length, Nat.le_refl _, rfl, .refl _ _ _, rfl⟩
  split at h
  · cases h
    exact ⟨a.length, Nat.le_refl _, rfl, .refl _ _ _, rfl⟩
  obtain ⟨m, _, hm, hks, hreach, _, _⟩ :=
    backward_bailout (sim hcb) (b := ()) (inv_start hw ()) trivial h
  exact ⟨m, hm, hks, hreach, (Reaches.spec_eq hreach).symm⟩

end ArrayFindLast
