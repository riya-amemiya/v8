import ArrayForEach.Model

namespace ArrayForEach

open Torque ArrayWitness

theorem sim {K : Kind} {cb : Callback} (hcb : CallbackOk K cb) :
    Sim K (body cb) (specBody cb) (fun s => .done s.arr) (fun _ a => a) (fun _ _ _ => True)
      Eq where
  step := by
    intro k ks acc b a _ hw hk _
    cases get a k with
    | none => exact ⟨trivial, rfl, inv_same hw hk ()⟩
    | some v => exact ⟨trivial, rfl, inv_post hcb k v a ()⟩
  fin := fun _ _ _ => rfl

theorem fastForEach_safe {cfg : Config} {cb : Callback} {a : JSArr} (hw : a.WF)
    (hcb : CallbackOk a.kind cb) :
    fastForEach cfg cb a ≠ .fatal ∧ fastForEach cfg cb a ≠ .ub := by
  unfold fastForEach
  split
  · exact ⟨nofun, nofun⟩
  split
  · exact ⟨nofun, nofun⟩
  exact ⟨loop_ne_fatal (sim hcb) (b := ()) (inv_start hw ()) trivial,
    loop_ne_ub (sim hcb) (b := ()) (inv_start hw ()) trivial⟩

theorem fastForEach_done {cfg : Config} {cb : Callback} {a r : JSArr} (hw : a.WF)
    (hcb : CallbackOk a.kind cb) (h : fastForEach cfg cb a = .done r) :
    r = specForEach cb a := by
  unfold fastForEach at h
  split at h
  · cases h
  split at h
  · cases h
  exact loop_done (sim hcb) (b := ()) (inv_start hw ()) trivial h

theorem fastForEach_bailout {cfg : Config} {cb : Callback} {a : JSArr} {ks : List Nat}
    {s : St Unit} (hw : a.WF) (hcb : CallbackOk a.kind cb)
    (h : fastForEach cfg cb a = .bailout ks s) :
    ∃ k, k ≤ a.length ∧ ks = List.range' k (a.length - k) ∧
      Reaches (specBody cb) (forward a.length) () a ks () s.arr ∧
      spec (specBody cb) (fun _ a => a) ks () s.arr = specForEach cb a := by
  unfold fastForEach at h
  split at h
  · cases h
    exact ⟨0, Nat.zero_le _, rfl, .refl _ _ _, rfl⟩
  split at h
  · cases h
    exact ⟨0, Nat.zero_le _, rfl, .refl _ _ _, rfl⟩
  obtain ⟨k, _, hk, hks, hreach, _, _⟩ :=
    forward_bailout (sim hcb) (b := ()) (inv_start hw ()) trivial h
  exact ⟨k, hk, hks, hreach, (Reaches.spec_eq hreach).symm⟩

end ArrayForEach
