import ArrayReduce.Model

namespace ArrayReduce

open Torque ArrayWitness

theorem spec_accumulate (cb : Callback) : ∀ (ks : List Nat) (c : Val) (a : JSArr),
    spec (specBody cb) (fun b _ => b) ks (some c) a = some (accumulate cb ks c a)
  | [], _, _ => rfl
  | k :: ks, c, a => by
    unfold spec accumulate
    cases get a k with
    | none => exact spec_accumulate cb ks c a
    | some v => exact spec_accumulate cb ks _ _

theorem spec_search (cb : Callback) : ∀ (ks : List Nat) (a : JSArr),
    spec (specBody cb) (fun b _ => b) ks none a = search cb ks a
  | [], _ => rfl
  | k :: ks, a => by
    unfold spec search
    cases get a k with
    | none => exact spec_search cb ks a
    | some v => exact spec_accumulate cb ks v a

theorem spec_eq (cb : Callback) (a : JSArr) (init : Option Val) :
    spec (specBody cb) (fun b _ => b) (forward a.length) init a = specReduce cb a init := by
  cases init with
  | none => exact spec_search cb _ a
  | some c => exact spec_accumulate cb _ c a

theorem sim {K : Kind} {cb : Callback} (hcb : CallbackOk K cb) :
    Sim K (body cb) (specBody cb) (fun s => .done s.acc) (fun b _ => b)
      (fun _ acc b => acc = b) Eq where
  step := by
    intro k ks acc b a hR hw hk _
    subst hR
    cases get a k with
    | none => exact ⟨rfl, rfl, inv_same hw hk acc⟩
    | some v =>
      cases acc with
      | none => exact ⟨rfl, rfl, inv_same hw hk (some v)⟩
      | some c => exact ⟨rfl, rfl, inv_post hcb k (c, v) a _⟩
  fin := fun _ _ hR => hR

theorem fastReduce_safe {cfg : Config} {cb : Callback} {a : JSArr} {init : Option Val}
    (hw : a.WF) (hcb : CallbackOk a.kind cb) :
    fastReduce cfg cb a init ≠ .fatal ∧ fastReduce cfg cb a init ≠ .ub := by
  unfold fastReduce
  split
  · exact ⟨nofun, nofun⟩
  split
  · exact ⟨nofun, nofun⟩
  exact ⟨loop_ne_fatal (sim hcb) (b := init) (inv_start hw init) rfl,
    loop_ne_ub (sim hcb) (b := init) (inv_start hw init) rfl⟩

theorem fastReduce_done {cfg : Config} {cb : Callback} {a : JSArr} {init r : Option Val}
    (hw : a.WF) (hcb : CallbackOk a.kind cb) (h : fastReduce cfg cb a init = .done r) :
    r = specReduce cb a init := by
  unfold fastReduce at h
  split at h
  · cases h
  split at h
  · cases h
  rw [← spec_eq]
  exact loop_done (sim hcb) (b := init) (inv_start hw init) rfl h

theorem fastReduce_bailout {cfg : Config} {cb : Callback} {a : JSArr} {init : Option Val}
    {ks : List Nat} {s : St (Option Val)} (hw : a.WF) (hcb : CallbackOk a.kind cb)
    (h : fastReduce cfg cb a init = .bailout ks s) :
    ∃ k, k ≤ a.length ∧ ks = List.range' k (a.length - k) ∧
      Reaches (specBody cb) (forward a.length) init a ks s.acc s.arr ∧
      spec (specBody cb) (fun b _ => b) ks s.acc s.arr = specReduce cb a init := by
  unfold fastReduce at h
  split at h
  · cases h
    exact ⟨0, Nat.zero_le _, rfl, .refl _ _ _, spec_eq cb a init⟩
  split at h
  · cases h
    exact ⟨0, Nat.zero_le _, rfl, .refl _ _ _, spec_eq cb a init⟩
  obtain ⟨k, b', hk, hks, hreach, hR, _⟩ :=
    forward_bailout (sim hcb) (b := init) (inv_start hw init) rfl h
  subst hR
  exact ⟨k, hk, hks, hreach, (Reaches.spec_eq hreach).symm.trans (spec_eq cb a init)⟩

end ArrayReduce
