import ArrayFilter.Model

namespace ArrayFilter

open Torque ArrayWitness

def SlowOk (K : Kind) (slow : SlowStore) : Prop :=
  ∀ a v, a.WF → (slow a a.length v).arr.WF ∧ (slow a a.length v).arr.cow = false ∧
    (slow a a.length v).arr.length = a.length + 1 ∧
    (slow a a.length v).arr.elems = a.elems ++ [some v] ∧
    ((slow a a.length v).sameMap = true → (slow a a.length v).arr.kind = K)

structure OutInv (K : Kind) (o : Out) (sel : List Val) : Prop where
  wf : o.arr.WF
  cow : o.arr.cow = false
  length : o.arr.length = sel.length
  to : o.to = sel.length
  elems : o.arr.elems = sel.map some
  kind : o.same = true → o.arr.kind = K

def Selected (r : JSArr) (sel : List Val) : Prop :=
  r.WF ∧ r.cow = false ∧ r.length = sel.length ∧ r.elems = sel.map some

theorem pushKind_isDouble (ud : Bool) (k : Kind) : (pushKind ud k).isDouble = k.isDouble := by
  cases k <;> cases ud <;> rfl

theorem outInv_new {K : Kind} (hf : K.isFast = true) : OutInv K (newOutput K) [] where
  wf := ⟨Nat.le_refl 0, by simp [JSArr.elems, newOutput], fun _ => hf, fun _ => rfl,
    fun _ => rfl, nofun⟩
  cow := rfl
  length := rfl
  to := rfl
  elems := rfl
  kind := fun _ => rfl

theorem take_set_succ {l : List (Option Val)} {n : Nat} {x : Option Val} (h : n < l.length) :
    (l.set n x).take (n + 1) = l.take n ++ [x] := by
  rw [List.take_add_one, List.take_set_of_le (Nat.le_refl n), List.getElem?_set_self h]
  rfl

theorem push_wf {b : JSArr} {v : Val} (hw : b.WF) (hlt : b.length < b.store.length)
    (hk : kindOk b.kind (some v) = true) :
    ({ b with store := b.store.set b.length (some v), length := b.length + 1 } : JSArr).WF ∧
      ({ b with store := b.store.set b.length (some v), length := b.length + 1 } : JSArr).elems =
        b.elems ++ [some v] := by
  have he : ({ b with store := b.store.set b.length (some v), length := b.length + 1 } :
      JSArr).elems = b.elems ++ [some v] := take_set_succ hlt
  refine ⟨⟨?_, ?_, hw.forRead_fast, hw.fast_forRead, hw.forCopy_fast, hw.cow_not_double⟩, he⟩
  · show b.length + 1 ≤ (b.store.set b.length (some v)).length
    rw [List.length_set]
    omega
  · intro x hx
    rw [he, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hw.kind_ok x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact hk

theorem capacityFor_spec {c : FilterConfig} {pk : Kind} {a b : JSArr} (hw : a.WF)
    (h : capacityFor c pk a = some b) :
    b.WF ∧ b.kind = a.kind ∧ b.cow = a.cow ∧ b.length = a.length ∧ b.elems = a.elems ∧
      b.length < b.store.length := by
  unfold capacityFor at h
  split at h
  · cases h
    exact ⟨hw, rfl, rfl, rfl, rfl, by omega⟩
  split at h
  · cases h
  cases h
  rename_i h1 _
  have hl := hw.length_le
  have hlen : (grown a.store (newCapacity (a.length + 1))).length =
      a.store.length + (newCapacity (a.length + 1) - a.store.length) := by
    simp [grown]
  have hnc : a.length < newCapacity (a.length + 1) := by
    unfold newCapacity
    omega
  have he : (grown a.store (newCapacity (a.length + 1))).take a.length = a.store.take a.length :=
    List.take_append_of_le_length hl
  refine ⟨⟨?_, ?_, hw.forRead_fast, hw.fast_forRead, hw.forCopy_fast, hw.cow_not_double⟩,
    rfl, rfl, rfl, he, ?_⟩
  · show a.length ≤ (grown a.store (newCapacity (a.length + 1))).length
    omega
  · intro x hx
    exact hw.kind_ok x (by simpa [JSArr.elems, he] using hx)
  · show a.length < (grown a.store (newCapacity (a.length + 1))).length
    omega

theorem append_spec {c : FilterConfig} {u : Val} {pk : Kind} {a : JSArr} {v : Val} (hw : a.WF)
    (hd : pk.isDouble = a.kind.isDouble) (hc : a.cow = false) (hk : kindOk a.kind (some v) = true) :
    (∃ b, append c u pk a v = .ok b ∧ b.WF ∧ b.kind = a.kind ∧ b.cow = false ∧
        b.length = a.length + 1 ∧ b.elems = a.elems ++ [some v]) ∨
      (∃ b, append c u pk a v = .failed b ∧ b.WF ∧ b.kind = a.kind ∧ b.cow = false ∧
        b.length = a.length ∧ b.elems = a.elems) := by
  unfold append
  rw [ite_eq_right (by simp [hd, hc])]
  cases hcap : capacityFor c pk a with
  | none => exact Or.inr ⟨a, rfl, hw, rfl, hc, rfl, rfl⟩
  | some b =>
    obtain ⟨hbw, hbk, hbc, hbl, hbe, hlt⟩ := capacityFor_spec hw hcap
    simp only []
    by_cases hacc : accepts c.undefinedDouble u pk v = false
    · rw [ite_eq_left hacc]
      exact Or.inr ⟨b, rfl, hbw, hbk, hbc.trans hc, hbl, hbe⟩
    · rw [ite_eq_right hacc, ite_eq_left hlt]
      obtain ⟨hw', he'⟩ := push_wf hbw hlt (by rw [hbk]; exact hk)
      exact Or.inl ⟨_, rfl, hw', hbk, hbc.trans hc, by simp [hbl], by rw [he', hbe]⟩

theorem outInv_slow {K : Kind} {slow : SlowStore} (hs : SlowOk K slow) {a : JSArr}
    {sel : List Val} {v : Val} (hw : a.WF) (hl : a.length = sel.length)
    (he : a.elems = sel.map some) : OutInv K (slowStore slow a a.length v) (sel ++ [v]) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs a v hw
  refine ⟨h1, h2, ?_, ?_, ?_, h5⟩
  · show (slow a a.length v).arr.length = (sel ++ [v]).length
    rw [h3, hl]
    simp
  · show a.length + 1 = (sel ++ [v]).length
    rw [hl]
    simp
  · show (slow a a.length v).arr.elems = (sel ++ [v]).map some
    rw [h4, he]
    simp

theorem store_ok {c : FilterConfig} {u : Val} {K : Kind} {slow : SlowStore} (hs : SlowOk K slow)
    {o : Out} {sel : List Val} {v : Val} (hi : OutInv K o sel) (hk : kindOk K (some v) = true)
    (prot : Bool) : ∃ o', store c u K slow o v prot = .ok o' ∧ OutInv K o' (sel ++ [v]) := by
  have hto : o.to = o.arr.length := hi.to.trans hi.length.symm
  unfold store
  by_cases hsame : (o.same && prot) = true
  · rw [ite_eq_left hsame]
    rw [ite_eq_right (by omega)]
    have hok : o.arr.kind = K := hi.kind (by simp at hsame; exact hsame.1)
    rcases append_spec (c := c) (u := u) (pk := pushKind c.undefinedDouble K) hi.wf
        (by rw [pushKind_isDouble, hok]) hi.cow (by rw [hok]; exact hk) with
      ⟨b, hb, hbw, hbk, hbc, hbl, hbe⟩ | ⟨b, hb, hbw, hbk, hbc, hbl, hbe⟩
    · rw [hb]
      refine ⟨_, rfl, hbw, hbc, by rw [hbl, hi.length]; simp, by rw [hi.to]; simp, ?_,
        fun _ => hbk.trans hok⟩
      rw [hbe, hi.elems]
      simp
    · rw [hb]
      refine ⟨_, rfl, ?_⟩
      rw [hto, ← hbl]
      exact outInv_slow hs hbw (hbl.trans hi.length) (hbe.trans hi.elems)
  · rw [ite_eq_right hsame]
    refine ⟨_, rfl, ?_⟩
    rw [hto]
    exact outInv_slow hs hi.wf hi.length hi.elems

theorem sim {c : FilterConfig} {u : Val} {K : Kind} {cb : Callback} {slow : SlowStore}
    (hcb : CallbackOk K cb) (hs : SlowOk K slow) :
    Sim K (body c u K cb slow) (specBody cb) (fun s => .done s.acc.arr) (fun sel _ => sel)
      (fun _ => OutInv K) Selected where
  step := by
    intro k ks o sel a hR hw hk _
    cases hx : get a k with
    | none => exact ⟨hR, rfl, inv_same hw hk o⟩
    | some v =>
      simp only [body, specBody]
      split
      · obtain ⟨o', ho', hi'⟩ :=
          store_ok (c := c) (u := u) hs hR (by rw [← hk]; exact get_kindOk hw hx)
            (cb k v a).protector
        rw [ho']
        exact ⟨hi', rfl, inv_post hcb k v a o'⟩
      · exact ⟨hR, rfl, inv_post hcb k v a o⟩
  fin := fun s _ hR => ⟨hR.wf, hR.cow, hR.length, hR.elems⟩

theorem fastFilter_safe {c : FilterConfig} {u : Val} {cb : Callback} {slow : SlowStore}
    {speciesOk pushable : Bool} {a : JSArr} (hw : a.WF) (hcb : CallbackOk a.kind cb)
    (hs : SlowOk a.kind slow) :
    fastFilter c u cb slow speciesOk pushable a ≠ .fatal ∧
      fastFilter c u cb slow speciesOk pushable a ≠ .ub := by
  unfold fastFilter
  split
  · exact ⟨nofun, nofun⟩
  rename_i hsp
  have hf : a.kind.isFast = true :=
    hw.forRead_fast (hw.fast_forRead (by cases h : a.fast <;> simp_all))
  split
  · exact ⟨nofun, nofun⟩
  split
  · exact ⟨nofun, nofun⟩
  have h1 := loop_ne_fatal (sim (c := c) (u := u) hcb hs) (ks := forward a.length) (b := [])
    (inv_start hw _)
    (outInv_new hf)
  have h2 := loop_ne_ub (sim (c := c) (u := u) hcb hs) (ks := forward a.length) (b := [])
    (inv_start hw _)
    (outInv_new hf)
  split
  · exact ⟨nofun, nofun⟩
  · exact ⟨nofun, nofun⟩
  · contradiction
  · contradiction

theorem fastFilter_done {c : FilterConfig} {u : Val} {cb : Callback} {slow : SlowStore}
    {speciesOk pushable : Bool} {a r : JSArr} (hw : a.WF) (hcb : CallbackOk a.kind cb)
    (hs : SlowOk a.kind slow) (h : fastFilter c u cb slow speciesOk pushable a = .done r) :
    r.WF ∧ r.cow = false ∧ r.length = (specFilter cb a).length ∧
      r.elems = (specFilter cb a).map some := by
  unfold fastFilter at h
  split at h
  · cases h
  rename_i hsp
  have hf : a.kind.isFast = true :=
    hw.forRead_fast (hw.fast_forRead (by cases h : a.fast <;> simp_all))
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · rename_i r' hl
    cases h
    exact loop_done (sim (c := c) (u := u) hcb hs) (b := []) (inv_start hw _) (outInv_new hf) hl
  all_goals cases h

theorem fastFilter_bailout {c : FilterConfig} {u : Val} {cb : Callback} {slow : SlowStore}
    {speciesOk pushable : Bool} {a : JSArr} {ks : List Nat} {o : Out} {arr : JSArr}
    (hw : a.WF) (hcb : CallbackOk a.kind cb) (hs : SlowOk a.kind slow)
    (h : fastFilter c u cb slow speciesOk pushable a = .bailout ks o arr) :
    ∃ k sel, k ≤ a.length ∧ ks = List.range' k (a.length - k) ∧
      Reaches (specBody cb) (forward a.length) [] a ks sel arr ∧
      OutInv a.kind o sel ∧ o.to = sel.length ∧
      spec (specBody cb) (fun sel _ => sel) ks sel arr = specFilter cb a := by
  unfold fastFilter at h
  split at h
  · cases h
  rename_i hsp
  have hf : a.kind.isFast = true :=
    hw.forRead_fast (hw.fast_forRead (by cases h : a.fast <;> simp_all))
  split at h
  · cases h
    exact ⟨0, [], Nat.zero_le _, rfl, .refl _ _ _, outInv_new hf, rfl, rfl⟩
  split at h
  · cases h
    exact ⟨0, [], Nat.zero_le _, rfl, .refl _ _ _, outInv_new hf, rfl, rfl⟩
  split at h
  · cases h
  · rename_i ks' s hl
    cases h
    obtain ⟨k, sel, hk, hks, hreach, hR, _⟩ :=
      forward_bailout (sim (c := c) (u := u) hcb hs) (b := []) (inv_start hw _) (outInv_new hf) hl
    exact ⟨k, sel, hk, hks, hreach, hR, hR.to, (Reaches.spec_eq hreach).symm⟩
  · cases h
  · cases h

end ArrayFilter
