import ArrayBuild.Store

namespace ArrayBuild

open Torque

theorem newCapacity_gt (n : Nat) : n < newCapacity n := by
  unfold newCapacity
  omega

theorem length_growTo (store : List (Option Val)) (n : Nat) :
    (growTo store n).length = max store.length n := by
  simp only [growTo, List.length_append, List.length_replicate]
  omega

theorem take_growTo {store : List (Option Val)} {m n : Nat} (h : m ≤ store.length) :
    (growTo store n).take m = store.take m := by
  simp only [growTo]
  rw [List.take_append_of_le_length h]

structure Same (a b : JSArr) : Prop where
  kind : b.kind = a.kind
  length : b.length = a.length
  forRead : b.forRead = a.forRead
  fast : b.fast = a.fast
  forCopy : b.forCopy = a.forCopy
  elems : b.elems = a.elems
  cow : b.cow = true → a.cow = true

theorem Same.wf {a b : JSArr} (h : Same a b) (hw : a.WF) (hl : b.length ≤ b.store.length) :
    b.WF where
  length_le := hl
  kind_ok := by
    rw [h.elems, h.kind]
    exact hw.kind_ok
  forRead_fast := fun hr => by
    rw [h.kind]
    exact hw.forRead_fast (by rw [← h.forRead]; exact hr)
  fast_forRead := fun hf => by
    rw [h.forRead]
    exact hw.fast_forRead (by rw [← h.fast]; exact hf)
  forCopy_fast := fun hc => by
    rw [h.fast]
    exact hw.forCopy_fast (by rw [← h.forCopy]; exact hc)
  cow_not_double := fun hc => by
    rw [h.kind]
    exact hw.cow_not_double (h.cow hc)

theorem Same.trans {a b c : JSArr} (h1 : Same a b) (h2 : Same b c) : Same a c where
  kind := h2.kind.trans h1.kind
  length := h2.length.trans h1.length
  forRead := h2.forRead.trans h1.forRead
  fast := h2.fast.trans h1.fast
  forCopy := h2.forCopy.trans h1.forCopy
  elems := h2.elems.trans h1.elems
  cow := fun h => h1.cow (h2.cow h)

theorem ensureWritable_same (a : JSArr) : Same a (ensureWritable a) := by
  unfold ensureWritable
  split
  · refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun h => by cases h⟩
    simp only [JSArr.elems, List.take_take, Nat.min_self]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, id⟩

theorem ensureWritable_cow (a : JSArr) : (ensureWritable a).cow = false := by
  unfold ensureWritable
  split
  · rfl
  · rename_i h
    simpa using h

theorem ensureWritable_length_le {a : JSArr} (hl : a.length ≤ a.store.length) :
    (ensureWritable a).length ≤ (ensureWritable a).store.length := by
  unfold ensureWritable
  split
  · simp only [List.length_take]
    omega
  · exact hl

theorem ensureWritable_slack {a : JSArr} (hsl : a.SlackHoles) : (ensureWritable a).SlackHoles := by
  unfold ensureWritable
  split
  · intro x hx
    rw [List.drop_eq_nil_of_le (by simp only [List.length_take]; omega)] at hx
    simp at hx
  · exact hsl

theorem growIfNeeded_spec {env : AppendEnv} {a a1 : JSArr} (hl : a.length ≤ a.store.length)
    (h : growIfNeeded env a = some a1) :
    Same a a1 ∧ a1.length + 1 ≤ a1.store.length ∧ (a1.cow = true → a.cow = true) ∧
      (a.SlackHoles → a1.SlackHoles) := by
  unfold growIfNeeded at h
  by_cases hlt : a.store.length < a.length + 1
  · rw [ite_eq_left hlt] at h
    by_cases hmax : env.maxNewSpace ≤ newCapacity (a.length + 1)
    · rw [ite_eq_left hmax] at h
      cases h
    · rw [ite_eq_right hmax] at h
      obtain rfl := Option.some.inj h
      have hcap := newCapacity_gt (a.length + 1)
      refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
      · simp only [JSArr.elems]
        exact take_growTo hl
      · intro hc
        cases hc
      · show a.length + 1 ≤ (growTo a.store _).length
        rw [length_growTo]
        omega
      · intro hc
        cases hc
      · intro hsl x hx
        simp only [growTo, List.drop_append, List.mem_append] at hx
        rcases hx with hx | hx
        · exact hsl x hx
        · exact List.eq_of_mem_replicate (List.mem_of_mem_drop hx)
  · rw [ite_eq_right hlt] at h
    obtain rfl := Option.some.inj h
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, id⟩, by omega, id, id⟩

theorem store_done {b : JSArr} {i : Nat} {v : Val} (hc : b.cow = false) (hi : i < b.store.length) :
    storeChecked b i v = .done { b with store := b.store.set i (some v) } ∧
      storeUnchecked b i v = .done { b with store := b.store.set i (some v) } := by
  unfold storeChecked storeUnchecked
  rw [hc]
  simp [hi]

theorem elems_set_lt {b : JSArr} {i : Nat} {x : Option Val} (hi : i < b.length) :
    ({ b with store := b.store.set i x } : JSArr).elems = b.elems.set i x := by
  apply List.ext_getElem?
  intro j
  simp only [JSArr.elems, List.getElem?_take, List.getElem?_set, List.length_take]
  by_cases hj : j < b.length
  · simp [hj, Nat.lt_min, hi]
  · have : i ≠ j := by omega
    simp [hj, this]

theorem elems_set_append {b : JSArr} {x : Option Val} (hl : b.length < b.store.length) :
    ({ b with store := b.store.set b.length x, length := b.length + 1 } : JSArr).elems =
      b.elems ++ [x] := by
  have ht : (b.store.take b.length).length = b.length := by
    simp only [List.length_take]
    omega
  apply List.ext_getElem?
  intro j
  simp only [JSArr.elems, List.getElem?_take, List.getElem?_set, List.getElem?_append, ht]
  rcases Nat.lt_trichotomy j b.length with h | h | h
  · simp [h, show j < b.length + 1 by omega, show b.length ≠ j by omega]
  · subst h
    simp [hl]
  · simp [show ¬j < b.length + 1 by omega, show ¬j < b.length by omega,
      show j - b.length ≠ 0 by omega]

theorem slack_set_lt {b : JSArr} {i : Nat} {x : Option Val} (hi : i < b.length)
    (hsl : b.SlackHoles) : ({ b with store := b.store.set i x } : JSArr).SlackHoles := by
  intro y hy
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy
  simp only [List.getElem?_drop, List.getElem?_set] at hj
  rw [ite_eq_right (by omega)] at hj
  exact hsl y (List.mem_iff_getElem?.mpr ⟨j, by rw [List.getElem?_drop]; exact hj⟩)

theorem slack_set_append {b : JSArr} {x : Option Val} (hsl : b.SlackHoles) :
    ({ b with store := b.store.set b.length x, length := b.length + 1 } : JSArr).SlackHoles := by
  intro y hy
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy
  simp only [List.getElem?_drop, List.getElem?_set] at hj
  rw [ite_eq_right (by omega)] at hj
  exact hsl y (List.mem_iff_getElem?.mpr ⟨j + 1, by
    rw [List.getElem?_drop, ← hj]
    congr 1
    omega⟩)

theorem Same.refl (a : JSArr) : Same a a := ⟨rfl, rfl, rfl, rfl, rfl, rfl, id⟩

theorem kindOk_appendKind {ud : Bool} {k : Kind} {v : Val}
    (h : valueFits ud (appendKind k) v = true) : kindOk k (some v) = true := by
  cases k <;> cases v <;> cases ud <;>
    simp_all [appendKind, valueFits, kindOk, Val.isSmi, Val.isNumber]

def Appended (b : JSArr) (v : Val) (a' : JSArr) : Prop :=
  ∃ base : JSArr, Same b base ∧ base.length < base.store.length ∧ base.cow = false ∧
    (b.SlackHoles → base.SlackHoles) ∧
    a' = { base with store := base.store.set base.length (some v), length := base.length + 1 }

theorem appendElem_spec {env : AppendEnv} {k : Kind} {b : JSArr} {v : Val}
    (hl : b.length ≤ b.store.length) (hc : b.cow = false) :
    (∃ a', appendElem env k b v = .done a' ∧ Appended b v a' ∧
        valueFits env.undefinedDouble k v = true) ∨
      (∃ a1, appendElem env k b v = .slow a1 ∧ Same b a1 ∧ a1.length ≤ a1.store.length ∧
        (b.SlackHoles → a1.SlackHoles)) := by
  unfold appendElem
  cases hg : growIfNeeded env b with
  | none =>
    exact Or.inr ⟨b, rfl, Same.refl b, hl, id⟩
  | some a1 =>
    dsimp only
    obtain ⟨hs, hroom, hcow, hsl⟩ := growIfNeeded_spec hl hg
    have hc1 : a1.cow = false := by
      cases h1 : a1.cow
      · rfl
      · rw [hcow h1] at hc
        exact absurd hc (by decide)
    by_cases hv : valueFits env.undefinedDouble k v = false
    · rw [ite_eq_left hv]
      exact Or.inr ⟨a1, rfl, hs, by omega, hsl⟩
    · rw [ite_eq_right hv]
      have hd := store_done (v := v) hc1 (show a1.length < a1.store.length by omega)
      have hsel : (if k = .holeyDouble ∧ v = .undef then storeUnchecked a1 a1.length v
          else storeChecked a1 a1.length v) =
          .done { a1 with store := a1.store.set a1.length (some v) } := by
        split
        · exact hd.2
        · exact hd.1
      rw [hsel]
      refine Or.inl ⟨_, rfl, ⟨a1, hs, by omega, hc1, hsl, rfl⟩, ?_⟩
      cases hf : valueFits env.undefinedDouble k v
      · exact absurd hf hv
      · rfl

theorem appended_elems {b a' : JSArr} {v : Val} (h : Appended b v a') :
    a'.elems = b.elems ++ [some v] := by
  obtain ⟨base, hs, hroom, _, _, rfl⟩ := h
  rw [elems_set_append hroom, hs.elems]

theorem appended_length {b a' : JSArr} {v : Val} (h : Appended b v a') :
    a'.length = b.length + 1 := by
  obtain ⟨base, hs, _, _, _, rfl⟩ := h
  show base.length + 1 = b.length + 1
  rw [hs.length]

theorem appended_slack {b a' : JSArr} {v : Val} (hsl : b.SlackHoles) (h : Appended b v a') :
    a'.SlackHoles := by
  obtain ⟨base, _, _, _, hs, rfl⟩ := h
  exact slack_set_append (hs hsl)

theorem appended_wf {b a' : JSArr} {v : Val} (hw : b.WF) (hk : kindOk b.kind (some v) = true)
    (h : Appended b v a') : a'.WF ∧ a'.kind = b.kind ∧ a'.cow = false ∧
      a'.forRead = b.forRead ∧ a'.fast = b.fast ∧ a'.forCopy = b.forCopy := by
  obtain ⟨base, hs, hroom, hc, _, rfl⟩ := h
  have hbw : base.WF := hs.wf hw (by omega)
  refine ⟨?_, hs.kind, hc, hs.forRead, hs.fast, hs.forCopy⟩
  exact {
    length_le := by
      show base.length + 1 ≤ (base.store.set base.length (some v)).length
      rw [List.length_set]
      exact hroom
    kind_ok := by
      intro x hx
      rw [elems_set_append hroom] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hbw.kind_ok x hx
      · rw [List.mem_singleton.mp hx]
        show kindOk base.kind (some v) = true
        rw [hs.kind]
        exact hk
    forRead_fast := hbw.forRead_fast
    fast_forRead := hbw.fast_forRead
    forCopy_fast := hbw.forCopy_fast
    cow_not_double := fun h => absurd (hc.symm.trans h) (by decide) }

theorem overwrite_spec {env : StoreEnv} {b : JSArr} {i : Nat} {v : Val}
    (hc : b.cow = false) (hi : i < b.length) (hl : b.length ≤ b.store.length) :
    (overwrite env b i v = .done { b with store := b.store.set i (some v) } ∧
        kindOk b.kind (some v) = true) ∨ overwrite env b i v = .slow b := by
  have hd := store_done (v := v) hc (show i < b.store.length by omega)
  unfold overwrite
  by_cases hs : b.kind = .packedSmi ∨ b.kind = .holeySmi
  · rw [ite_eq_left hs]
    by_cases hv : v.isSmi = true
    · rw [ite_eq_left hv]
      refine Or.inl ⟨hd.1, ?_⟩
      rcases hs with h | h <;> rw [h] <;> simpa [kindOk] using hv
    · rw [ite_eq_right hv]
      exact Or.inr rfl
  · rw [ite_eq_right hs]
    by_cases hdb : b.kind.isDouble = true
    · rw [ite_eq_left hdb]
      by_cases hu : env.append.undefinedDouble = true ∧ b.kind = .holeyDouble
      · rw [ite_eq_left hu]
        by_cases hn : v.isNumber = true
        · rw [ite_eq_left hn]
          refine Or.inl ⟨hd.1, ?_⟩
          rw [hu.2]
          simp [kindOk, hn]
        · rw [ite_eq_right hn]
          by_cases hun : v = .undef
          · rw [ite_eq_left hun]
            refine Or.inl ⟨hd.2, ?_⟩
            rw [hu.2, hun]
            rfl
          · rw [ite_eq_right hun]
            exact Or.inr rfl
      · rw [ite_eq_right hu]
        by_cases hn : v.isNumber = true
        · rw [ite_eq_left hn]
          refine Or.inl ⟨hd.1, ?_⟩
          cases hk : b.kind <;> simp_all [Kind.isDouble, kindOk]
        · rw [ite_eq_right hn]
          exact Or.inr rfl
    · rw [ite_eq_right hdb]
      refine Or.inl ⟨hd.1, ?_⟩
      cases hk : b.kind <;> simp_all [Kind.isDouble, kindOk]

theorem set_wf {b : JSArr} {i : Nat} {v : Val} (hw : b.WF) (hi : i < b.length)
    (hk : kindOk b.kind (some v) = true) : ({ b with store := b.store.set i (some v) } : JSArr).WF where
  length_le := by
    show b.length ≤ (b.store.set i (some v)).length
    rw [List.length_set]
    exact hw.length_le
  kind_ok := by
    intro x hx
    rw [elems_set_lt hi] at hx
    rcases List.mem_or_eq_of_mem_set hx with hx | rfl
    · exact hw.kind_ok x hx
    · exact hk
  forRead_fast := hw.forRead_fast
  fast_forRead := hw.fast_forRead
  forCopy_fast := hw.forCopy_fast
  cow_not_double := hw.cow_not_double

theorem fastCreateDataProperty_spec {env : StoreEnv} {a : JSArr} {i : Nat} {v : Val}
    (hw : a.WF) :
    (∃ a', fastCreateDataProperty env a i v = .done a' ∧ a'.WF ∧
        a'.elems = setElem a.elems i v ∧ a'.length = max a.length (i + 1) ∧
        (a.SlackHoles → a'.SlackHoles) ∧ a'.kind = a.kind ∧ a'.cow = false ∧
        a'.forRead = a.forRead ∧ a'.fast = a.fast ∧ a'.forCopy = a.forCopy) ∨
      (∃ b, fastCreateDataProperty env a i v = .slow b ∧ b.WF ∧
        (a.SlackHoles → b.SlackHoles) ∧ Same a b) := by
  have hl := hw.length_le
  have helen : a.elems.length = a.length := JSArr.elems_length hw
  unfold fastCreateDataProperty
  by_cases hf : a.fast = false
  · rw [ite_eq_left hf]
    exact Or.inr ⟨a, rfl, hw, id, Same.refl a⟩
  rw [ite_eq_right hf]
  by_cases hgt : a.length < i
  · rw [ite_eq_left hgt]
    exact Or.inr ⟨a, rfl, hw, id, Same.refl a⟩
  rw [ite_eq_right hgt]
  have hew := ensureWritable_same a
  have hewl := ensureWritable_length_le hl
  have hewc := ensureWritable_cow a
  have hewwf : (ensureWritable a).WF := hew.wf hw hewl
  by_cases heq : i = a.length
  · rw [ite_eq_left heq]
    by_cases hp : env.pushable = false
    · rw [ite_eq_left hp]
      exact Or.inr ⟨a, rfl, hw, id, Same.refl a⟩
    rw [ite_eq_right hp]
    rcases appendElem_spec (env := env.append) (k := appendKind a.kind) (v := v) hewl hewc with
      ⟨a', hd, happ, hfit⟩ | ⟨a1, hs, hsame, hl1, hsl1⟩
    · have hk : kindOk (ensureWritable a).kind (some v) = true := by
        rw [hew.kind]
        exact kindOk_appendKind hfit
      obtain ⟨hwf, hkind, hcow, hfr, hfa, hfc⟩ := appended_wf hewwf hk happ
      refine Or.inl ⟨a', hd, hwf, ?_, ?_, fun hsl => appended_slack (ensureWritable_slack hsl) happ,
        hkind.trans hew.kind, hcow, hfr.trans hew.forRead, hfa.trans hew.fast,
        hfc.trans hew.forCopy⟩
      · rw [appended_elems happ, hew.elems]
        unfold setElem
        rw [ite_eq_right (by omega)]
      · rw [appended_length happ, hew.length]
        omega
    · exact Or.inr ⟨a1, hs, hsame.wf hewwf hl1, fun hsl => hsl1 (ensureWritable_slack hsl),
        hew.trans hsame⟩
  · rw [ite_eq_right heq]
    have hi : i < (ensureWritable a).length := by
      rw [hew.length]
      omega
    rcases overwrite_spec (env := env) (v := v) hewc hi hewl with ⟨hd, hk⟩ | hs
    · refine Or.inl ⟨_, hd, set_wf hewwf hi hk, ?_, ?_, ?_, hew.kind, hewc, hew.forRead,
        hew.fast, hew.forCopy⟩
      · rw [elems_set_lt hi, hew.elems]
        unfold setElem
        rw [ite_eq_left (by omega)]
      · show (ensureWritable a).length = _
        rw [hew.length]
        omega
      · intro hsl
        exact slack_set_lt hi (ensureWritable_slack hsl)
    · exact Or.inr ⟨_, hs, hewwf, ensureWritable_slack, hew⟩

theorem fastCreateDataProperty_safe {env : StoreEnv} {a : JSArr} {i : Nat} {v : Val}
    (hw : a.WF) :
    fastCreateDataProperty env a i v ≠ .ub ∧ fastCreateDataProperty env a i v ≠ .fatal := by
  rcases fastCreateDataProperty_spec (env := env) (i := i) (v := v) hw with
    ⟨a', h, _⟩ | ⟨b, h, _⟩ <;> rw [h] <;> exact ⟨nofun, nofun⟩

end ArrayBuild
