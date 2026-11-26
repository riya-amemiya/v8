import ArrayMap.Model

namespace ArrayMap

open Torque ArrayWitness

def SmiOrHole (x : Option Val) : Prop := x = none ∨ ∃ y, x = some y ∧ y.isSmi = true

def NumOrHole (x : Option Val) : Prop := x = none ∨ ∃ y, x = some y ∧ y.isNumber = true

structure Rel (ud : Bool) (len : Nat) (ks : List Nat) (v : Vec) (out : List (Option Val)) :
    Prop where
  le : ks.length ≤ len
  pos : ks = List.range' (len - ks.length) ks.length
  store : v.store = out
  length : out.length = len
  rest : ∀ i, len - ks.length ≤ i → out.getD i none = none
  smis : v.onlySmis = true → ∀ x ∈ out, SmiOrHole x
  numbers : v.onlyNumbers = true → ∀ x ∈ out, NumOrHole x
  numUndef : v.onlyNumUndef = true → ∀ x ∈ out, doubleOk ud x = true
  packed : v.skipped = false → ∀ i < len - ks.length, out.getD i none ≠ none

theorem rel_start (ud : Bool) (len : Nat) :
    Rel ud len (forward len) (newVector len) (List.replicate len none) where
  le := by simp [forward]
  pos := by simp [forward]
  store := rfl
  length := by simp
  rest := by
    intro i _
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  smis := fun _ x hx => Or.inl (List.eq_of_mem_replicate hx)
  numbers := fun _ x hx => Or.inl (List.eq_of_mem_replicate hx)
  numUndef := fun _ x hx => by rw [List.eq_of_mem_replicate hx]; rfl
  packed := fun _ i hi => by simp [forward] at hi

theorem range'_cons {m n k : Nat} {ks : List Nat} (h : k :: ks = List.range' m n) :
    k = m ∧ ks = List.range' (m + 1) (n - 1) ∧ 0 < n := by
  cases n with
  | zero => simp at h
  | succ n =>
    simp only [List.range'_succ, List.cons.injEq] at h
    exact ⟨h.1, by simpa using h.2, by omega⟩

theorem rel_pos {ud : Bool} {len k : Nat} {ks : List Nat} {v : Vec} {out : List (Option Val)}
    (hr : Rel ud len (k :: ks) v out) : k = len - (ks.length + 1) ∧ k < len ∧
      ks = List.range' (len - ks.length) ks.length := by
  have hle := hr.le
  simp only [List.length_cons] at hle
  obtain ⟨h1, h2, _⟩ := range'_cons hr.pos
  simp only [List.length_cons] at h1 h2
  refine ⟨h1, by omega, ?_⟩
  have e1 : len - (ks.length + 1) + 1 = len - ks.length := by omega
  have e2 : ks.length + 1 - 1 = ks.length := by omega
  rw [e1, e2] at h2
  exact h2

theorem getD_set_ne {out : List (Option Val)} {k i : Nat} {x : Option Val} (h : k ≠ i) :
    (out.set k x).getD i none = out.getD i none := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem mem_set_cases {out : List (Option Val)} {k : Nat} {x y : Option Val}
    (h : y ∈ out.set k x) : y ∈ out ∨ y = x := List.mem_or_eq_of_mem_set h

theorem rel_skip {ud : Bool} {len k : Nat} {ks : List Nat} {v : Vec} {out : List (Option Val)}
    (hr : Rel ud len (k :: ks) v out) : Rel ud len ks { v with skipped := true } out := by
  obtain ⟨hk, _, hks⟩ := rel_pos hr
  have hle := hr.le
  simp only [List.length_cons] at hle
  exact {
    le := by omega
    pos := hks
    store := hr.store
    length := hr.length
    rest := fun i hi => hr.rest i (by simp only [List.length_cons]; omega)
    smis := hr.smis
    numbers := hr.numbers
    numUndef := hr.numUndef
    packed := fun h => by cases h }

theorem noteResult_flags (ud : Bool) (v : Vec) (r : Val) :
    ((noteResult ud v r).onlySmis = true → v.onlySmis = true ∧ r.isSmi = true) ∧
      ((noteResult ud v r).onlyNumbers = true → v.onlyNumbers = true ∧ r.isNumber = true) ∧
      ((noteResult ud v r).onlyNumUndef = true → v.onlyNumUndef = true ∧
        doubleOk ud (some r) = true) ∧
      (noteResult ud v r).skipped = v.skipped := by
  cases r <;> cases ud <;> simp [noteResult, Val.isSmi, Val.isNumber, doubleOk]

theorem rel_store {ud : Bool} {len k : Nat} {ks : List Nat} {v : Vec} {out : List (Option Val)}
    {r : Val} (hr : Rel ud len (k :: ks) v out) :
    ∃ v', storeResult ud v k r = some v' ∧ Rel ud len ks v' (out.set k (some r)) := by
  obtain ⟨hk, hlt, hks⟩ := rel_pos hr
  have hle := hr.le
  simp only [List.length_cons] at hle
  have hsl : k < v.store.length := by rw [hr.store, hr.length]; exact hlt
  obtain ⟨fs, fn, fu, fk⟩ := noteResult_flags ud v r
  refine ⟨{ noteResult ud v r with store := v.store.set k (some r) },
    by simp [storeResult, hsl], ?_⟩
  exact {
    le := by omega
    pos := hks
    store := by simp only [hr.store]
    length := by simp [hr.length]
    rest := fun i hi => by
      rw [getD_set_ne (by omega)]
      exact hr.rest i (by simp only [List.length_cons]; omega)
    smis := fun h x hx => by
      obtain ⟨h1, h2⟩ := fs h
      rcases mem_set_cases hx with hx | rfl
      · exact hr.smis h1 x hx
      · exact Or.inr ⟨r, rfl, h2⟩
    numbers := fun h x hx => by
      obtain ⟨h1, h2⟩ := fn h
      rcases mem_set_cases hx with hx | rfl
      · exact hr.numbers h1 x hx
      · exact Or.inr ⟨r, rfl, h2⟩
    numUndef := fun h x hx => by
      obtain ⟨h1, h2⟩ := fu h
      rcases mem_set_cases hx with hx | rfl
      · exact hr.numUndef h1 x hx
      · exact h2
    packed := fun h i hi => by
      have h' : v.skipped = false := by rw [← fk]; exact h
      by_cases hik : i = k
      · subst hik
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [hr.length]; exact hlt)]
        simp
      · rw [getD_set_ne (Ne.symm hik)]
        exact hr.packed h' i (by simp only [List.length_cons] at hk ⊢; omega) }

theorem take_holes {out : List (Option Val)} {valid : Nat} (hv : valid ≤ out.length)
    (hrest : ∀ i, valid ≤ i → out.getD i none = none) :
    out.take valid ++ List.replicate (out.length - valid) none = out := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_append]
  simp only [List.length_take, Nat.min_eq_left hv]
  by_cases hi : i < valid
  · rw [ite_eq_left hi, List.getElem?_take, ite_eq_left hi]
  · rw [ite_eq_right hi, List.getElem?_replicate]
    have := hrest i (by omega)
    rw [List.getD_eq_getElem?_getD] at this
    by_cases hl : i < out.length
    · rw [ite_eq_left (by omega), List.getElem?_eq_getElem hl]
      rw [List.getElem?_eq_getElem hl] at this
      simp only [Option.getD_some] at this
      rw [this]
    · rw [ite_eq_right (by omega), List.getElem?_eq_none (by omega)]

theorem baseKind_ok {ud : Bool} {len : Nat} {ks : List Nat} {v : Vec} {out : List (Option Val)}
    (hr : Rel ud len ks v out) :
    ∀ x ∈ out, x ≠ none → kindOk (baseKind v) x = true := by
  intro x hx hn
  unfold baseKind
  split
  · rename_i h
    rcases hr.smis h x hx with h1 | ⟨y, rfl, hy⟩
    · exact absurd h1 hn
    · simpa [kindOk] using hy
  · split
    · rename_i _ h
      rcases hr.numbers h x hx with h1 | ⟨y, rfl, hy⟩
      · exact absurd h1 hn
      · simpa [kindOk] using hy
    · split
      · rename_i _ _ h
        have := hr.numUndef h x hx
        cases x with
        | none => exact absurd rfl hn
        | some y =>
          simp only [doubleOk, Bool.or_eq_true, Bool.and_eq_true] at this
          simp only [kindOk, Bool.or_eq_true]
          rcases this with h1 | ⟨_, h2⟩
          · exact Or.inl h1
          · exact Or.inr h2
      · cases x with
        | none => exact absurd rfl hn
        | some _ => rfl

theorem holey_ok {k : Kind} {x : Option Val} (hk : x ≠ none → kindOk k x = true) :
    kindOk k.toHoley x = true := by
  cases x with
  | none => cases k <;> rfl
  | some y =>
    have := hk (by simp)
    cases k <;> simp_all [Kind.toHoley, kindOk]

theorem kind_isFast (v : Vec) (valid : Nat) : (resultKind v valid).isFast = true := by
  unfold resultKind baseKind
  repeat' split
  all_goals rfl

theorem create_ok {ud : Bool} {len : Nat} {ks : List Nat} {v : Vec} {out : List (Option Val)}
    (hr : Rel ud len ks v out) :
    ∃ a, createJSArray ud v (len - ks.length) = .arr a ∧ a.WF ∧ a.elems = out ∧ a.length = len := by
  have hlen : v.store.length = len := by rw [hr.store, hr.length]
  have hvalid : len - ks.length ≤ out.length := by rw [hr.length]; omega
  have hkind : ∀ x ∈ out, kindOk (resultKind v (len - ks.length)) x = true := by
    intro x hx
    unfold resultKind
    split
    · exact holey_ok (baseKind_ok hr x hx)
    · rename_i hp
      have hs : v.skipped = false := by
        cases h : v.skipped
        · rfl
        · exact absurd (Or.inl h) hp
      have hfull : ks.length = 0 := by
        have : ¬(len - ks.length < v.store.length) := fun h => hp (Or.inr h)
        rw [hlen] at this
        have := hr.le
        omega
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
      obtain ⟨hil, _⟩ := List.getElem?_eq_some_iff.mp hi
      have hne := hr.packed hs i (by rw [hr.length] at hil; omega)
      rw [List.getD_eq_getElem?_getD, hi] at hne
      exact baseKind_ok hr x hx hne
  have helems : ∀ st : List (Option Val), st = out →
      (⟨resultKind v (len - ks.length), true, true, false, false, v.store.length, st⟩ :
        JSArr).WF ∧
      (⟨resultKind v (len - ks.length), true, true, false, false, v.store.length, st⟩ :
        JSArr).elems = out := by
    intro st hst
    rw [hst]
    have htake : out.take v.store.length = out := by
      rw [hlen, ← hr.length, List.take_length]
    refine ⟨⟨Nat.le_of_eq (show v.store.length = out.length by rw [hlen, hr.length]), ?_,
      fun _ => kind_isFast v _, id, nofun, nofun⟩, htake⟩
    intro x hx
    rw [JSArr.elems, htake] at hx
    exact hkind x hx
  unfold createJSArray
  split
  · rename_i hd
    have hall : ((v.store.take (len - ks.length)).all (doubleOk ud)) = true := by
      rw [List.all_eq_true]
      intro x hx
      have hx' : x ∈ out := by rw [← hr.store]; exact List.mem_of_mem_take hx
      have hb : (baseKind v).isDouble = true := by
        unfold resultKind at hd
        split at hd
        · cases hk : baseKind v <;> rw [hk] at hd <;> simp_all [Kind.toHoley, Kind.isDouble]
        · exact hd
      unfold baseKind at hb
      by_cases hs : v.onlySmis = true
      · rw [ite_eq_left hs] at hb
        cases hb
      rw [ite_eq_right hs] at hb
      by_cases hn : v.onlyNumbers = true
      · rcases hr.numbers hn x hx' with rfl | ⟨y, rfl, hy⟩
        · rfl
        · simp [doubleOk, hy]
      rw [ite_eq_right hn] at hb
      by_cases hu : v.onlyNumUndef = true
      · exact hr.numUndef hu x hx'
      rw [ite_eq_right hu] at hb
      cases hb
    rw [ite_eq_right (by rw [hall]; decide)]
    have hst : v.store.take (len - ks.length) ++
        List.replicate (v.store.length - (len - ks.length)) none = out := by
      rw [hr.store]
      exact take_holes hvalid (fun i hi => hr.rest i hi)
    obtain ⟨hw, he⟩ := helems _ hst
    exact ⟨_, rfl, hw, he, hlen⟩
  · obtain ⟨hw, he⟩ := helems _ hr.store
    exact ⟨_, rfl, hw, he, hlen⟩

def Q (len : Nat) (r : JSArr) (out : List (Option Val)) : Prop :=
  r.WF ∧ r.elems = out ∧ r.length = len

theorem sim {ud : Bool} {K : Kind} {cb : Callback} {len : Nat} (hcb : CallbackOk K cb) :
    Sim K (body ud cb) (specBody cb) (finish ud len) (fun out _ => out) (Rel ud len) (Q len) where
  step := by
    intro k ks acc b a hr hw hk _
    cases hg : get a k with
    | none =>
      simp only [body, specBody]
      exact ⟨rel_skip hr, rfl, inv_same hw hk _⟩
    | some x =>
      obtain ⟨v', hs, hr'⟩ := rel_store (r := (cb k x a).res) hr
      simp only [body, specBody, hs]
      exact ⟨hr', rfl, inv_post hcb k x a v'⟩
  fin := by
    intro s b hr
    obtain ⟨r, hc, hw, he, hl⟩ := create_ok hr
    simp only [List.length_nil, Nat.sub_zero] at hc
    simp only [finish, hc, FinOk]
    exact ⟨hw, he, hl⟩

theorem fastMap_safe {ud : Bool} {smiMax : Nat} {speciesOk : Bool} {cb : Callback} {a : JSArr}
    (hw : a.WF) (hcb : CallbackOk a.kind cb) :
    fastMap ud smiMax speciesOk cb a ≠ .fatal ∧ fastMap ud smiMax speciesOk cb a ≠ .ub := by
  unfold fastMap
  split
  · exact ⟨nofun, nofun⟩
  have hs := sim (ud := ud) (len := a.length) hcb
  have hi := inv_start (acc := newVector a.length) hw
  have hr := rel_start ud a.length
  split
  · exact ⟨nofun, nofun⟩
  · rename_i ks s hb
    obtain ⟨b', _, hR, _, _⟩ := loop_bailout hs hi hr hb
    obtain ⟨out, hc, _⟩ := create_ok hR
    rw [hc]
    exact ⟨nofun, nofun⟩
  · rename_i hf
    exact absurd hf (loop_ne_fatal hs hi hr)
  · rename_i hu
    exact absurd hu (loop_ne_ub hs hi hr)

theorem fastMap_done {ud : Bool} {smiMax : Nat} {speciesOk : Bool} {cb : Callback} {a r : JSArr}
    (hw : a.WF) (hcb : CallbackOk a.kind cb) (h : fastMap ud smiMax speciesOk cb a = .done r) :
    r.WF ∧ r.elems = specMap cb a ∧ r.length = a.length := by
  unfold fastMap at h
  split at h
  · cases h
  have hs := sim (ud := ud) (len := a.length) hcb
  have hi := inv_start (acc := newVector a.length) hw
  have hr := rel_start ud a.length
  split at h
  · rename_i r' hd
    cases h
    exact loop_done hs hi hr hd
  · split at h <;> cases h
  · cases h
  · cases h

theorem fastMap_bailout {ud : Bool} {smiMax : Nat} {speciesOk : Bool} {cb : Callback}
    {a out arr : JSArr} {ks : List Nat} (hw : a.WF) (hcb : CallbackOk a.kind cb)
    (h : fastMap ud smiMax speciesOk cb a = .bailout out ks arr) :
    ∃ k o, k ≤ a.length ∧ ks = List.range' k (a.length - k) ∧
      Reaches (specBody cb) (forward a.length) (List.replicate a.length none) a ks o arr ∧
      out.WF ∧ out.elems = o ∧ out.length = a.length ∧ arr.WF ∧
      spec (specBody cb) (fun out _ => out) ks o arr = specMap cb a := by
  unfold fastMap at h
  split at h
  · cases h
  have hs := sim (ud := ud) (len := a.length) hcb
  have hi := inv_start (acc := newVector a.length) hw
  have hr := rel_start ud a.length
  split at h
  · cases h
  · rename_i ks' s hb
    split at h
    · rename_i out' hc
      cases h
      obtain ⟨k, b', hk, hks, hreach, hR, hI⟩ := forward_bailout hs hi hr hb
      obtain ⟨out'', hc', hw', he', hl'⟩ := create_ok hR
      rw [hc] at hc'
      cases hc'
      exact ⟨k, b', hk, hks, hreach, hw', he', hl', hI.1, (Reaches.spec_eq hreach).symm⟩
    · cases h
  · cases h
  · cases h

end ArrayMap
