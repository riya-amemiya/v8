import InPlace.Model

namespace InPlace

open Torque

@[simp] theorem Res.ok_bind {α β : Type} (x : α) (f : α → Res β) : (Res.ok x >>= f) = f x := rfl

@[simp] theorem Res.ub_bind {α β : Type} (f : α → Res β) : ((Res.ub : Res α) >>= f) = .ub := rfl

@[simp] theorem Res.abort_bind {α β : Type} (f : α → Res β) :
    ((Res.abort : Res α) >>= f) = .abort := rfl

@[simp] theorem Res.pure_eq {α : Type} (x : α) : (pure x : Res α) = .ok x := rfl

@[simp] theorem Res.ok_then {α ρ : Type} (x : α) (f : α → Result ρ) : (Res.ok x).then f = f x :=
  rfl

@[simp] theorem Res.ub_then {α ρ : Type} (f : α → Result ρ) : (Res.ub : Res α).then f = .ub := rfl

@[simp] theorem Res.abort_then {α ρ : Type} (f : α → Result ρ) :
    (Res.abort : Res α).then f = .abort := rfl

theorem loadSlot_nat {s : List (Option Val)} {i : Nat} (h : i < s.length) :
    loadSlot s i = .ok (s.getD i none) := by
  unfold loadSlot
  rw [ite_eq_left ⟨by omega, by omega⟩, Int.toNat_natCast]

theorem storeSlot_nat {s : List (Option Val)} {i : Nat} {x : Option Val} (h : i < s.length) :
    storeSlot false s i x = .ok (s.set i x) := by
  unfold storeSlot
  rw [ite_eq_left ⟨by omega, by omega⟩, Int.toNat_natCast]
  rfl

theorem memmove_ok {s : List (Option Val)} {dst src n : Nat} (hd : dst + n ≤ s.length)
    (hs : src + n ≤ s.length) : memmove false s dst src n = .ok (moveElements s dst src n) := by
  unfold memmove
  rw [ite_eq_right (by decide), ite_eq_left ⟨hd, hs⟩]

theorem memcpy_ok {d s : List (Option Val)} {dst src n : Nat} (hd : dst + n ≤ d.length)
    (hs : src + n ≤ s.length) : memcpy d dst s src n = .ok (blit d dst ((s.drop src).take n)) := by
  unfold memcpy
  rw [ite_eq_left ⟨hd, hs⟩]

theorem castElements_ok {k : Kind} {s : List (Option Val)} (h : k.isDouble = true → s ≠ []) :
    castElements k s = .ok () := by
  unfold castElements
  rw [ite_eq_right]
  intro ⟨h1, h2⟩
  exact h h1 h2

theorem ensureWritable_cow (a : JSArr) : (ensureWritable a).cow = false := by
  unfold ensureWritable
  split
  · rfl
  · simp_all

theorem ensureWritable_kind (a : JSArr) : (ensureWritable a).kind = a.kind := by
  unfold ensureWritable
  split <;> rfl

theorem ensureWritable_length (a : JSArr) : (ensureWritable a).length = a.length := by
  unfold ensureWritable
  split <;> rfl

theorem ensureWritable_flags (a : JSArr) :
    (ensureWritable a).forRead = a.forRead ∧ (ensureWritable a).fast = a.fast ∧
      (ensureWritable a).forCopy = a.forCopy := by
  unfold ensureWritable
  split <;> exact ⟨rfl, rfl, rfl⟩

theorem ensureWritable_elems (a : JSArr) : (ensureWritable a).elems = a.elems := by
  unfold ensureWritable
  split
  · simp [JSArr.elems, List.take_take]
  · rfl

theorem ensureWritable_store_length (a : JSArr) :
    (ensureWritable a).store.length ≤ a.store.length := by
  unfold ensureWritable
  split
  · simp only [List.length_take]
    exact Nat.min_le_right _ _
  · exact Nat.le_refl _

theorem ensureWritable_wf {a : JSArr} (hw : a.WF) : (ensureWritable a).WF := by
  unfold ensureWritable
  split
  · refine ⟨?_, ?_, hw.forRead_fast, hw.fast_forRead, hw.forCopy_fast, fun h => by cases h⟩
    · have := hw.length_le
      simp [List.length_take]
      omega
    · intro x hx
      have : x ∈ a.elems := by simpa [JSArr.elems, List.take_take] using hx
      exact hw.kind_ok x this
  · exact hw

theorem ensureWritable_slack {a : JSArr} (hsl : a.SlackHoles) : (ensureWritable a).SlackHoles := by
  unfold ensureWritable
  split
  · intro x hx
    simp at hx
  · exact hsl

theorem ensureWritableChecked_ok {c : Config} {a : JSArr} (hw : a.WF)
    (hcap : a.store.length ≤ c.maxLen) (hc : c.maxLen ≤ c.smiMax) :
    ensureWritableChecked c a = .ok (ensureWritable a) := by
  have := hw.length_le
  unfold ensureWritableChecked
  split
  · rw [ite_eq_right (by omega)]
  · unfold ensureWritable
    rw [ite_eq_right (by assumption)]

theorem ensureWritableChecked_cases (c : Config) (a : JSArr) :
    ensureWritableChecked c a = .abort ∨ ensureWritableChecked c a = .ok (ensureWritable a) := by
  unfold ensureWritableChecked
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · right
    unfold ensureWritable
    rw [ite_eq_right (by assumption)]

theorem cow_false_of_double {a : JSArr} (hw : a.WF) (hk : a.kind.isDouble = true) :
    a.cow = false := by
  cases h : a.cow
  · rfl
  · have := hw.cow_not_double h
    rw [hk] at this
    cases this

theorem store_eq_elems {b : JSArr} (hsl : b.SlackHoles) :
    b.store = b.elems ++ List.replicate (b.store.length - b.length) none := by
  have hd : b.store.drop b.length = List.replicate (b.store.length - b.length) none := by
    rw [List.eq_replicate_iff]
    exact ⟨by simp [List.length_drop], hsl⟩
  rw [← hd]
  simp [JSArr.elems]

theorem elems_slack_of_store {b : JSArr} {spec : List (Option Val)} {k : Nat}
    (h : b.store = spec ++ List.replicate k none) (hl : b.length = spec.length) :
    b.elems = spec ∧ b.SlackHoles ∧ b.length ≤ b.store.length := by
  refine ⟨?_, ?_, ?_⟩
  · simp [JSArr.elems, h, hl]
  · intro x hx
    rw [h, hl] at hx
    simp at hx
    exact hx.2
  · rw [h, hl]
    simp

theorem eq_append_replicate {t spec : List (Option Val)} (hl : spec.length ≤ t.length)
    (h : ∀ j, j < t.length → t[j]? = some (spec.getD j none)) :
    t = spec ++ List.replicate (t.length - spec.length) none := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_append]
  by_cases h1 : j < t.length
  · rw [h j h1, List.getD_eq_getElem?_getD]
    by_cases h2 : j < spec.length
    · rw [ite_eq_left h2, List.getElem?_eq_getElem h2]
      rfl
    · rw [ite_eq_right h2, List.getElem?_eq_none (by omega), List.getElem?_replicate,
        ite_eq_left (by omega)]
      rfl
  · rw [List.getElem?_eq_none (by omega)]
    by_cases h2 : j < spec.length
    · omega
    · rw [ite_eq_right h2, List.getElem?_replicate, ite_eq_right (by omega)]

theorem getElem?_store {b : JSArr} (hsl : b.SlackHoles) (hl : b.length ≤ b.store.length) {j : Nat}
    (hj : j < b.store.length) : b.store[j]? = some (b.elems.getD j none) := by
  have he : b.elems.length = b.length := by
    simp [JSArr.elems, List.length_take]
    omega
  have h := store_eq_elems hsl
  rw [h, List.getElem?_append, List.getD_eq_getElem?_getD]
  by_cases h1 : j < b.elems.length
  · rw [ite_eq_left h1, List.getElem?_eq_getElem h1]
    rfl
  · rw [ite_eq_right h1, List.getElem?_replicate, ite_eq_left (by omega),
      List.getElem?_eq_none (by omega)]
    rfl

structure KindFits (k0 kf : Kind) (xs : List Val) : Prop where
  fast : kf.isFast = true
  general : ∀ x, kindOk k0 x = true → kindOk kf x = true
  items : ∀ e ∈ xs, kindOk kf (some e) = true
  double : kf.isDouble = true → ∀ e ∈ xs, e.isNumber = true

structure Transitioned (a b : JSArr) (k : Kind) : Prop where
  kind_eq : b.kind = a.kind.transitionTarget k
  store_eq : b.store = a.store
  length_eq : b.length = a.length
  forRead_eq : b.forRead = a.forRead
  fast_eq : b.fast = a.fast
  forCopy_eq : b.forCopy = a.forCopy
  cow_double : b.kind.isDouble = true → b.cow = false
  cow_false : a.cow = false → b.cow = false

theorem transitionTo_spec {c : Config} {a : JSArr} (k : Kind) (hw : a.WF) :
    transitionTo c a k ≠ .ub ∧ ∀ b, transitionTo c a k = .ok b → Transitioned a b k := by
  unfold transitionTo
  dsimp only
  split
  · rename_i h
    refine ⟨nofun, fun b hb => ?_⟩
    cases hb
    exact ⟨h, rfl, rfl, rfl, rfl, rfl, cow_false_of_double hw, id⟩
  split
  · refine ⟨nofun, fun b hb => ?_⟩
    cases hb
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩
  split
  · rename_i h
    refine ⟨nofun, fun b hb => ?_⟩
    cases hb
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun hd => ?_, id⟩
    have hd' : a.kind.isDouble = true := by
      rw [h]
      exact hd
    show a.cow = false
    exact cow_false_of_double hw hd'
  split
  · exact ⟨nofun, fun b hb => by cases hb⟩
  · refine ⟨nofun, fun b hb => ?_⟩
    cases hb
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem transitionTo_ok {c : Config} {a : JSArr} (k : Kind) (hcap : a.store.length ≤ c.maxLen) :
    ∃ b, transitionTo c a k = .ok b := by
  unfold transitionTo
  dsimp only
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  rw [ite_eq_right (by omega)]
  exact ⟨_, rfl⟩

theorem transitionTo_cases {c : Config} {a : JSArr} (k : Kind) (hw : a.WF) :
    transitionTo c a k = .abort ∨ ∃ b, transitionTo c a k = .ok b ∧ Transitioned a b k := by
  have h := transitionTo_spec (c := c) k hw
  cases ht : transitionTo c a k with
  | ok b => exact Or.inr ⟨b, rfl, h.2 b ht⟩
  | ub => exact absurd ht h.1
  | abort => exact Or.inl rfl

theorem newArray_wf {k : Kind} {s : List (Option Val)} (hf : k.isFast = true)
    (hk : ∀ x ∈ s, kindOk k x = true) : (newArray k s).WF where
  length_le := Nat.le_refl _
  kind_ok := by
    intro x hx
    simp only [newArray, JSArr.elems, List.take_length] at hx
    exact hk x hx
  forRead_fast := fun _ => hf
  fast_forRead := fun _ => rfl
  forCopy_fast := fun _ => rfl
  cow_not_double := nofun

theorem newArray_slack (k : Kind) (s : List (Option Val)) : (newArray k s).SlackHoles := by
  intro x hx
  simp [newArray] at hx

theorem newArray_elems (k : Kind) (s : List (Option Val)) : (newArray k s).elems = s := by
  simp [newArray, JSArr.elems]

end InPlace
