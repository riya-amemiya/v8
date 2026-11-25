import ArrayCopyWithin.Model

namespace ArrayCopyWithin

open Torque

theorem some_getD {xs : List (Option Val)} {i : Nat} (h : i < xs.length) :
    some (xs.getD i none) = xs[i]? := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem moveElements_zero {xs : List (Option Val)} {dst src : Nat} (hd : dst ≤ xs.length)
    (hs : src ≤ xs.length) : moveElements xs dst src 0 = xs := by
  apply List.ext_getElem?
  intro j
  rw [getElem?_moveElements (by omega) (by omega)]
  rw [ite_eq_right (by omega)]

theorem copyFwd_eq : ∀ (n : Nat) (xs : List (Option Val)) (dst src : Nat),
    dst + n ≤ xs.length → src + n ≤ xs.length → (dst ≤ src ∨ src + n ≤ dst) →
    copyFwd xs dst src n = moveElements xs dst src n
  | 0, xs, dst, src, hd, hs, _ => by
    rw [copyFwd, moveElements_zero (by omega) (by omega)]
  | n + 1, xs, dst, src, hd, hs, hdir => by
    rw [copyFwd, copyFwd_eq n _ (dst + 1) (src + 1) (by simp; omega) (by simp; omega)
      (by omega)]
    apply List.ext_getElem?
    intro j
    rw [getElem?_moveElements (by simp; omega) (by simp; omega), getElem?_moveElements hd hs]
    rcases Nat.lt_or_ge j dst with h1 | h1
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), List.getElem?_set_ne (by omega)]
    · rcases Nat.eq_or_lt_of_le h1 with h2 | h2
      · subst h2
        rw [ite_eq_right (by omega), ite_eq_left (by omega), List.getElem?_set_self (by omega),
          Nat.sub_self, Nat.add_zero, some_getD (by omega)]
      · by_cases h3 : j < dst + (n + 1)
        · rw [ite_eq_left (by omega), ite_eq_left (by omega), List.getElem?_set_ne (by omega)]
          congr 1
          omega
        · rw [ite_eq_right (by omega), ite_eq_right (by omega), List.getElem?_set_ne (by omega)]

theorem copyBwd_eq : ∀ (n : Nat) (xs : List (Option Val)) (dst src : Nat),
    dst + n ≤ xs.length → src + n ≤ xs.length → src ≤ dst →
    copyBwd xs dst src n = moveElements xs dst src n
  | 0, xs, dst, src, hd, hs, _ => by
    rw [copyBwd, moveElements_zero (by omega) (by omega)]
  | n + 1, xs, dst, src, hd, hs, hdir => by
    rw [copyBwd, copyBwd_eq n _ dst src (by simp; omega) (by simp; omega) hdir]
    apply List.ext_getElem?
    intro j
    rw [getElem?_moveElements (by simp; omega) (by simp; omega), getElem?_moveElements hd hs]
    by_cases h1 : dst ≤ j ∧ j < dst + n
    · rw [ite_eq_left h1, ite_eq_left (by omega), List.getElem?_set_ne (by omega)]
    · by_cases h2 : j = dst + n
      · subst h2
        rw [ite_eq_right h1, ite_eq_left (by omega), List.getElem?_set_self (by omega),
          some_getD (by omega)]
        congr 1
        omega
      · rw [ite_eq_right h1, List.getElem?_set_ne (by omega)]
        by_cases h3 : dst ≤ j ∧ j < dst + (n + 1)
        · omega
        · rw [ite_eq_right h3]

theorem specCopy_eq {xs : List (Option Val)} {dst src c : Nat} (hc : 0 < c)
    (hd : dst + c ≤ xs.length) (hs : src + c ≤ xs.length) :
    specCopy xs dst src c = moveElements xs dst src c := by
  unfold specCopy
  rw [ite_eq_right (by omega), Int.toNat_natCast]
  split
  · exact copyBwd_eq c xs dst src hd hs (by omega)
  · exact copyFwd_eq c xs dst src hd hs (by omega)

theorem take_moveElements {store : List (Option Val)} {dst src c L : Nat}
    (hd : dst + c ≤ L) (hs : src + c ≤ L) (hL : L ≤ store.length) :
    (moveElements store dst src c).take L = moveElements (store.take L) dst src c := by
  have hlen : (store.take L).length = L := by
    simp [List.length_take]
    omega
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take, getElem?_moveElements (by omega) (by omega),
    getElem?_moveElements (by omega) (by omega)]
  by_cases h1 : dst ≤ j ∧ j < dst + c
  · rw [ite_eq_left (by omega), ite_eq_left h1, ite_eq_left h1, List.getElem?_take,
      ite_eq_left (by omega)]
  · rw [ite_eq_right h1, ite_eq_right h1, List.getElem?_take]

theorem mem_moveElements {xs : List (Option Val)} {dst src c : Nat} (hd : dst + c ≤ xs.length)
    (hs : src + c ≤ xs.length) {x : Option Val} (hx : x ∈ moveElements xs dst src c) :
    x ∈ xs := by
  rw [List.mem_iff_getElem?] at hx ⊢
  obtain ⟨j, hj⟩ := hx
  rw [getElem?_moveElements hd hs] at hj
  split at hj
  · exact ⟨_, hj⟩
  · exact ⟨_, hj⟩

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

theorem ensureWritable_elems (a : JSArr) : (ensureWritable a).elems = a.elems := by
  unfold ensureWritable
  split
  · simp [JSArr.elems, List.take_take]
  · rfl

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

theorem moveChecked_done {b : JSArr} (hw : b.WF) (hcow : b.cow = false) {dst src c : Nat}
    (hd : dst + c ≤ b.length) (hs : src + c ≤ b.length) :
    moveChecked b dst src c = .done { b with store := moveElements b.store dst src c } := by
  have := hw.length_le
  unfold moveChecked
  rw [ite_eq_right (by simp [hcow]), ite_eq_left (by omega)]
  simp

theorem moved_props {a b : JSArr} (hw : b.WF) (hk : b.kind = a.kind) (hl : b.length = a.length)
    (he : b.elems = a.elems) {dst src c : Nat} (hc : 0 < c) (hd : dst + c ≤ b.length)
    (hs : src + c ≤ b.length) :
    let a' := { b with store := moveElements b.store dst src c }
    a'.kind = a.kind ∧ a'.length = a.length ∧ a'.WF ∧ a'.elems = specCopy a.elems dst src c := by
  have hlb := hw.length_le
  have hel : b.elems.length = b.length := JSArr.elems_length hw
  have hsp : moveElements b.elems dst src c = specCopy a.elems dst src c := by
    rw [← he, specCopy_eq hc (by omega) (by omega)]
  have helems : ({ b with store := moveElements b.store dst src c } : JSArr).elems =
      specCopy a.elems dst src c := by
    show (moveElements b.store dst src c).take b.length = _
    rw [take_moveElements hd hs hlb, ← hsp]
    rfl
  refine ⟨hk, hl, ⟨?_, ?_, hw.forRead_fast, hw.fast_forRead, hw.forCopy_fast,
    hw.cow_not_double⟩, helems⟩
  · show b.length ≤ (moveElements b.store dst src c).length
    rw [length_moveElements (by omega)]
    exact hlb
  · intro x hx
    rw [helems, ← hsp] at hx
    exact hw.kind_ok x (mem_moveElements (by omega) (by omega) hx)

theorem passes_checks {r : SmiRepr} (hr : r.shift < r.width) {a : JSArr} {dst src c : Nat}
    (hlen : a.length ≤ r.max)
    (hsmi : ¬(r.isSmi dst && r.isSmi src && r.isSmi (c : Int)) = false)
    (hdst : ¬SmiRepr.above (r.add dst c) (r.word a.length) = true)
    (hsrc : ¬SmiRepr.above (r.add src c) (r.word a.length) = true) :
    dst + c ≤ a.length ∧ src + c ≤ a.length := by
  simp only [Bool.not_eq_false, Bool.and_eq_true, SmiRepr.isSmi, decide_eq_true_eq] at hsmi
  obtain ⟨⟨⟨_, h1⟩, ⟨_, h2⟩⟩, ⟨_, h3⟩⟩ := hsmi
  have h1' : dst ≤ r.max := by omega
  have h2' : src ≤ r.max := by omega
  have h3' : c ≤ r.max := by omega
  rw [SmiRepr.above_add_iff hr h1' h3' hlen] at hdst
  rw [SmiRepr.above_add_iff hr h2' h3' hlen] at hsrc
  omega

theorem cow_false_of_double {a : JSArr} (hw : a.WF) (hk : a.kind.isDouble = true) :
    a.cow = false := by
  cases h : a.cow
  · rfl
  · have := hw.cow_not_double h
    rw [hk] at this
    cases this

theorem tryFast_ok {r : SmiRepr} (hr : r.shift < r.width) {a a' : JSArr} (hw : a.WF)
    (hlen : a.length ≤ r.max) (dst src : Nat) (count : Int)
    (h : tryFast r a dst src count = .done a') :
    a'.kind = a.kind ∧ a'.length = a.length ∧ a'.WF ∧
      a'.elems = specCopy a.elems dst src count := by
  by_cases hc : count ≤ 0
  · simp only [tryFast, ite_eq_left hc] at h
    cases h
    exact ⟨rfl, rfl, hw, by simp [specCopy, hc]⟩
  obtain ⟨c, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : Int) ≤ count by omega)
  have hc0 : 0 < c := by omega
  unfold tryFast at h
  rw [ite_eq_right hc] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hsmi
  split at h
  · cases h
  rename_i hdst
  split at h
  · cases h
  rename_i hsrc
  obtain ⟨hd, hs⟩ := passes_checks hr hlen hsmi hdst hsrc
  have hew := ensureWritable_wf hw
  have hel := ensureWritable_length a
  split at h
  all_goals first
    | (cases h; done)
    | (rw [moveChecked_done hew (ensureWritable_cow a) (by omega) (by omega)] at h
       cases h
       exact moved_props hew (ensureWritable_kind a) hel (ensureWritable_elems a) hc0
         (by omega) (by omega))
    | (rw [moveChecked_done hw (cow_false_of_double hw (by simp [*, Kind.isDouble]))
         (by omega) (by omega)] at h
       cases h
       exact moved_props hw rfl rfl rfl hc0 (by omega) (by omega))

theorem tryFast_ne_ub {r : SmiRepr} (hr : r.shift < r.width) {a : JSArr} (hw : a.WF)
    (hlen : a.length ≤ r.max) (dst src : Nat) (count : Int) :
    tryFast r a dst src count ≠ .ub := by
  intro h
  by_cases hc : count ≤ 0
  · simp [tryFast, hc] at h
  obtain ⟨c, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : Int) ≤ count by omega)
  unfold tryFast at h
  rw [ite_eq_right hc] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hsmi
  split at h
  · cases h
  rename_i hdst
  split at h
  · cases h
  rename_i hsrc
  obtain ⟨hd, hs⟩ := passes_checks hr hlen hsmi hdst hsrc
  have hew := ensureWritable_wf hw
  have hel := ensureWritable_length a
  split at h
  all_goals first
    | (cases h; done)
    | (rw [moveChecked_done hew (ensureWritable_cow a) (by omega) (by omega)] at h
       cases h)
    | (rw [moveChecked_done hw (cow_false_of_double hw (by simp [*, Kind.isDouble]))
         (by omega) (by omega)] at h
       cases h)

theorem fastPath_ne_ub {r : SmiRepr} (hr : r.shift < r.width) {a : JSArr} (hw : a.WF)
    (hlen : a.length ≤ r.max) (len : Nat) (args : Args) : fastPath r a len args ≠ .ub :=
  tryFast_ne_ub hr hw hlen _ _ _

theorem fastPath_ok {r : SmiRepr} (hr : r.shift < r.width) {a a' : JSArr} (hw : a.WF)
    (hlen : a.length ≤ r.max) {len : Nat} {args : Args} (h : fastPath r a len args = .done a') :
    a'.kind = a.kind ∧ a'.length = a.length ∧ a'.WF ∧
      a'.elems = specCopy a.elems (targetIndex len args) (startIndex len args) (count len args) :=
  tryFast_ok hr hw hlen _ _ _ h

end ArrayCopyWithin
