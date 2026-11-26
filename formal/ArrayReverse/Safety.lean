import ArrayReverse.Model

namespace ArrayReverse

open Torque InPlace

theorem some_getD {xs : List (Option Val)} {i : Nat} (h : i < xs.length) :
    some (xs.getD i none) = xs[i]? := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem revLoop_ok : ∀ (n : Nat) (s : List (Option Val)) (lo hi : Nat), hi + 1 - lo = n →
    hi < s.length → lo ≤ hi + 1 →
    ∃ t, revLoop false s lo hi = .ok t ∧ t.length = s.length ∧
      ∀ j, t[j]? = if lo ≤ j ∧ j ≤ hi then s[lo + hi - j]? else s[j]?
  | n, s, lo, hi, hn, hs, hle => by
    rw [revLoop]
    by_cases h : (lo : Int) < hi
    · rw [dite_eq_left h]
      have hlt : lo < hi := by omega
      rw [loadSlot_nat (by omega), loadSlot_nat hs]
      simp only [Res.ok_bind]
      rw [storeSlot_nat (by omega), Res.ok_bind, storeSlot_nat (by simp; omega), Res.ok_bind]
      have h1 : (lo : Int) + 1 = ((lo + 1 : Nat) : Int) := by omega
      have h2 : (hi : Int) - 1 = ((hi - 1 : Nat) : Int) := by omega
      rw [h1, h2]
      obtain ⟨t, ht, htl, htj⟩ := revLoop_ok (hi - 1 + 1 - (lo + 1))
        ((s.set lo (s.getD hi none)).set hi (s.getD lo none)) (lo + 1) (hi - 1) rfl
        (by simp; omega) (by omega)
      refine ⟨t, ht, by simpa using htl, ?_⟩
      intro j
      rw [htj j]
      by_cases hj1 : j = lo
      · subst hj1
        rw [ite_eq_right (by omega), ite_eq_left (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by omega), some_getD hs]
        congr 1
        omega
      · by_cases hj2 : j = hi
        · subst hj2
          rw [ite_eq_right (by omega), ite_eq_left (by omega), List.getElem?_set_self (by simp; omega),
            some_getD (by omega)]
          congr 1
          omega
        · by_cases hj3 : lo + 1 ≤ j ∧ j ≤ hi - 1
          · rw [ite_eq_left hj3, ite_eq_left (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega)]
            congr 1
            omega
          · rw [ite_eq_right hj3, ite_eq_right (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega)]
    · rw [dite_eq_right h]
      refine ⟨s, rfl, rfl, ?_⟩
      intro j
      split
      · congr 1
        omega
      · rfl
termination_by n => n
decreasing_by omega

theorem fastReverse_spec {b : JSArr} (hl : b.length ≤ b.store.length) (hcow : b.cow = false) :
    ∃ t, fastReverse b = .done { b with store := t } () ∧ t.length = b.store.length ∧
      ∀ j, t[j]? = if j < b.length then b.store[b.length - 1 - j]? else b.store[j]? := by
  unfold fastReverse
  rw [hcow]
  by_cases h0 : b.length = 0
  · rw [h0]
    have : revLoop false b.store 0 ((0 : Nat) - 1 : Int) = .ok b.store := by
      rw [revLoop]
      rw [dite_eq_right (by omega)]
    rw [this, Res.ok_then]
    refine ⟨b.store, rfl, rfl, ?_⟩
    intro j
    rw [ite_eq_right (by omega)]
  · have he : ((b.length : Int) - 1) = ((b.length - 1 : Nat) : Int) := by omega
    rw [he]
    obtain ⟨t, ht, htl, htj⟩ := revLoop_ok _ b.store 0 (b.length - 1) rfl (by omega) (by omega)
    rw [show ((0 : Nat) : Int) = 0 from rfl] at ht
    rw [ht, Res.ok_then]
    refine ⟨t, rfl, htl, ?_⟩
    intro j
    rw [htj j]
    by_cases hj : j < b.length
    · rw [ite_eq_left (by omega), ite_eq_left hj]
      congr 1
      omega
    · rw [ite_eq_right (by omega), ite_eq_right hj]

theorem getElem?_specReverse (xs : List (Option Val)) (j : Nat) :
    (specReverse xs)[j]? = if j < xs.length then xs[xs.length - 1 - j]? else none := by
  unfold specReverse
  rw [List.getElem?_map]
  by_cases h : j < xs.length
  · rw [List.getElem?_range h, ite_eq_left h, Option.map_some, some_getD (by omega)]
    congr 1
    omega
  · rw [List.getElem?_eq_none (by simp; omega), ite_eq_right h]
    rfl

theorem specReverse_eq_reverse (xs : List (Option Val)) : specReverse xs = xs.reverse := by
  apply List.ext_getElem?
  intro j
  rw [getElem?_specReverse]
  by_cases h : j < xs.length
  · rw [ite_eq_left h, List.getElem?_reverse h]
  · rw [ite_eq_right h, List.getElem?_eq_none (by simp; omega)]

theorem mem_specReverse {xs : List (Option Val)} {x : Option Val} (hx : x ∈ specReverse xs) :
    x ∈ xs := by
  rw [specReverse_eq_reverse] at hx
  exact List.mem_reverse.mp hx

theorem reversed_props {b : JSArr} (hw : b.WF) (hsl : b.SlackHoles) (hcow : b.cow = false)
    {t : List (Option Val)} (htl : t.length = b.store.length)
    (htj : ∀ j, t[j]? = if j < b.length then b.store[b.length - 1 - j]? else b.store[j]?) :
    let b' : JSArr := { b with store := t }
    b'.cow = false ∧ b'.WF ∧ b'.SlackHoles ∧ b'.elems = specReverse b.elems := by
  have hl := hw.length_le
  have hel : b.elems.length = b.length := JSArr.elems_length hw
  have helems : ({ b with store := t } : JSArr).elems = specReverse b.elems := by
    apply List.ext_getElem?
    intro j
    show (t.take b.length)[j]? = _
    rw [List.getElem?_take, getElem?_specReverse, hel]
    by_cases hj : j < b.length
    · rw [ite_eq_left hj, ite_eq_left hj, htj j, ite_eq_left hj]
      simp only [JSArr.elems, List.getElem?_take]
      rw [ite_eq_left (by omega)]
    · rw [ite_eq_right hj, ite_eq_right hj]
  refine ⟨hcow, ⟨?_, ?_, hw.forRead_fast, hw.fast_forRead, hw.forCopy_fast, hw.cow_not_double⟩,
    ?_, helems⟩
  · show b.length ≤ t.length
    omega
  · intro x hx
    rw [helems] at hx
    exact hw.kind_ok x (mem_specReverse hx)
  · intro x hx
    change x ∈ t.drop b.length at hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    rw [List.getElem?_drop, htj, ite_eq_right (by omega)] at hi
    exact hsl x (List.mem_iff_getElem?.mpr ⟨i, by rw [List.getElem?_drop]; exact hi⟩)

theorem fastReverse_done {b : JSArr} (hw : b.WF) (hsl : b.SlackHoles) (hcow : b.cow = false) :
    ∃ b', fastReverse b = .done b' () ∧ b'.kind = b.kind ∧ b'.length = b.length ∧
      b'.cow = false ∧ b'.WF ∧ b'.SlackHoles ∧ b'.elems = specReverse b.elems := by
  obtain ⟨t, ht, htl, htj⟩ := fastReverse_spec hw.length_le hcow
  exact ⟨_, ht, rfl, rfl, reversed_props hw hsl hcow htl htj⟩

theorem fastReverse_ne {b : JSArr} (hl : b.length ≤ b.store.length) (hcow : b.cow = false) :
    fastReverse b ≠ .ub ∧ fastReverse b ≠ .abort := by
  obtain ⟨t, ht, _, _⟩ := fastReverse_spec hl hcow
  rw [ht]
  exact ⟨nofun, nofun⟩

theorem tryFast_slow {c : Config} {a : JSArr} (hf : a.fast = false) : tryFast c a = .slow := by
  unfold tryFast
  rw [ite_eq_left hf]

theorem tryFast_eq {c : Config} {a : JSArr} (hw : a.WF) (hf : a.fast = true) :
    tryFast c a = if a.kind.isDouble then fastReverse a
      else (ensureWritableChecked c a).then fastReverse := by
  have hk := hw.forRead_fast (hw.fast_forRead hf)
  unfold tryFast
  rw [ite_eq_right (by simp [hf])]
  cases h : a.kind <;> simp_all [Kind.isDouble, Kind.isFast]

theorem tryFast_ne_ub {c : Config} {a : JSArr} (hw : a.WF) : tryFast c a ≠ .ub := by
  cases hf : a.fast
  · rw [tryFast_slow hf]
    nofun
  rw [tryFast_eq hw hf]
  split
  · exact (fastReverse_ne hw.length_le (cow_false_of_double hw (by assumption))).1
  · rcases ensureWritableChecked_cases c a with h | h <;> rw [h]
    · nofun
    · exact (fastReverse_ne (ensureWritable_wf hw).length_le (ensureWritable_cow a)).1

theorem tryFast_ne_abort {c : Config} {a : JSArr} (hw : a.WF) (hcap : a.store.length ≤ c.maxLen)
    (hc : c.maxLen ≤ c.smiMax) : tryFast c a ≠ .abort := by
  cases hf : a.fast
  · rw [tryFast_slow hf]
    nofun
  rw [tryFast_eq hw hf]
  split
  · exact (fastReverse_ne hw.length_le (cow_false_of_double hw (by assumption))).2
  · rw [ensureWritableChecked_ok hw hcap hc, Res.ok_then]
    exact (fastReverse_ne (ensureWritable_wf hw).length_le (ensureWritable_cow a)).2

theorem tryFast_done {c : Config} {a a' : JSArr} {r : Unit} (hw : a.WF) (hsl : a.SlackHoles)
    (h : tryFast c a = .done a' r) :
    a'.kind = a.kind ∧ a'.length = a.length ∧ a'.cow = false ∧ a'.WF ∧ a'.SlackHoles ∧
      a'.elems = specReverse a.elems := by
  cases hf : a.fast
  · rw [tryFast_slow hf] at h
    cases h
  rw [tryFast_eq hw hf] at h
  split at h
  · obtain ⟨b', hb', hk, hl, hcw, hwf, hs, he⟩ :=
      fastReverse_done hw hsl (cow_false_of_double hw (by assumption))
    rw [hb'] at h
    cases h
    exact ⟨hk, hl, hcw, hwf, hs, he⟩
  · obtain ⟨b', hb', hk, hl, hcw, hwf, hs, he⟩ :=
      fastReverse_done (ensureWritable_wf hw) (ensureWritable_slack hsl) (ensureWritable_cow a)
    rw [ensureWritable_kind] at hk
    rw [ensureWritable_length] at hl
    rw [ensureWritable_elems] at he
    rcases ensureWritableChecked_cases c a with h' | h' <;> rw [h'] at h
    · cases h
    · rw [Res.ok_then, hb'] at h
      cases h
      exact ⟨hk, hl, hcw, hwf, hs, he⟩

theorem tryFast_handles {c : Config} {a : JSArr} (hw : a.WF) (hcap : a.store.length ≤ c.maxLen)
    (hc : c.maxLen ≤ c.smiMax) (hf : a.fast = true) : ∃ a', tryFast c a = .done a' () := by
  have hesl : ∀ b : JSArr, b.length ≤ b.store.length → b.cow = false →
      ∃ b', fastReverse b = .done b' () := fun b hl hcow => by
    obtain ⟨t, ht, _, _⟩ := fastReverse_spec hl hcow
    exact ⟨_, ht⟩
  rw [tryFast_eq hw hf]
  split
  · exact hesl _ hw.length_le (cow_false_of_double hw (by assumption))
  · rw [ensureWritableChecked_ok hw hcap hc, Res.ok_then]
    exact hesl _ (ensureWritable_wf hw).length_le (ensureWritable_cow a)

end ArrayReverse
