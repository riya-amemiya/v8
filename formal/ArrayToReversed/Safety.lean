import ArrayToReversed.Model

namespace ArrayToReversed

open Torque ArrayCopyCommon

def written (f : Nat → Val) (init : List (Option Val)) (k : Nat) : List (Option Val) :=
  (List.range k).map (fun i => some (f i)) ++ init.drop k

theorem getElem?_written {f : Nat → Val} {init : List (Option Val)} {k : Nat} (j : Nat) :
    (written f init k)[j]? = if j < k then some (some (f j)) else init[j]? := by
  unfold written
  rw [List.getElem?_append]
  simp only [List.length_map, List.length_range]
  by_cases hj : j < k
  · rw [ite_eq_left hj, ite_eq_left hj, List.getElem?_map, List.getElem?_range hj]
    rfl
  · rw [ite_eq_right hj, ite_eq_right hj, List.getElem?_drop]
    congr 1
    omega

theorem length_written {f : Nat → Val} {init : List (Option Val)} {k : Nat}
    (hk : k ≤ init.length) : (written f init k).length = init.length := by
  simp [written, List.length_drop]
  omega

theorem written_set {f : Nat → Val} {init : List (Option Val)} {k : Nat}
    (hk : k < init.length) :
    (written f init k).set k (some (f k)) = written f init (k + 1) := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set, length_written (by omega), getElem?_written, getElem?_written]
  by_cases h1 : k = j
  · subst h1
    rw [ite_eq_left rfl, ite_eq_left hk, ite_eq_left (by omega)]
  · rw [ite_eq_right h1]
    by_cases h2 : j < k
    · rw [ite_eq_left h2, ite_eq_left (by omega)]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem written_full {f : Nat → Val} {init : List (Option Val)} :
    written f init init.length = (List.range init.length).map fun i => some (f i) := by
  simp [written]

theorem none_not_mem_written {f : Nat → Val} {init : List (Option Val)} {k : Nat}
    (hi : ∀ x ∈ init, x ≠ none) : none ∉ written f init k := by
  intro hm
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  rw [getElem?_written] at hj
  split at hj
  · cases hj
  · exact hi none (List.mem_iff_getElem?.mpr ⟨j, hj⟩) rfl

theorem revLoop_ok {load : Nat → Load} {f : Nat → Val} {init : List (Option Val)}
    (hload : ∀ k < init.length, ∃ al, load (init.length - k - 1) = .val (f k) al ∧
      (al = true → ∀ x ∈ init, x ≠ none)) :
    ∀ n k, k + n = init.length →
      revLoop load init.length n k (written f init k) =
        .ok ((List.range init.length).map fun i => some (f i))
  | 0, k, hk => by
    rw [revLoop, show k = init.length by omega, written_full]
  | n + 1, k, hk => by
    obtain ⟨al, hl, hal⟩ := hload k (by omega)
    rw [revLoop, hl]
    simp only
    have hgc : ¬(al = true ∧ none ∈ written f init k) := by
      intro ⟨ha, hm⟩
      exact none_not_mem_written (hal ha) hm
    rw [ite_eq_right hgc, storeChecked_eq (by rw [length_written (by omega)]; omega),
      written_set (by omega)]
    exact revLoop_ok hload n (k + 1) (by omega)

theorem written_zero (f : Nat → Val) (init : List (Option Val)) : written f init 0 = init := by
  simp [written]

def revVal (a : JSArr) (k : Nat) : Val := holeToUndef (a.elems.getD (a.length - k - 1) none)

theorem specReversed_eq {a : JSArr} (hw : a.WF) :
    (List.range a.length).map (fun i => some (revVal a i)) = specReversed a.elems := by
  have hel := JSArr.elems_length hw
  apply List.ext_getElem?
  intro i
  unfold specReversed
  rw [List.getElem?_map, List.getElem?_map]
  by_cases hi : i < a.length
  · rw [List.getElem?_range hi, List.getElem?_reverse (by omega), hel,
      show a.length - 1 - i = a.length - i - 1 by omega]
    unfold revVal
    simp only [Option.map_some, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    rfl

theorem store_getElem? {a : JSArr} (hw : a.WF) {i : Nat} (hi : i < a.length) :
    a.store[i]? = some (a.elems.getD i none) := by
  have hl := hw.length_le
  rw [List.getD_eq_getElem?_getD]
  simp only [JSArr.elems, List.getElem?_take]
  rw [ite_eq_left hi, List.getElem?_eq_getElem (by omega)]
  rfl

theorem elem_mem {a : JSArr} (hw : a.WF) {i : Nat} (hi : i < a.length) :
    a.elems.getD i none ∈ a.elems := by
  have hel := JSArr.elems_length hw
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

theorem load_tagged {a : JSArr} (hw : a.WF) (init : List (Option Val)) :
    ∀ k < a.length, ∃ al, loadTagged a.store (a.length - k - 1) = .val (revVal a k) al ∧
      (al = true → ∀ x ∈ init, x ≠ none) := by
  intro k hk
  refine ⟨false, ?_, nofun⟩
  unfold loadTagged revVal
  rw [store_getElem? hw (by omega)]

theorem load_packedDouble {a : JSArr} (hw : a.WF) (hk : a.kind = .packedDouble)
    (init : List (Option Val)) :
    ∀ k < a.length, ∃ al, loadPackedDouble a.store (a.length - k - 1) = .val (revVal a k) al ∧
      (al = true → ∀ x ∈ init, x ≠ none) := by
  intro k hk'
  refine ⟨false, ?_, nofun⟩
  obtain ⟨v, hv, hn⟩ := packedDouble_elem hw hk (elem_mem hw (i := a.length - k - 1) (by omega))
  unfold loadPackedDouble revVal
  rw [store_getElem? hw (by omega), hv]
  have : v ≠ .undef := by
    intro h
    subst h
    simp [Val.isNumber] at hn
  simp only [this, ite_false, holeToUndef]

theorem load_holeyDouble {a : JSArr} (init : List (Option Val)) (hw : a.WF)
    (hi : ∀ x ∈ init, x ≠ none) :
    ∀ k < a.length, ∃ al, loadHoleyDouble a.store (a.length - k - 1) = .val (revVal a k) al ∧
      (al = true → ∀ x ∈ init, x ≠ none) := by
  intro k hk
  unfold loadHoleyDouble revVal
  rw [store_getElem? hw (by omega)]
  cases h : a.elems.getD (a.length - k - 1) none with
  | none => exact ⟨false, rfl, nofun⟩
  | some v =>
    by_cases hu : v = .undef
    · subst hu
      exact ⟨false, by simp [holeToUndef], nofun⟩
    · exact ⟨true, by simp [hu, holeToUndef], fun _ => hi⟩

theorem copyReversed_ok {lim : Limits} {a : JSArr} {kind : Kind} {load : Nat → Load} {init : Bool}
    (hw : a.WF) (hm : a.length ≤ lim.maxLen)
    (hload : ∀ k < a.length, ∃ al, load (a.length - k - 1) = .val (revVal a k) al ∧
      (al = true → ∀ x ∈ (if init then List.replicate a.length (some (Val.smi 0))
        else List.replicate a.length none), x ≠ none)) :
    copyReversed lim a kind load init = .done a (newArray kind (specReversed a.elems)) := by
  unfold copyReversed
  rw [ite_eq_right (by omega)]
  simp only
  generalize hb : (if init = true then List.replicate a.length (some (Val.smi 0))
    else List.replicate a.length none) = buf at hload
  have hbl : buf.length = a.length := by
    rw [← hb]
    split <;> simp
  rw [hbl.symm] at hload
  have hr := revLoop_ok (init := buf) hload buf.length 0 (by omega)
  rw [written_zero, hbl, specReversed_eq hw] at hr
  rw [hr]
  simp only
  have hnone : none ∉ specReversed a.elems := by
    intro hm
    simp [specReversed] at hm
  rw [ite_eq_right hnone]

theorem kindOk_specReversed {a : JSArr} (hw : a.WF) (hf : a.kind.isFast = true) :
    ∀ x ∈ specReversed a.elems, kindOk (resultKind a.kind) x = true := by
  intro x hx
  simp only [specReversed, List.mem_map, List.mem_reverse] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hk := hw.kind_ok y hy
  cases hka : a.kind <;> rw [hka] at hk <;>
    rcases y with _ | v <;> simp_all [kindOk, resultKind, holeToUndef, Kind.isFast]

theorem tryFast_cases {lim : Limits} {a : JSArr} (hw : a.WF) (hm : a.length ≤ lim.maxLen) :
    tryFast lim a = .slow ∨ (a.length = 0 ∧ tryFast lim a = .done a (newArray .packedSmi [])) ∨
      (a.kind.isFast = true ∧ tryFast lim a = .done a (newArray (resultKind a.kind) (specReversed a.elems))) := by
  unfold tryFast
  by_cases hf : a.fast = false
  · rw [ite_eq_left hf]
    exact Or.inl rfl
  rw [ite_eq_right hf]
  by_cases h0 : a.length = 0
  · rw [ite_eq_left h0]
    exact Or.inr (Or.inl ⟨h0, rfl⟩)
  rw [ite_eq_right h0]
  have hrep : ∀ x ∈ List.replicate a.length (some (Val.smi 0)), x ≠ none := by
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    nofun
  cases hk : a.kind with
  | packedSmi =>
    exact Or.inr (Or.inr ⟨rfl, copyReversed_ok hw hm (load_tagged hw _)⟩)
  | packedElem =>
    exact Or.inr (Or.inr ⟨rfl, copyReversed_ok hw hm (load_tagged hw _)⟩)
  | packedDouble =>
    exact Or.inr (Or.inr ⟨rfl, copyReversed_ok hw hm (load_packedDouble hw hk _)⟩)
  | holeySmi =>
    exact Or.inr (Or.inr ⟨rfl, copyReversed_ok hw hm (load_tagged hw _)⟩)
  | holeyElem =>
    exact Or.inr (Or.inr ⟨rfl, copyReversed_ok hw hm (load_tagged hw _)⟩)
  | holeyDouble =>
    exact Or.inr (Or.inr ⟨rfl, copyReversed_ok hw hm (load_holeyDouble _ hw hrep)⟩)
  | slow => exact Or.inl rfl

theorem tryFast_ne_ub {lim : Limits} {a : JSArr} (hw : a.WF) (hcap : a.store.length ≤ lim.maxLen) :
    tryFast lim a ≠ .ub := by
  rcases tryFast_cases hw (Nat.le_trans hw.length_le hcap) with h | ⟨_, h⟩ | ⟨_, h⟩ <;>
    rw [h] <;> nofun

theorem tryFast_ne_abort {lim : Limits} {a : JSArr} (hw : a.WF)
    (hcap : a.store.length ≤ lim.maxLen) : tryFast lim a ≠ .abort := by
  rcases tryFast_cases hw (Nat.le_trans hw.length_le hcap) with h | ⟨_, h⟩ | ⟨_, h⟩ <;>
    rw [h] <;> nofun

theorem tryFast_done {lim : Limits} {a src res : JSArr} (hw : a.WF)
    (hcap : a.store.length ≤ lim.maxLen) (h : tryFast lim a = .done src res) :
    src = a ∧ res.WF ∧ res.SlackHoles ∧ res.cow = false ∧ isFastPacked res.kind = true ∧
      res.length = a.length ∧ res.elems = specReversed a.elems := by
  rcases tryFast_cases hw (Nat.le_trans hw.length_le hcap) with h' | ⟨h0, h'⟩ | ⟨hf, h'⟩ <;>
    rw [h'] at h
  · cases h
  · cases h
    have he : a.elems = [] := List.eq_nil_of_length_eq_zero (by rw [JSArr.elems_length hw]; exact h0)
    refine ⟨rfl, newArray_wf rfl (by simp), newArray_slack _ _, rfl, rfl, by simp [newArray, h0], ?_⟩
    rw [newArray_elems, he]
    rfl
  · cases h
    refine ⟨rfl, newArray_wf ?_ (kindOk_specReversed hw hf), newArray_slack _ _, rfl, ?_, ?_,
      newArray_elems _ _⟩
    · cases a.kind <;> rfl
    · cases a.kind <;> rfl
    · simp [newArray, specReversed, JSArr.elems_length hw]

end ArrayToReversed
