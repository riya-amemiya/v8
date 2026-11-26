import ArrayCopyCommon.Basic

namespace ArrayCopyCommon

open Torque

theorem blit_zero_full {buf src : List (Option Val)} (h : src.length = buf.length) :
    blit buf 0 src = src := by
  simp [blit, h]

theorem copyElements_eq {dst src : List (Option Val)} {di si n : Nat}
    (hd : di + n ≤ dst.length) (hs : si + n ≤ src.length) :
    copyElements dst di src si n = some (blit dst di ((src.drop si).take n)) := by
  simp [copyElements, hd, hs]

theorem length_take_drop {src : List (Option Val)} {si n : Nat} (hs : si + n ≤ src.length) :
    ((src.drop si).take n).length = n := by
  simp [List.length_take, List.length_drop]
  omega

theorem getElem?_specSlice (xs : List (Option Val)) (k n i : Nat) :
    (specSlice xs k n)[i]? = if i < n then some (xs.getD (k + i) none) else none := by
  unfold specSlice
  rw [List.getElem?_map]
  by_cases h : i < n
  · rw [List.getElem?_range h, ite_eq_left h]
    rfl
  · rw [List.getElem?_eq_none (by simp; omega), ite_eq_right h]
    rfl

theorem length_specSlice (xs : List (Option Val)) (k n : Nat) : (specSlice xs k n).length = n := by
  simp [specSlice]

theorem specSlice_zero (xs : List (Option Val)) (k : Nat) : specSlice xs k 0 = [] := rfl

theorem take_drop_eq_specSlice {xs : List (Option Val)} {k n : Nat} (h : k + n ≤ xs.length) :
    (xs.drop k).take n = specSlice xs k n := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_drop, getElem?_specSlice, List.getD_eq_getElem?_getD]
  by_cases hi : i < n
  · rw [ite_eq_left hi, ite_eq_left hi, List.getElem?_eq_getElem (by omega)]
    rfl
  · rw [ite_eq_right hi, ite_eq_right hi]

theorem specSlice_store {a : JSArr} {k n : Nat}
    (h : k + n ≤ a.length) : specSlice a.store k n = specSlice a.elems k n := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_specSlice, getElem?_specSlice]
  by_cases hi : i < n
  · rw [ite_eq_left hi, ite_eq_left hi, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [JSArr.elems, List.getElem?_take]
    rw [ite_eq_left (by omega)]
  · rw [ite_eq_right hi, ite_eq_right hi]

theorem specSlice_full {xs : List (Option Val)} {n : Nat} (h : xs.length = n) :
    specSlice xs 0 n = xs := by
  rw [← take_drop_eq_specSlice (by omega)]
  simp [← h]

theorem mem_specSlice {xs : List (Option Val)} {k n : Nat} (h : k + n ≤ xs.length)
    {x : Option Val} (hx : x ∈ specSlice xs k n) : x ∈ xs := by
  rw [← take_drop_eq_specSlice h] at hx
  exact List.mem_of_mem_drop (List.mem_of_mem_take hx)

theorem newArray_elems (k : Kind) (s : List (Option Val)) : (newArray k s).elems = s := by
  simp [newArray, JSArr.elems]

theorem newArray_wf {k : Kind} {s : List (Option Val)} (hf : k.isFast = true)
    (hk : ∀ x ∈ s, kindOk k x = true) : (newArray k s).WF where
  length_le := Nat.le_refl _
  kind_ok := by
    rw [newArray_elems]
    exact hk
  forRead_fast := fun _ => hf
  fast_forRead := fun _ => rfl
  forCopy_fast := fun _ => rfl
  cow_not_double := nofun

theorem newArray_slack (k : Kind) (s : List (Option Val)) : (newArray k s).SlackHoles := by
  intro x hx
  simp [newArray] at hx

theorem extractFast_eq {lim : Limits} {a : JSArr} (hf : a.fast = true) (hl : a.length ≤ a.store.length)
    {k n : Nat} (h : k + n ≤ a.length) (hm : n ≤ lim.maxLen) :
    extractFast lim a k n = .done a (newArray a.kind (specSlice a.elems k n)) := by
  unfold extractFast
  rw [ite_eq_right (by simp [hf])]
  by_cases h0 : n = 0
  · subst h0
    rw [ite_eq_left rfl]
    rfl
  · rw [ite_eq_right h0, ite_eq_right (by omega),
      copyElements_eq (by simp) (by omega),
      blit_zero_full (by rw [length_take_drop (by omega)]; simp),
      take_drop_eq_specSlice (by omega), specSlice_store h]

theorem kindOk_specSlice {a : JSArr} (hw : a.WF) {k n : Nat} (h : k + n ≤ a.length) :
    ∀ x ∈ specSlice a.elems k n, kindOk a.kind x = true := by
  intro x hx
  exact hw.kind_ok x (mem_specSlice (by rw [JSArr.elems_length hw]; exact h) hx)

theorem kindOk_packed_some {k : Kind} (hk : isFastPacked k = true) {x : Option Val}
    (h : kindOk k x = true) : x ≠ none := by
  intro hx
  subst hx
  cases k <;> simp_all [isFastPacked, kindOk]

theorem isFast_of_isFastPacked {k : Kind} (hk : isFastPacked k = true) : k.isFast = true := by
  cases k <;> simp_all [isFastPacked, Kind.isFast]

theorem holeToUndef_some (v : Val) : holeToUndef (some v) = v := rfl

theorem getOrUndef_of_some {xs : List (Option Val)} {i : Nat} {v : Val}
    (h : xs[i]? = some (some v)) : getOrUndef xs i = v := by
  simp [getOrUndef, List.getD_eq_getElem?_getD, h, holeToUndef]

theorem storeChecked_eq {buf : List (Option Val)} {i : Nat} (h : i < buf.length) (v : Val) :
    storeChecked buf i v = some (buf.set i (some v)) := by
  simp [storeChecked, h]

end ArrayCopyCommon
