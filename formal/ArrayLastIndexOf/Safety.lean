import ArrayLastIndexOf.Model

namespace ArrayLastIndexOf

open Torque

theorem scanDown_congr {test : Option Val → Bool} {g1 g2 : Nat → Option (Option Val)} :
    ∀ k, (∀ i ≤ k, ∃ x1 x2, g1 i = some x1 ∧ g2 i = some x2 ∧ test x1 = test x2) →
      scanDown test g1 k = scanDown test g2 k
  | 0, h => by
    obtain ⟨x1, x2, h1, h2, ht⟩ := h 0 (Nat.le_refl 0)
    unfold scanDown
    rw [h1, h2]
    simp only [ht]
  | k + 1, h => by
    obtain ⟨x1, x2, h1, h2, ht⟩ := h (k + 1) (Nat.le_refl _)
    have ih := scanDown_congr k (fun i hi => h i (by omega))
    rw [scanDown, scanDown, h1, h2]
    simp only [ht, ih]

theorem scanDown_skip {test : Option Val → Bool} {g : Nat → Option (Option Val)} (m : Nat) :
    ∀ d, (∀ i, m < i → i ≤ m + d → ∃ x, g i = some x ∧ test x = false) →
      scanDown test g (m + d) = scanDown test g m
  | 0, _ => rfl
  | d + 1, h => by
    obtain ⟨x, hx, ht⟩ := h (m + d + 1) (by omega) (by omega)
    have ih := scanDown_skip m d (fun i h1 h2 => h i h1 (by omega))
    rw [show m + (d + 1) = (m + d) + 1 by omega, scanDown, hx]
    simp only [ht, Bool.false_eq_true, ite_false, ih]

theorem scanDown_some {test : Option Val → Bool} {g : Nat → Option (Option Val)} :
    ∀ k, (∀ i ≤ k, ∃ x, g i = some x) → ∃ r, scanDown test g k = some r
  | 0, h => by
    obtain ⟨x, hx⟩ := h 0 (Nat.le_refl 0)
    rw [scanDown, hx]
    dsimp only
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  | k + 1, h => by
    obtain ⟨x, hx⟩ := h (k + 1) (Nat.le_refl _)
    rw [scanDown, hx]
    dsimp only
    split
    · exact ⟨_, rfl⟩
    · exact scanDown_some k (fun i hi => h i (by omega))

theorem scanDown_none {test : Option Val → Bool} {g : Nat → Option (Option Val)} :
    ∀ k, (∀ i ≤ k, ∃ x, g i = some x ∧ test x = false) → scanDown test g k = some (-1)
  | 0, h => by
    obtain ⟨x, hx, ht⟩ := h 0 (Nat.le_refl 0)
    rw [scanDown, hx]
    simp [ht]
  | k + 1, h => by
    obtain ⟨x, hx, ht⟩ := h (k + 1) (Nat.le_refl _)
    rw [scanDown, hx]
    simp only [ht, Bool.false_eq_true, ite_false]
    exact scanDown_none k (fun i hi => h i (by omega))

theorem getD_elems {a : JSArr} (hw : a.WF) (hsl : a.SlackHoles) {i : Nat}
    (hi : i < a.store.length) : a.elems.getD i none = a.store[i] := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < a.length
  · simp [JSArr.elems, h, List.getElem?_eq_getElem hi]
  · rw [List.getElem?_eq_none (by rw [JSArr.elems_length hw]; omega)]
    have hm : a.store[i] ∈ a.store.drop a.length := by
      rw [List.mem_iff_getElem?]
      exact ⟨i - a.length, by rw [List.getElem?_drop, show a.length + (i - a.length) = i by omega,
        List.getElem?_eq_getElem hi]⟩
    rw [hsl _ hm]
    rfl

theorem getD_elems_out {a : JSArr} (hw : a.WF) {i : Nat} (hi : a.store.length ≤ i) :
    a.elems.getD i none = none := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [JSArr.elems_length hw]
    have := hw.length_le
    omega

theorem scan_eq {c : Cmp} {s : Val} {a : JSArr} (hw : a.WF) (hsl : a.SlackHoles)
    (hpos : 0 < a.length) (fromK : Int) (hk : 0 ≤ fromK) :
    scanStore (present c s) a.store (clampFrom fromK a.store.length) =
      .done (specScan c s a.elems fromK) := by
  have hl := hw.length_le
  have hcl : 0 ≤ clampFrom fromK a.store.length := by
    unfold clampFrom
    split <;> omega
  have hcle : (clampFrom fromK a.store.length).toNat < a.store.length := by
    unfold clampFrom
    split <;> omega
  have hcong := scanDown_congr (test := present c s) (g1 := fun i => a.store[i]?)
    (g2 := fun i => some (a.elems.getD i none)) (clampFrom fromK a.store.length).toNat
    (fun i hi => ⟨a.store[i], a.elems.getD i none,
      List.getElem?_eq_getElem (by omega), rfl, by rw [getD_elems hw hsl (by omega)]⟩)
  have hfin : ∃ r, scanDown (present c s) (fun i => some (a.elems.getD i none))
      (clampFrom fromK a.store.length).toNat = some r := by
    exact scanDown_some _ (fun i _ => ⟨_, rfl⟩)
  have hskip : scanDown (present c s) (fun i => some (a.elems.getD i none)) fromK.toNat =
      scanDown (present c s) (fun i => some (a.elems.getD i none))
        (clampFrom fromK a.store.length).toNat := by
    unfold clampFrom
    split
    · rename_i hge
      have := scanDown_skip (test := present c s) (g := fun i => some (a.elems.getD i none))
        (((a.store.length : Int) - 1).toNat) (fromK.toNat - ((a.store.length : Int) - 1).toNat)
        (fun i h1 _ => ⟨none, by rw [getD_elems_out hw (by omega)], rfl⟩)
      rw [show ((a.store.length : Int) - 1).toNat +
        (fromK.toNat - ((a.store.length : Int) - 1).toNat) = fromK.toNat by omega] at this
      exact this
    · rfl
  unfold scanStore specScan
  rw [ite_eq_right (by omega), ite_eq_right (by omega), hcong, hskip]
  obtain ⟨r, hr⟩ := hfin
  rw [hr]
  rfl

theorem spec_all_false {c : Cmp} {s : Val} {a : JSArr} (fromK : Int)
    (hf : ∀ x ∈ a.elems, present c s x = false) : specScan c s a.elems fromK = -1 := by
  unfold specScan
  split
  · rfl
  · rw [scanDown_none]
    · rfl
    · intro i _
      refine ⟨a.elems.getD i none, rfl, ?_⟩
      rw [List.getD_eq_getElem?_getD]
      cases h : a.elems[i]? with
      | none => rfl
      | some x => exact hf x (List.mem_of_getElem? h)

theorem double_false {c : Cmp} (hc : c.OK) {s : Val} {a : JSArr} (hw : a.WF)
    (hd : a.kind.isDouble = true) (hs : ¬(s.isNumber = true ∨ s = .undef)) :
    ∀ x ∈ a.elems, present c s x = false := by
  intro x hx
  cases x with
  | none => rfl
  | some e =>
    show c.seq s e = false
    cases hq : c.seq s e
    · rfl
    · have hok := hw.kind_ok (some e) hx
      cases hk : a.kind <;> rw [hk] at hd hok <;> simp [Kind.isDouble, kindOk] at hd hok
      · exact absurd (Or.inl (hc.number s e hq hok)) hs
      · rcases hok with hn | hu
        · exact absurd (Or.inl (hc.number s e hq hn)) hs
        · exact absurd (Or.inr (hc.undef s e hq hu)) hs

theorem nan_false {c : Cmp} (hc : c.OK) {s : Val} (hn : c.isNaN s = true) (x : Option Val) :
    present c s x = false := by
  cases x with
  | none => rfl
  | some e => exact hc.nan_ne s e hn

theorem fast_spec {c : Cmp} (hc : c.OK) {smiMax : Nat} {a : JSArr} {s : Val} {fromK : Int}
    {r : Int} (hw : a.WF) (hsl : a.SlackHoles)
    (h : fastLastIndexOf c smiMax a s (.fin fromK) = .done r) :
    r = specScan c s a.elems fromK := by
  have hlen := JSArr.elems_length hw
  unfold fastLastIndexOf at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · rename_i _ h0
    cases h
    have hz : a.elems = [] := by
      rw [← List.length_eq_zero_iff, hlen, h0]
    rw [hz]
    unfold specScan
    split
    · rfl
    · rw [scanDown_none]
      · rfl
      · intro i _
        exact ⟨none, rfl, rfl⟩
  rename_i _ h0
  split at h
  · cases h
  have hpos : 0 < a.length := by omega
  have hscan : ∀ r', scanStore (present c s) a.store (clampFrom fromK a.store.length) = .done r' →
      r' = specScan c s a.elems fromK := by
    intro r' hr'
    by_cases hk : 0 ≤ fromK
    · rw [scan_eq hw hsl hpos fromK hk] at hr'
      cases hr'
      rfl
    · have hcl : clampFrom fromK a.store.length < 0 := by
        unfold clampFrom
        split <;> omega
      unfold scanStore at hr'
      rw [ite_eq_left hcl] at hr'
      cases hr'
      unfold specScan
      rw [ite_eq_left (by omega)]
  split at h
  · rename_i hd
    split at h
    · rename_i hn
      cases h
      exact (spec_all_false fromK (fun x _ => nan_false hc hn.2 x)).symm
    · split at h
      · exact hscan r h
      · rename_i hs
        cases h
        exact (spec_all_false fromK (double_false hc hw hd hs)).symm
  · split at h
    · rename_i hn
      cases h
      exact (spec_all_false fromK (fun x _ => nan_false hc hn.2 x)).symm
    · exact hscan r h

theorem fromIndex_spec (len : Nat) (n : ExtInt) :
    fromIndex len (some n) = match specFrom len n with
      | none => .negInf
      | some k => .fin k := by
  cases n with
  | fin n =>
    simp only [fromIndex, specFrom]
    split <;> rfl
  | posInf => rfl
  | negInf => rfl

theorem lastIndexOf_spec {c : Cmp} (hc : c.OK) {smiMax len : Nat} {arg : Option ExtInt}
    {a : JSArr} {s : Val} {r : Int} (hw : a.WF) (hsl : a.SlackHoles)
    (h : lastIndexOf c smiMax len arg a s = .done r) :
    r = specLastIndexOf c s len arg a.elems := by
  unfold lastIndexOf at h
  unfold specLastIndexOf
  split at h
  · rename_i h0
    cases h
    rw [ite_eq_left h0]
  · rename_i h0
    rw [ite_eq_right h0]
    cases arg with
    | none => exact fast_spec hc hw hsl h
    | some n =>
      rw [fromIndex_spec] at h
      dsimp only
      split
      · rename_i hn
        rw [hn] at h
        cases h
      · rename_i k hk
        rw [hk] at h
        exact fast_spec hc hw hsl h

theorem scanStore_ne_fatal {test : Option Val → Bool} {store : List (Option Val)} {k : Int}
    (hk : k < store.length) : scanStore test store k ≠ .fatal := by
  unfold scanStore
  split
  · nofun
  · obtain ⟨r, hr⟩ := scanDown_some (test := test) (g := fun i => store[i]?) k.toNat
      (fun i hi => ⟨_, List.getElem?_eq_getElem (by omega)⟩)
    rw [hr]
    nofun

theorem lastIndexOf_ne_fatal {c : Cmp} {smiMax len : Nat} {arg : Option ExtInt} {a : JSArr}
    {s : Val} (hw : a.WF) : lastIndexOf c smiMax len arg a s ≠ .fatal := by
  have hl := hw.length_le
  have hcl : ∀ fromK : Int, 0 < a.length →
      clampFrom fromK a.store.length < a.store.length := by
    intro fromK hp
    unfold clampFrom
    split <;> omega
  unfold lastIndexOf
  split
  · nofun
  · unfold fastLastIndexOf
    split
    · rename_i fromK _
      split
      · nofun
      split
      · nofun
      rename_i _ h0
      split
      · nofun
      split
      · split
        · nofun
        · split
          · exact scanStore_ne_fatal (hcl fromK (by omega))
          · nofun
      · split
        · nofun
        · exact scanStore_ne_fatal (hcl fromK (by omega))
    · nofun

end ArrayLastIndexOf
