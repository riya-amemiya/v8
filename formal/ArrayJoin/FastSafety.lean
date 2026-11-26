import ArrayJoin.Fast
import ArrayJoin.BufferSpec

namespace ArrayJoin

open Torque

theorem joinPieces_single (sep p : List Nat) : joinPieces sep [p] = p := by simp [joinPieces]

theorem joinPieces_snoc (sep : List Nat) {ps : List (List Nat)} (h : ps ≠ []) (p : List Nat) :
    joinPieces sep (ps ++ [p]) = joinPieces sep ps ++ sep ++ p := by
  cases ps with
  | nil => exact absurd rfl h
  | cons q qs => simp [joinPieces]

theorem sepRun_zero (sep : List Nat) : sepRun sep 0 = [] := rfl

theorem sepRun_add (sep : List Nat) (m : Nat) :
    ∀ n, sepRun sep (m + n) = sepRun sep m ++ sepRun sep n
  | 0 => by simp [sepRun]
  | n + 1 => by
    rw [← Nat.add_assoc, sepRun_succ, sepRun_succ, sepRun_add sep m n, List.append_assoc]

theorem joinPieces_replicate (sep : List Nat) (ps : List (List Nat)) (m : Nat) :
    joinPieces sep (ps ++ List.replicate m []) =
      if ps = [] then sepRun sep (m - 1) else joinPieces sep ps ++ sepRun sep m := by
  induction m with
  | zero =>
    cases ps with
    | nil => rfl
    | cons q qs => simp [sepRun]
  | succ m ih =>
    rw [List.replicate_succ', ← List.append_assoc]
    by_cases hp : ps = []
    · subst hp
      cases m with
      | zero => simp [joinPieces, sepRun]
      | succ m =>
        rw [joinPieces_snoc _ (by simp), ih]
        simp [sepRun_succ]
    · rw [joinPieces_snoc _ (by simp [hp]), ih, ite_eq_right hp, ite_eq_right hp, sepRun_succ]
      simp

theorem ofConv_str {o : Option (Option Str)} {s : Str} (h : ofConv o = .str s) : s.chars ≠ [] := by
  unfold ofConv at h
  split at h
  · cases h
  · cases h
  · split at h
    · cases h
    · cases h
      assumption

theorem fastNext_str {conv : Val → Option (Option Str)} {kind : Kind} {x : Option Val} {s : Str}
    (h : fastNext conv kind x = .str s) : s.chars ≠ [] := by
  unfold fastNext at h
  split at h <;> (repeat' split at h) <;> first
    | exact ofConv_str h
    | cases h

theorem ofConv_ne_bad (o : Option (Option Str)) : ofConv o ≠ .bad := by
  unfold ofConv
  split
  · simp
  · simp
  · split <;> simp

theorem fastNext_ne_bad (conv : Val → Option (Option Str)) {kind : Kind} {x : Option Val}
    (hf : kind.isFast = true) (hk : kindOk kind x = true) : fastNext conv kind x ≠ .bad := by
  intro h
  cases kind <;> cases x <;> simp only [fastNext] at h <;> (repeat' split at h) <;>
    simp_all [kindOk, Kind.isFast, ofConv_ne_bad]

theorem complete {l : Limits} (hl : l.OK) {sep : Str} {b : Buf} {C : List Nat}
    (hi : Inv l sep.chars b C) {n : Nat} (hsep : sep.len * n ≤ l.strMax) :
    ((addSeparators l b n sep.len true).bind fun b' => bufferJoin b' sep) = .throws ∨
      ((addSeparators l b n sep.len true).bind fun b' => bufferJoin b' sep) =
        .ok (C ++ sepRun sep.chars n) := by
  rcases finish_spec hl hi (n := n) hsep with h | ⟨b', h, hc, ht, hw⟩
  · left
    show (addSeparators l b n sep.chars.length true).bind _ = _
    rw [h]
    rfl
  · right
    show (addSeparators l b n sep.chars.length true).bind _ = _
    rw [h, Res.ok_bind]
    exact bufferJoin_spec hc ht hw

theorem fastLoop_spec {l : Limits} (hl : l.OK) {conv : Val → Option (Option Str)} {kind : Kind}
    {store : List (Option Val)} {sep : Str} {cur len : Nat} (hcs : cur ≤ store.length)
    (hcl : cur ≤ len) (hkind : ∀ x ∈ store.take cur, fastNext conv kind x ≠ .bad)
    (hS : sep.len * (len - 1) ≤ l.strMax) (k : Nat) (b : Buf) (nof : Nat) (C : List Nat)
    (hk : k ≤ cur) (hi : Inv l sep.chars b C)
    (hJ : C ++ sepRun sep.chars nof =
      joinPieces sep.chars (((store.take cur).map (fastPiece conv kind)).take k))
    (h0 : k = 0 → b.cur = [] ∧ nof = 0) (hn : k = 0 ∨ nof + 1 ≤ k) :
    fastLoop l conv kind store sep cur k b nof = .throws ∨
      fastLoop l conv kind store sep cur k b nof = .bailout ∨
      ∃ b' nof' C', fastLoop l conv kind store sep cur k b nof = .ok (b', nof') ∧
        Inv l sep.chars b' C' ∧
        C' ++ sepRun sep.chars nof' =
          joinPieces sep.chars ((store.take cur).map (fastPiece conv kind)) ∧
        (cur = 0 → b'.cur = [] ∧ nof' = 0) ∧ (cur = 0 ∨ nof' + 1 ≤ cur) := by
  have hplen : ((store.take cur).map (fastPiece conv kind)).length = cur := by
    simp [List.length_take]
    omega
  rw [fastLoop]
  by_cases hlt : k < cur
  · rw [dite_eq_left hlt]
    have hks : k < store.length := by omega
    rw [List.getElem?_eq_getElem hks]
    dsimp only
    have hmem : store[k] ∈ store.take cur := by
      rw [List.mem_iff_getElem]
      exact ⟨k, by simp; omega, by simp⟩
    have hx := hkind _ hmem
    have htake : ((store.take cur).map (fastPiece conv kind)).take (k + 1) =
        ((store.take cur).map (fastPiece conv kind)).take k ++ [fastPiece conv kind store[k]] := by
      rw [List.take_add_one]
      congr 1
      simp [hlt, List.getElem?_eq_getElem hks]
    have hnext : ∀ p, fastPiece conv kind store[k] = p →
        C ++ sepRun sep.chars (if 0 < k then nof + 1 else nof) ++ p =
          joinPieces sep.chars (((store.take cur).map (fastPiece conv kind)).take (k + 1)) := by
      intro p hp
      rw [htake, hp]
      by_cases hk0 : k = 0
      · subst hk0
        obtain ⟨hc, hnof⟩ := h0 rfl
        subst hnof
        have := (hi.empty hc).1
        subst this
        simp [joinPieces, sepRun]
      · rw [joinPieces_snoc _ (List.ne_nil_of_length_pos (by rw [List.length_take, hplen]; omega)), ← hJ, ite_eq_left (by omega), sepRun_succ]
        simp
    have hnle : (if 0 < k then nof + 1 else nof) ≤ len - 1 := by
      split <;> omega
    have hsepn : sep.len * (if 0 < k then nof + 1 else nof) ≤ l.strMax :=
      Nat.le_trans (Nat.mul_le_mul_left _ hnle) hS
    match hf : fastNext conv kind store[k] with
    | .skip =>
      have hp : fastPiece conv kind store[k] = [] := by simp [fastPiece, hf]
      have := hnext [] hp
      rw [List.append_nil] at this
      exact fastLoop_spec hl hcs hcl hkind hS (k + 1) b _ C (by omega) hi this
        (fun h => absurd h (by omega)) (Or.inr (by split <;> omega))
    | .bail => exact Or.inr (Or.inl rfl)
    | .bad => exact absurd hf hx
    | .str s =>
      have hp : fastPiece conv kind store[k] = s.chars := by simp [fastPiece, hf]
      have hs := fastNext_str hf
      dsimp only
      rcases add_spec hl hi hs (n := if 0 < k then nof + 1 else nof)
        (fun hc => by
          by_cases hk0 : k = 0
          · exact absurd (h0 hk0).1 hc
          · rw [ite_eq_left (by omega)]
            omega) hsepn with h | ⟨b', h, hi', _, hne⟩
      · left
        have h' : add l b s (if 0 < k then nof + 1 else nof) sep.len = .throws := h
        rw [h']
        rfl
      · have h' : add l b s (if 0 < k then nof + 1 else nof) sep.len = .ok b' := h
        rw [h', Res.ok_bind]
        exact fastLoop_spec hl hcs hcl hkind hS (k + 1) b' 0 _ (by omega) hi'
          (by rw [sepRun_zero, List.append_nil]; exact hnext _ hp)
          (fun h => absurd h (by omega)) (Or.inr (by omega))
  · rw [dite_eq_right hlt]
    have hkc : k = cur := by omega
    subst hkc
    rw [List.take_of_length_le (by omega)] at hJ
    refine Or.inr (Or.inr ⟨b, nof, C, rfl, hi, hJ, fun h => h0 h, ?_⟩)
    rcases hn with h | h
    · exact Or.inl h
    · exact Or.inr h
termination_by cur - k

theorem fastArrayJoin_spec {l : Limits} (hl : l.OK) (conv : Val → Option (Option Str)) {a : JSArr}
    (hw : a.WF) (hf : a.kind.isFast = true) (sep : Str) {len : Nat} (hlen : len ≤ l.strMax) :
    fastArrayJoin l conv a sep len = .throws ∨ fastArrayJoin l conv a sep len = .bailout ∨
      fastArrayJoin l conv a sep len = .ok (fastSpec conv a sep.chars len) := by
  unfold fastArrayJoin
  by_cases hov : 1 < sep.len ∧ 1 < len ∧ l.strMax < (len - 1) * sep.len
  · rw [ite_eq_left hov]
    exact Or.inl rfl
  rw [ite_eq_right hov]
  have hS : sep.len * (len - 1) ≤ l.strMax := by
    by_cases h1 : 1 < sep.len ∧ 1 < len
    · have : ¬ l.strMax < (len - 1) * sep.len := fun h => hov ⟨h1.1, h1.2, h⟩
      rw [Nat.mul_comm]
      omega
    · by_cases h2 : 1 < len
      · have h3 : sep.len ≤ 1 := by omega
        have := Nat.mul_le_mul_right (len - 1) h3
        omega
      · have : len - 1 = 0 := by omega
        rw [this, Nat.mul_zero]
        exact Nat.zero_le _
  have hcs : min len a.length ≤ a.store.length := Nat.le_trans (Nat.min_le_right _ _) hw.length_le
  have hkind : ∀ x ∈ a.store.take (min len a.length), fastNext conv a.kind x ≠ .bad := by
    intro x hx
    apply fastNext_ne_bad conv hf
    apply hw.kind_ok
    rw [← List.take_take] at hx
    exact List.mem_of_mem_take hx
  rcases fastLoop_spec hl (conv := conv) hcs (Nat.min_le_left _ _) hkind hS 0 (newBuffer l len) 0 []
    (Nat.zero_le _) (inv_new hl sep.chars len) (by simp [joinPieces, sepRun])
    (fun _ => ⟨rfl, rfl⟩) (Or.inl rfl) with h | h | ⟨b', nof', C', h, hi, hJ, h0, hn⟩
  · rw [h]
    exact Or.inl rfl
  · rw [h]
    exact Or.inr (Or.inl rfl)
  · rw [h, Res.ok_bind]
    dsimp only
    have hfin : finalSeps (min len a.length) (len - a.length) nof' ≤ len - 1 := by
      unfold finalSeps
      split
      · split <;> omega
      · omega
    rcases complete hl hi (n := finalSeps (min len a.length) (len - a.length) nof')
      (Nat.le_trans (Nat.mul_le_mul_left _ hfin) hS) with h2 | h2
    · exact Or.inl h2
    · refine Or.inr (Or.inr ?_)
      rw [h2, fastSpec, joinPieces_replicate]
      congr 1
      by_cases hz : min len a.length = 0
      · have hnil : (a.store.take (min len a.length)).map (fastPiece conv a.kind) = [] := by
          rw [hz]
          rfl
        rw [ite_eq_left hnil]
        obtain ⟨hc, hnof⟩ := h0 hz
        subst hnof
        have := (hi.empty hc).1
        subst this
        unfold finalSeps
        rw [hz]
        by_cases hex : 0 < len - a.length
        · rw [ite_eq_left hex, ite_eq_right (by omega)]
          simp
        · rw [ite_eq_right hex]
          have : len - a.length = 0 := by omega
          rw [this]
          rfl
      · have hne : (a.store.take (min len a.length)).map (fastPiece conv a.kind) ≠ [] :=
          List.ne_nil_of_length_pos (by rw [List.length_map, List.length_take]; omega)
        rw [ite_eq_right hne, ← hJ]
        unfold finalSeps
        by_cases hex : 0 < len - a.length
        · rw [ite_eq_left hex, ite_eq_left (by omega), List.append_assoc, ← sepRun_add]
          congr 2
          omega
        · rw [ite_eq_right hex]
          have : len - a.length = 0 := by omega
          rw [this]
          simp [sepRun]

end ArrayJoin
