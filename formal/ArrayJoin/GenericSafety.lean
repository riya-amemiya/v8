import ArrayJoin.Generic
import ArrayJoin.FastSafety

namespace ArrayJoin

open Torque

def LoaderOK (kind0 : Kind) : Loader → Prop
  | .fastDouble => kind0 = .packedDouble ∨ kind0 = .holeyDouble
  | _ => True

theorem cannotUseSame_false {σ : Type} {env : Env σ} {ld : Loader} {kind0 : Kind} {len : Nat}
    {w : σ} (hld : ld ≠ .generic) (h : cannotUseSame env ld kind0 len w = false) :
    (env.arr w).kind = kind0 ∧ (env.arr w).length = len := by
  cases ld with
  | generic => exact absurd rfl hld
  | fastObj =>
    simp only [cannotUseSame, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at h
    exact ⟨h.1.1, h.1.2⟩
  | fastDouble =>
    simp only [cannotUseSame, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at h
    exact ⟨h.1.1, h.1.2⟩

theorem loadFast_ok {ld : Loader} {a : JSArr} (hw : a.WF) {k : Nat} (hk : k < a.length)
    (hld : LoaderOK a.kind ld) : ∃ e, loadFast ld a k = .ok e := by
  have hks : k < a.store.length := Nat.lt_of_lt_of_le hk hw.length_le
  have hmem : a.store[k] ∈ a.elems := by
    rw [JSArr.elems, List.mem_iff_getElem]
    exact ⟨k, by simp; omega, by simp⟩
  have hok := hw.kind_ok _ hmem
  unfold loadFast
  rw [List.getElem?_eq_getElem hks]
  generalize a.store[k] = x at hok
  cases x with
  | none => exact ⟨_, rfl⟩
  | some v =>
    cases ld with
    | fastDouble =>
      have : v = .undef ∨ v.isNumber = true := by
        rcases hld with h | h <;> rw [h] at hok <;> simp [kindOk] at hok
        · exact Or.inr hok
        · rcases hok with h' | h'
          · exact Or.inr h'
          · exact Or.inl h'
      show ∃ e, (if v = .undef ∨ v.isNumber = true then Res.ok (Elem.val v) else Res.ub) = Res.ok e
      rw [ite_eq_left this]
      exact ⟨_, rfl⟩
    | fastObj => exact ⟨_, rfl⟩
    | generic => exact ⟨_, rfl⟩

theorem load_generic {σ : Type} (env : Env σ) (k : Nat) (w : σ) :
    load env .generic k w = .throws ∨ ∃ e w', load env .generic k w = .ok (e, w') := by
  unfold load
  cases hg : env.get k w with
  | none => exact Or.inl rfl
  | some p => exact Or.inr ⟨.val p.1, p.2, rfl⟩

theorem load_ok {σ : Type} {env : Env σ} (hwf : ∀ w, (env.arr w).WF) {ld : Loader} {kind0 : Kind}
    {len k : Nat} {w : σ} (hk : k < len) (hld : LoaderOK kind0 ld) :
    load env (if cannotUseSame env ld kind0 len w then .generic else ld) k w = .throws ∨
      ∃ e w', load env (if cannotUseSame env ld kind0 len w then .generic else ld) k w = .ok (e, w') := by
  by_cases hc : cannotUseSame env ld kind0 len w = true
  · rw [ite_eq_left hc]
    exact load_generic env k w
  · rw [ite_eq_right hc]
    have hc' : cannotUseSame env ld kind0 len w = false := by simpa using hc
    by_cases hg : ld = .generic
    · subst hg
      exact load_generic env k w
    · obtain ⟨hkind, hlen⟩ := cannotUseSame_false hg hc'
      obtain ⟨e, he⟩ := loadFast_ok (hwf w) (k := k) (by omega) (ld := ld) (by rw [hkind]; exact hld)
      right
      refine ⟨e, w, ?_⟩
      cases ld with
      | generic => exact absurd rfl hg
      | fastObj =>
        show (loadFast .fastObj (env.arr w) k).bind _ = _
        rw [he]
        rfl
      | fastDouble =>
        show (loadFast .fastDouble (env.arr w) k).bind _ = _
        rw [he]
        rfl

theorem loaderOK_step {σ : Type} {env : Env σ} {ld : Loader} {kind0 : Kind} {len : Nat} {w : σ}
    (hld : LoaderOK kind0 ld) :
    LoaderOK kind0 (if cannotUseSame env ld kind0 len w then .generic else ld) := by
  split
  · trivial
  · exact hld

theorem log_step {l : Limits} {sep : List Nat} {b : Buf} {C : List Nat} {nof k : Nat}
    {log : List (List Nat)} (hi : Inv l sep b C) (hJ : C ++ sepRun sep nof = joinPieces sep log)
    (hlog : log.length = k) (h0 : k = 0 → b.cur = [] ∧ nof = 0) (p : List Nat) :
    C ++ sepRun sep (if 0 < k then nof + 1 else nof) ++ p = joinPieces sep (log ++ [p]) := by
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨hc, hnof⟩ := h0 rfl
    subst hnof
    have := (hi.empty hc).1
    subst this
    rw [List.length_eq_zero_iff] at hlog
    subst hlog
    simp [joinPieces, sepRun]
  · rw [joinPieces_snoc _ (List.ne_nil_of_length_pos (by omega)), ← hJ, ite_eq_left (by omega),
      sepRun_succ]
    simp

theorem implLoop_spec {σ : Type} {l : Limits} (hl : l.OK) {env : Env σ}
    (hwf : ∀ w, (env.arr w).WF) {kind0 : Kind} {sep : Str} {len : Nat}
    (hS : sep.len * (len - 1) ≤ l.strMax) (k : Nat) (ld : Loader) (b : Buf) (nof : Nat) (w : σ)
    (log : List (List Nat)) (C : List Nat) (hk : k ≤ len) (hld : LoaderOK kind0 ld)
    (hi : Inv l sep.chars b C) (hJ : C ++ sepRun sep.chars nof = joinPieces sep.chars log)
    (hlog : log.length = k) (h0 : k = 0 → b.cur = [] ∧ nof = 0) (hn : k = 0 ∨ nof + 1 ≤ k) :
    implLoop l env kind0 sep len k ld b nof w log = .throws ∨
      ∃ b' nof' w' log' C', implLoop l env kind0 sep len k ld b nof w log = .ok (b', nof', w', log') ∧
        Inv l sep.chars b' C' ∧ C' ++ sepRun sep.chars nof' = joinPieces sep.chars log' ∧
        log'.length = len ∧ (len = 0 → b'.cur = [] ∧ nof' = 0) ∧ (len = 0 ∨ nof' + 1 ≤ len) := by
  rw [implLoop]
  by_cases hlt : k < len
  · rw [dite_eq_left hlt]
    have hnle : (if 0 < k then nof + 1 else nof) ≤ len - 1 := by
      split <;> omega
    have hsepn : sep.len * (if 0 < k then nof + 1 else nof) ≤ l.strMax :=
      Nat.le_trans (Nat.mul_le_mul_left _ hnle) hS
    have hld' := loaderOK_step (env := env) (len := len) (w := w) hld
    rcases load_ok hwf (w := w) hlt hld with h | ⟨e, w1, h⟩
    · rw [h]
      exact Or.inl rfl
    rw [h, Res.ok_bind]
    dsimp only
    have hskip : ∀ w2, implLoop l env kind0 sep len (k + 1)
        (if cannotUseSame env ld kind0 len w then .generic else ld) b
        (if 0 < k then nof + 1 else nof) w2 (log ++ [[]]) = .throws ∨
        ∃ b' nof' w' log' C', implLoop l env kind0 sep len (k + 1)
          (if cannotUseSame env ld kind0 len w then .generic else ld) b
          (if 0 < k then nof + 1 else nof) w2 (log ++ [[]]) = .ok (b', nof', w', log') ∧
          Inv l sep.chars b' C' ∧ C' ++ sepRun sep.chars nof' = joinPieces sep.chars log' ∧
          log'.length = len ∧ (len = 0 → b'.cur = [] ∧ nof' = 0) ∧ (len = 0 ∨ nof' + 1 ≤ len) := by
      intro w2
      have := log_step hi hJ hlog h0 []
      rw [List.append_nil] at this
      exact implLoop_spec hl hwf hS (k + 1) _ b _ w2 _ C (by omega) hld' hi this
        (by simp [hlog]) (fun h => absurd h (by omega)) (Or.inr (by split <;> omega))
    match hcv : env.conv e w1 with
    | none => exact Or.inl rfl
    | some (none, w2) => exact hskip w2
    | some (some s, w2) =>
      dsimp only
      by_cases hse : s.chars = []
      · rw [ite_eq_left hse]
        exact hskip w2
      · rw [ite_eq_right hse]
        rcases add_spec hl hi hse (n := if 0 < k then nof + 1 else nof)
          (fun hc => by
            by_cases hk0 : k = 0
            · exact absurd (h0 hk0).1 hc
            · rw [ite_eq_left (by omega)]
              omega) hsepn with h2 | ⟨b', h2, hi', _, _⟩
        · left
          have h' : add l b s (if 0 < k then nof + 1 else nof) sep.len = .throws := h2
          rw [h']
          rfl
        · have h' : add l b s (if 0 < k then nof + 1 else nof) sep.len = .ok b' := h2
          rw [h', Res.ok_bind]
          exact implLoop_spec hl hwf hS (k + 1) _ b' 0 w2 _ _ (by omega) hld' hi'
            (by rw [sepRun_zero, List.append_nil]; exact log_step hi hJ hlog h0 s.chars)
            (by simp [hlog]) (fun h => absurd h (by omega)) (Or.inr (by omega))
  · rw [dite_eq_right hlt]
    have hkc : k = len := by omega
    subst hkc
    exact Or.inr ⟨b, nof, w, log, C, rfl, hi, hJ, hlog, h0, hn⟩
termination_by len - k

theorem implJoin_spec {σ : Type} {l : Limits} (hl : l.OK) {env : Env σ}
    (hwf : ∀ w, (env.arr w).WF) {kind0 : Kind} {ld0 : Loader} {sep : Str} {len : Nat} (w : σ)
    (hld : LoaderOK kind0 ld0) (hS : sep.len * (len - 1) ≤ l.strMax) :
    implJoin l env kind0 ld0 sep len w = .throws ∨
      ∃ s w' log, implJoin l env kind0 ld0 sep len w = .ok (s, w', log) ∧
        s = joinPieces sep.chars log ∧ log.length = len := by
  unfold implJoin
  rcases implLoop_spec hl hwf hS 0 ld0 (newBuffer l len) 0 w [] [] (Nat.zero_le _) hld
    (inv_new hl sep.chars len) (by simp [joinPieces, sepRun]) rfl (fun _ => ⟨rfl, rfl⟩) (Or.inl rfl)
    with h | ⟨b', nof', w', log', C', h, hi, hJ, hlog, _, hn⟩
  · rw [h]
    exact Or.inl rfl
  · rw [h, Res.ok_bind]
    dsimp only
    have hnle : nof' ≤ len - 1 := by omega
    rcases complete hl hi (n := nof') (Nat.le_trans (Nat.mul_le_mul_left _ hnle) hS) with h2 | h2
    · left
      have : ((addSeparators l b' nof' sep.len true).bind fun b => bufferJoin b sep) = .throws := h2
      cases ha : addSeparators l b' nof' sep.len true with
      | ok b1 =>
        rw [ha, Res.ok_bind] at this
        rw [Res.ok_bind, this]
        rfl
      | throws => rfl
      | bailout => rw [ha] at this; cases this
      | ub => rw [ha] at this; cases this
      | fatal => rw [ha] at this; cases this
    · right
      refine ⟨C' ++ sepRun sep.chars nof', w', log', ?_, hJ, hlog⟩
      cases ha : addSeparators l b' nof' sep.len true with
      | ok b1 =>
        rw [ha, Res.ok_bind] at h2
        rw [Res.ok_bind, h2]
        rfl
      | throws => rw [ha] at h2; cases h2
      | bailout => rw [ha] at h2; cases h2
      | ub => rw [ha] at h2; cases h2
      | fatal => rw [ha] at h2; cases h2

theorem select_ok {a : JSArr} {isArray : Bool} {len : Nat} {protoOk protector dictEmpty : Bool}
    {ld : Loader} (h : select a isArray len protoOk protector dictEmpty = .loader ld) :
    LoaderOK a.kind ld := by
  unfold select at h
  split at h
  · cases hk : a.kind with
    | packedSmi => rw [hk] at h; injection h with h; subst h; trivial
    | holeySmi => rw [hk] at h; injection h with h; subst h; trivial
    | packedElem => rw [hk] at h; injection h with h; subst h; trivial
    | holeyElem => rw [hk] at h; injection h with h; subst h; trivial
    | packedDouble => rw [hk] at h; injection h with h; subst h; exact Or.inl rfl
    | holeyDouble => rw [hk] at h; injection h with h; subst h; exact Or.inr rfl
    | slow =>
      simp only [hk] at h
      split at h
      · cases h
      · injection h with h
        subst h
        trivial
  · injection h with h
    subst h
    trivial

theorem arrayJoin_spec {σ : Type} {l : Limits} (hl : l.OK) {env : Env σ}
    (hwf : ∀ w, (env.arr w).WF) (rc : Receiver σ) {sep : Str} {len : Nat} (w : σ)
    (hS : sep.len * (len - 1) ≤ l.strMax) :
    arrayJoin l env rc sep len w = .throws ∨
      ∃ s w' log, arrayJoin l env rc sep len w = .ok (s, w', log) ∧
        s = joinPieces sep.chars log ∧ log.length = len := by
  unfold arrayJoin
  split
  · rename_i hsel
    have hrep : joinPieces sep.chars (List.replicate len []) = sepRun sep.chars (len - 1) := by
      have := joinPieces_replicate sep.chars [] len
      simpa using this
    by_cases he : sep.chars = []
    · rw [ite_eq_left he]
      refine Or.inr ⟨_, _, _, rfl, ?_, by simp⟩
      rw [hrep, he]
      simp [sepRun]
    · rw [ite_eq_right he]
      by_cases hs : len - 1 ≤ l.smiMax
      · rw [ite_eq_left hs]
        exact Or.inr ⟨_, _, _, rfl, hrep.symm, by simp⟩
      · rw [ite_eq_right hs]
        exact Or.inl rfl
  · rename_i ld hsel
    exact implJoin_spec hl hwf w (select_ok hsel) hS

end ArrayJoin
