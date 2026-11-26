import ArraySort.SortImpl

namespace ArraySort

open Torque

theorem msort_map_some (le : Val → Val → Bool) (vs : List Val) :
    msort le (vs.map some) = (vs.mergeSort le).map some := by
  unfold msort
  exact (List.map_mergeSort (r := le) (s := oleq le) (f := some) (l := vs) fun _ _ _ _ => rfl).symm

theorem filterMap_msort (le : Val → Val → Bool) (vs : List Val) :
    (msort le (vs.map some)).filterMap id = vs.mergeSort le := by
  rw [msort_map_some]
  simp

theorem cmpOK_user {le : Val → Val → Bool} {env : Env}
    (h : ∀ t r x y k r', env.call t r x y = some (k, r') →
      ((match k with
        | .nan => False
        | .fin z => z < 0) ↔ le y x = false)) :
    CmpOK le (sortCompare env true) := by
  intro e x y o e' hc
  simp only [sortCompare, ite_true] at hc
  split at hc
  · next r hk =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    rw [← hc.1]
    have := h _ _ _ _ _ _ hk
    simpa using this
  · next z r hk =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    rw [← hc.1]
    exact h _ _ _ _ _ _ hk
  · cases hc

theorem cmpOK_default {le : Val → Val → Bool} {env : Env}
    (hs : ∀ a b, smiLexCompare a b < 0 ↔ le (.smi b) (.smi a) = false)
    (h : ∀ t r x y z r', env.str t r x y = some (z, r') → (z < 0 ↔ le y x = false)) :
    CmpOK le (sortCompare env false) := by
  intro e x y o e' hc
  simp only [sortCompare, Bool.false_eq_true, ite_false] at hc
  split at hc
  · next a b =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    rw [← hc.1]
    exact hs a b
  · split at hc
    · next z r hk =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rw [← hc.1]
      exact h _ _ _ _ _ _ hk
    · cases hc

section

variable {ε : Type} {le : Val → Val → Bool}

theorem sortCore_sorted (hle : TotalPreorder le) {cmp : Cmp ε} (hc : CmpOK le cmp) (smiMax : Nat) {n : Nat}
    (hn : n ≤ smiMax) (hsm : smiMax < 2 ^ 31) {e : ε} {c : Core} (hv : Vals c.work 0 n) (hsz : c.size = 0) :
    ((sortCore cmp smiMax (n : Int)) e c).Good (fun _ _ c' =>
      PermOn c.work c'.work 0 n ∧ seg c'.work 0 n = msort le (seg c.work 0 n)) :=
  good_post (sortCore_good cmp smiMax hn hsm hv hsz) (sortCore_post cmp smiMax hle hc hv hsz)

theorem sortCore_result (hle : TotalPreorder le) {cmp : Cmp ε} (hc : CmpOK le cmp) (smiMax : Nat) {e : ε}
    {c : Core} {vs : List Val} {a : Unit} {e' : ε} {c' : Core} (hnl : vs.length ≤ c.work.length)
    (hw : seg c.work 0 vs.length = vs.map some) (hsz : c.size = 0)
    (h : (sortCore cmp smiMax (vs.length : Int)) e c = .ok a e' c') :
    (seg c'.work 0 vs.length).filterMap id = vs.mergeSort le := by
  have hv : Vals c.work 0 vs.length := ⟨hnl, fun i _ hi => ⟨_, getD_seg_map hnl hw hi⟩⟩
  have hp := sortCore_post cmp smiMax hle hc (e := e) hv hsz
  rw [h] at hp
  have hp' : seg c'.work 0 vs.length = msort le (seg c.work 0 vs.length) := hp
  rw [hp', hw, filterMap_msort]

end

theorem arraySort_sorted {cfg : Cfg} {mp : Maps} {env : Env} (henv : EnvOK cfg mp env)
    (hsm : cfg.smiMax < 2 ^ 31) (arg : CmpArg) {r0 : Recv} {len : Nat} (hr0 : RecvOK cfg mp r0)
    (hlen : r0.arr.fast = true → len = r0.arr.length) (h2 : 2 ≤ len) {le : Val → Val → Bool}
    (hle : TotalPreorder le) (hc : CmpOK le (sortCompare env (decide (arg = CmpArg.fn)))) {e : Ext}
    (hd : arraySort cfg env arg r0 len = .done () e) :
    ∃ vals u e1, gather env false len ⟨ensureWritableRecv r0, 0, []⟩ = some (vals, u, e1) ∧
      e.log = writeLog (vals.mergeSort le) u len := by
  unfold arraySort at hd
  split at hd
  · cases hd
  split at hd
  · omega
  split at hd
  · cases hd
  obtain ⟨c, vals, u, e1, hg, sorted, -, hs, hl⟩ := (toResult_good (arraySort_core henv hsm hr0 hlen h2
    (by omega) _ (R := fun vs s => s = vs.mergeSort le)
    fun _ _ _ _ _ _ hnl hw hsz h => sortCore_result hle hc cfg.smiMax hnl hw hsz h)).2 () e hd
  exact ⟨vals, u, e1, hg, by rw [hl, hs]⟩

theorem arrayToSorted_sorted {cfg : Cfg} {mp : Maps} {env : Env} (henv : EnvOK cfg mp env)
    (hsm : cfg.smiMax < 2 ^ 31) (arg : CmpArg) {r0 : Recv} {len : Nat} (hr0 : RecvOK cfg mp r0)
    (hlen : r0.arr.fast = true → len = r0.arr.length) (h2 : 2 ≤ len) {le : Val → Val → Bool}
    (hle : TotalPreorder le) (hc : CmpOK le (sortCompare env (decide (arg = CmpArg.fn)))) {a : JSArr} {e : Ext}
    (hd : arrayToSorted cfg env arg r0 len = .done a e) :
    ∃ vals u e1, gather env true len ⟨r0, 0, []⟩ = some (vals, u, e1) ∧
      a.store = (vals.mergeSort le).map some ++ List.replicate u (some Val.undef) ∧ a.length = len := by
  unfold arrayToSorted at hd
  split at hd
  · cases hd
  split at hd
  · omega
  split at hd
  · omega
  split at hd
  · cases hd
  obtain ⟨c, vals, u, e1, hg, sorted, -, hs, hst, hal⟩ := (toResult_good (arrayToSorted_core henv hsm hr0 hlen h2
    (by omega) _ (R := fun vs s => s = vs.mergeSort le)
    fun _ _ _ _ _ _ hnl hw hsz h => sortCore_result hle hc cfg.smiMax hnl hw hsz h)).2 a e hd
  exact ⟨vals, u, e1, hg, by rw [hst, hs], hal⟩

theorem continueFromSnapshot_sorted {cfg : Cfg} {env : Env} {user : Bool} {e0 : Ext}
    {temp : List (Option Val)} {len : Nat} (hsm : cfg.smiMax < 2 ^ 31) (hl : len ≤ cfg.smiMax)
    (hv : Vals temp 0 len) {le : Val → Val → Bool} (hle : TotalPreorder le) (hc : CmpOK le (sortCompare env user))
    {e : Ext} (hd : continueFromSnapshot cfg env user e0 temp len = .done () e) :
    e.log = e0.log ++ writeLog (((seg temp 0 len).filterMap id).mergeSort le) 0 len := by
  have hw := snapshot_vals hv
  have hlen : ((seg temp 0 len).filterMap id).length = len := by
    have := congrArg List.length hw
    rw [List.length_map, length_seg hv.1] at this
    omega
  obtain ⟨c, sorted, -, hs, hl'⟩ := (toResult_good (continueFromSnapshot_core (user := user) (env := env) (e0 := e0)
    hsm hl hv (R := fun s => s = ((seg temp 0 len).filterMap id).mergeSort le) fun a e' c' h => by
      have := sortCore_result hle hc cfg.smiMax (vs := (seg temp 0 len).filterMap id) (c := Core.init temp)
        (by rw [hlen]; exact hv.1) (by rw [hlen]; exact hw) rfl (by rw [hlen]; exact h)
      rw [hlen] at this
      exact this)).2 () e hd
  rw [hl', hs]

end ArraySort
