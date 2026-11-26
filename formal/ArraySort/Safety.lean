import ArraySort.ToSorted

namespace ArraySort

open Torque

def Result.Safe {ρ : Type} : Result ρ → Prop
  | .ub => False
  | .abort => False
  | _ => True

theorem toResult_good {ρ : Type} {r : Res Ext ρ} {Q : ρ → Ext → Core → Prop} (h : r.Good Q) :
    r.toResult.Safe ∧ ∀ a e, r.toResult = .done a e → ∃ c, Q a e c := by
  cases r with
  | ok a e c =>
    refine ⟨trivial, fun a' e' h' => ?_⟩
    simp only [Res.toResult, Result.done.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨c, h⟩
  | throw e =>
    refine ⟨trivial, fun _ _ h' => ?_⟩
    simp [Res.toResult] at h'
  | ub => simp [Res.Good] at h
  | abort => simp [Res.Good] at h

theorem ensureWritableRecv_fields (r : Recv) :
    (ensureWritableRecv r).map = r.map ∧ (ensureWritableRecv r).prot = r.prot ∧
      (ensureWritableRecv r).arr.fast = r.arr.fast ∧ (ensureWritableRecv r).arr.kind = r.arr.kind ∧
        (ensureWritableRecv r).arr.length = r.arr.length := by
  unfold ensureWritableRecv ensureWritable
  split <;> (try split) <;> simp

theorem ensureWritableRecv_cow {r : Recv} (h : r.arr.fast = true) : (ensureWritableRecv r).arr.cow = false := by
  unfold ensureWritableRecv ensureWritable
  simp only [h, ite_true]
  split <;> simp_all

theorem ensureWritableRecv_ok {cfg : Cfg} {mp : Maps} {r : Recv} (h : RecvOK cfg mp r) :
    RecvOK cfg mp (ensureWritableRecv r) := by
  unfold ensureWritableRecv
  split
  · unfold ensureWritable
    split
    · have hwf := h.wf
      have hel : ({ r.arr with cow := false, store := r.arr.store.take r.arr.length } : JSArr).elems =
          r.arr.elems := by
        simp [JSArr.elems, List.take_take]
      refine ⟨⟨?_, ?_, hwf.forRead_fast, hwf.fast_forRead, hwf.forCopy_fast, fun h => by cases h⟩, h.kind,
        h.fast, ?_⟩
      · simp only [List.length_take]
        exact Nat.le_min.2 ⟨Nat.le_refl _, hwf.length_le⟩
      · rw [hel]
        exact hwf.kind_ok
      · rw [hel]
        exact h.dbl
    · exact h
  · exact h

theorem smiKind_ok {k : Kind} (h : isSmiKind k = true) (v : Val) : kindOk k (some v) = v.isSmi := by
  cases k <;> simp_all [isSmiKind, kindOk]

theorem smiKind_undef {k : Kind} (h : isSmiKind k = true) : kindOk k (some .undef) = false := by
  cases k <;> simp_all [isSmiKind, kindOk, Val.isSmi]

theorem holey_of_none {k : Kind} (hf : k.isFast = true) (h : kindOk k none = true) : k.isHoley = true := by
  cases k <;> simp_all [Kind.isFast, kindOk, Kind.isHoley]

theorem selectAcc_fast {r : Recv} (hf : r.arr.fast = true) :
    selectAcc false r = if r.arr.kind.isDouble then .dbl else if isSmiKind r.arr.kind then .smi else .obj := by
  unfold selectAcc
  simp [hf]

theorem fast_facts {cfg : Cfg} {mp : Maps} {r : Recv} (hr : RecvOK cfg mp r) (hf : r.arr.fast = true) :
    (∀ v ∈ ((r.arr.store.take r.arr.length).foldl (gstep false) ([], 0)).1, ValOK cfg (selectAcc false r) v) ∧
      (0 < ((r.arr.store.take r.arr.length).foldl (gstep false) ([], 0)).2 →
        ValOK cfg (selectAcc false r) .undef) ∧
      (((r.arr.store.take r.arr.length).foldl (gstep false) ([], 0)).1.length +
        ((r.arr.store.take r.arr.length).foldl (gstep false) ([], 0)).2 < r.arr.length →
          r.arr.kind.isHoley = true) := by
  obtain ⟨ws, h1, h2, -, h4, h5⟩ := fold_gout false (r.arr.store.take r.arr.length) ([], 0)
  have hlen : (r.arr.store.take r.arr.length).length = r.arr.length := JSArr.elems_length hr.wf
  have hk : ∀ x ∈ r.arr.store.take r.arr.length, kindOk r.arr.kind x = true := hr.wf.kind_ok
  have hdb : r.arr.kind.isDouble = true → ∀ x ∈ r.arr.store.take r.arr.length,
      x = none ∨ (∃ k, x = some (.num k)) ∨ (x = some .undef ∧ cfg.ud = true) := hr.dbl
  have hfast : r.arr.kind.isFast = true := hr.wf.forRead_fast (hr.wf.fast_forRead hf)
  generalize (r.arr.store.take r.arr.length).foldl (gstep false) ([], 0) = res at h1 h4 h5 ⊢
  simp only [List.nil_append] at h1
  rw [selectAcc_fast hf]
  refine ⟨fun v hv => ?_, fun hu => ?_, fun hl => ?_⟩
  · rw [h1] at hv
    obtain ⟨hm, hne⟩ := h2 v hv
    split
    · next hd =>
      rcases hdb hd _ hm with h | ⟨k, h⟩ | ⟨h, _⟩
      · cases h
      · simp only [Option.some.injEq] at h
        exact Or.inl ⟨k, h⟩
      · simp only [Option.some.injEq] at h
        exact absurd h hne
    · split
      · next hs =>
        have := hk _ hm
        rw [smiKind_ok hs] at this
        exact this
      · trivial
  · rcases h5 hu with h | ⟨h, _⟩
    · split
      · next hd =>
        rcases hdb hd _ h with h' | ⟨k, h'⟩ | ⟨-, hu'⟩
        · cases h'
        · simp at h'
        · exact Or.inr ⟨rfl, hu'⟩
      · split
        · next hs =>
          have := hk _ h
          rw [smiKind_undef hs] at this
          cases this
        · trivial
    · cases h
  · by_cases hn : none ∈ r.arr.store.take r.arr.length
    · exact holey_of_none hfast (hk _ hn)
    · have := h4 (Or.inr hn)
      simp only [List.length_nil, Nat.zero_add, hlen] at this
      omega

theorem arraySort_core {cfg : Cfg} {mp : Maps} {env : Env} (henv : EnvOK cfg mp env)
    (hsm : cfg.smiMax < 2 ^ 31) {user : Bool} {r0 : Recv} {len : Nat} (hr0 : RecvOK cfg mp r0)
    (hlen : r0.arr.fast = true → len = r0.arr.length) (h2 : 2 ≤ len) (hl : len ≤ cfg.smiMax)
    (work : List (Option Val)) :
    ((do
      let cn ← compact env false len
      sortTail cfg env user r0.map len false cn.1 cn.2 len) ⟨ensureWritableRecv r0, 0, []⟩
      (Core.init work)).Good (fun _ (e : Ext) _ => ∃ vals u e1,
        gather env false len ⟨ensureWritableRecv r0, 0, []⟩ = some (vals, u, e1) ∧
        ∃ sorted : List Val, sorted.Perm vals ∧ e.log = writeLog sorted u len) := by
  obtain ⟨fm, fp, ff, fk, fl⟩ := ensureWritableRecv_fields r0
  have hr1 := ensureWritableRecv_ok hr0
  have hreach : Reach cfg mp (ensureWritableRecv r0) ⟨ensureWritableRecv r0, 0, []⟩ := ⟨hr1, id, id⟩
  have hl1 : (ensureWritableRecv r0).arr.fast = true → len ≤ (ensureWritableRecv r0).arr.store.length := by
    intro hf
    rw [hlen (ff ▸ hf), ← fl]
    exact hr1.wf.length_le
  refine good_bind_of (compact_good henv hreach hl1 fun hf _ h => by have := hl1 hf; rw [h] at this; simp at this; omega) ?_
  rintro cn e1 c1 ⟨vs, u, hg, hcn, hsz, hnl, hw, hr, hlog⟩
  subst hcn
  have hgl := gather_len hl1 hg
  refine (sortTail_good (vs := vs) (sortCompare_reach henv) hr hsm (by omega) hl hnl hw hsz hgl.1 ?_).mono ?_
  · intro e' hr' _ hf hm hle
    have hok := hr'.1
    have hfe := hok.fast
    rw [hf] at hfe
    have hmf : mp.fast e'.recv.map = true ∧ e'.recv.prot = true := by
      simpa using hfe.symm
    have hp1 := hr'.2.1 hmf.2
    have hf1 : (ensureWritableRecv r0).arr.fast = true := by
      rw [hr1.fast, hp1, fm, ← hm]
      simp [hmf.1]
    have hc1 : (ensureWritableRecv r0).arr.cow = false := ensureWritableRecv_cow (ff ▸ hf1)
    have hkind : e'.recv.arr.kind = (ensureWritableRecv r0).arr.kind := by
      rw [hok.kind, hr1.kind, hm, fm]
    have hlen1 : len = (ensureWritableRecv r0).arr.length := by rw [fl]; exact hlen (ff ▸ hf1)
    have hg' := hg
    simp only [gather, hf1, ite_true, Option.some.injEq, Prod.mk.injEq] at hg'
    obtain ⟨hvs, hu, -⟩ := hg'
    have facts := fast_facts hr1 hf1
    rw [← hlen1, hvs, hu] at facts
    have hacc : selectAcc false e'.recv = selectAcc false (ensureWritableRecv r0) := by
      rw [selectAcc_fast hf, selectAcc_fast hf1, hkind]
    rw [hacc]
    refine ⟨facts.1, facts.2.1, Or.inr ⟨?_, ?_, fun h => hkind ▸ facts.2.2 h⟩⟩
    · rw [← hle]
      exact hok.wf.length_le
    · cases hcw : e'.recv.arr.cow
      · rfl
      · have := hr'.2.2 hcw
        rw [hc1] at this
        cases this
  · rintro _ e' _ ⟨vs', hp, hl'⟩
    refine ⟨vs, u, e1, hg, vs', hp, ?_⟩
    rw [hl', hlog]
    rfl

theorem arraySort_safe {cfg : Cfg} {mp : Maps} {env : Env} (henv : EnvOK cfg mp env)
    (hsm : cfg.smiMax < 2 ^ 31) (arg : CmpArg) {r0 : Recv} {len : Nat} (hr0 : RecvOK cfg mp r0)
    (hlen : r0.arr.fast = true → len = r0.arr.length) :
    (arraySort cfg env arg r0 len).Safe := by
  unfold arraySort
  split
  · trivial
  split
  · trivial
  split
  · trivial
  exact (toResult_good (arraySort_core henv hsm hr0 hlen (by omega) (by omega) _)).1

theorem arraySort_perm {cfg : Cfg} {mp : Maps} {env : Env} (henv : EnvOK cfg mp env)
    (hsm : cfg.smiMax < 2 ^ 31) (arg : CmpArg) {r0 : Recv} {len : Nat} (hr0 : RecvOK cfg mp r0)
    (hlen : r0.arr.fast = true → len = r0.arr.length) (h2 : 2 ≤ len) {e : Ext}
    (hd : arraySort cfg env arg r0 len = .done () e) :
    ∃ vals u e1, gather env false len ⟨ensureWritableRecv r0, 0, []⟩ = some (vals, u, e1) ∧
      ∃ sorted : List Val, sorted.Perm vals ∧ e.log = writeLog sorted u len := by
  unfold arraySort at hd
  split at hd
  · cases hd
  split at hd
  · omega
  split at hd
  · cases hd
  obtain ⟨c, hc⟩ := (toResult_good (arraySort_core henv hsm hr0 hlen h2 (by omega) _)).2 () e hd
  exact hc

theorem arrayToSorted_core {cfg : Cfg} {mp : Maps} {env : Env} (henv : EnvOK cfg mp env)
    (hsm : cfg.smiMax < 2 ^ 31) {user : Bool} {r0 : Recv} {len : Nat} (hr0 : RecvOK cfg mp r0)
    (hlen : r0.arr.fast = true → len = r0.arr.length) (h2 : 2 ≤ len) (hl : len ≤ cfg.smiMax)
    (work : List (Option Val)) :
    ((do
      let cn ← compact env true len
      intoCopy cfg env user cn.1 cn.2 len) ⟨r0, 0, []⟩ (Core.init work)).Good (fun (a : JSArr) _ _ => ∃ vals u e1,
        gather env true len ⟨r0, 0, []⟩ = some (vals, u, e1) ∧
        ∃ sorted : List Val, sorted.Perm vals ∧ a.store = sorted.map some ++ List.replicate u (some Val.undef) ∧
          a.length = len) := by
  have hreach : Reach cfg mp r0 ⟨r0, 0, []⟩ := ⟨hr0, id, id⟩
  have hl1 : r0.arr.fast = true → len ≤ r0.arr.store.length := by
    intro hf
    rw [hlen hf]
    exact hr0.wf.length_le
  refine good_bind_of (compact_good henv hreach hl1 fun hf _ h => by have := hl1 hf; rw [h] at this; simp at this; omega) ?_
  rintro cn e1 c1 ⟨vs, u, hg, hcn, hsz, hnl, hw, hr, hlog⟩
  subst hcn
  have hgl := gather_len hl1 hg
  refine (intoCopy_good (user := user) (env := env) hsm (by omega) hnl hw hsz (hgl.2 rfl).symm).mono ?_
  rintro a _ _ ⟨vs', hp, hs, hal⟩
  exact ⟨vs, u, e1, hg, vs', hp, hs, hal⟩

theorem arrayToSorted_safe {cfg : Cfg} {mp : Maps} {env : Env} (henv : EnvOK cfg mp env)
    (hsm : cfg.smiMax < 2 ^ 31) (arg : CmpArg) {r0 : Recv} {len : Nat} (hr0 : RecvOK cfg mp r0)
    (hlen : r0.arr.fast = true → len = r0.arr.length) :
    (arrayToSorted cfg env arg r0 len).Safe := by
  unfold arrayToSorted
  split
  · trivial
  split
  · trivial
  split
  · split <;> trivial
  split
  · trivial
  exact (toResult_good (arrayToSorted_core henv hsm hr0 hlen (by omega) (by omega) _)).1

theorem arrayToSorted_perm {cfg : Cfg} {mp : Maps} {env : Env} (henv : EnvOK cfg mp env)
    (hsm : cfg.smiMax < 2 ^ 31) (arg : CmpArg) {r0 : Recv} {len : Nat} (hr0 : RecvOK cfg mp r0)
    (hlen : r0.arr.fast = true → len = r0.arr.length) (h2 : 2 ≤ len) {a : JSArr} {e : Ext}
    (hd : arrayToSorted cfg env arg r0 len = .done a e) :
    ∃ vals u e1, gather env true len ⟨r0, 0, []⟩ = some (vals, u, e1) ∧
      ∃ sorted : List Val, sorted.Perm vals ∧ a.store = sorted.map some ++ List.replicate u (some Val.undef) ∧
        a.length = len := by
  unfold arrayToSorted at hd
  split at hd
  · cases hd
  split at hd
  · omega
  split at hd
  · omega
  split at hd
  · cases hd
  obtain ⟨c, hc⟩ := (toResult_good (arrayToSorted_core henv hsm hr0 hlen h2 (by omega) _)).2 a e hd
  exact hc

theorem snapshot_vals {temp : List (Option Val)} {len : Nat} (hv : Vals temp 0 len) :
    seg temp 0 len = ((seg temp 0 len).filterMap id).map some := by
  refine (map_some_filterMap_id _ fun x hx => ?_).symm
  obtain ⟨i, _, hi2, hi⟩ := mem_seg.1 hx
  obtain ⟨v, hv'⟩ := hv.2 i (Nat.zero_le _) hi2
  rw [← getD_of_getElem? hi, hv']
  simp

theorem continueFromSnapshot_core {cfg : Cfg} {env : Env} {user : Bool} {e0 : Ext}
    {temp : List (Option Val)} {len : Nat} (hsm : cfg.smiMax < 2 ^ 31) (hl : len ≤ cfg.smiMax)
    (hv : Vals temp 0 len) :
    ((sortTail cfg env user e0.recv.map len true len 0 len) e0 (Core.init temp)).Good (fun _ e _ =>
      ∃ sorted : List Val, sorted.Perm ((seg temp 0 len).filterMap id) ∧
        e.log = e0.log ++ writeLog sorted 0 len) :=
  sortTail_good (I := fun _ => True) (fun _ _ _ _ _ _ _ => trivial) trivial hsm hl hl hv.1 (snapshot_vals hv) rfl
    (by omega) (fun _ _ h => by cases h)

theorem continueFromSnapshot_safe {cfg : Cfg} {env : Env} {user : Bool} {e0 : Ext}
    {temp : List (Option Val)} {len : Nat} (hsm : cfg.smiMax < 2 ^ 31) (hl : len ≤ cfg.smiMax)
    (hv : Vals temp 0 len) : (continueFromSnapshot cfg env user e0 temp len).Safe :=
  (toResult_good (continueFromSnapshot_core hsm hl hv)).1

theorem continueFromSnapshot_perm {cfg : Cfg} {env : Env} {user : Bool} {e0 : Ext}
    {temp : List (Option Val)} {len : Nat} (hsm : cfg.smiMax < 2 ^ 31) (hl : len ≤ cfg.smiMax)
    (hv : Vals temp 0 len) {e : Ext} (hd : continueFromSnapshot cfg env user e0 temp len = .done () e) :
    ∃ sorted : List Val, sorted.Perm ((seg temp 0 len).filterMap id) ∧
      e.log = e0.log ++ writeLog sorted 0 len := by
  obtain ⟨c, hc⟩ := (toResult_good (continueFromSnapshot_core (user := user) (env := env) (e0 := e0) hsm hl hv)).2 () e hd
  exact hc

theorem continueAfterCallback_safe {cfg : Cfg} {env : Env} {user : Bool} {r0 : Recv}
    {temp : List (Option Val)} {len : Nat} {result : Val} (hsm : cfg.smiMax < 2 ^ 31) (hl : len ≤ cfg.smiMax)
    (hv : Vals temp 0 len) : (continueAfterCallback cfg env user r0 temp len result).Safe := by
  unfold continueAfterCallback
  split
  · exact continueFromSnapshot_safe hsm hl hv
  · trivial

theorem continueAfterCallback_perm {cfg : Cfg} {env : Env} {user : Bool} {r0 : Recv}
    {temp : List (Option Val)} {len : Nat} {result : Val} (hsm : cfg.smiMax < 2 ^ 31) (hl : len ≤ cfg.smiMax)
    (hv : Vals temp 0 len) {e : Ext} (hd : continueAfterCallback cfg env user r0 temp len result = .done () e) :
    ∃ r1, env.toNum 0 r0 result = some r1 ∧ ∃ sorted : List Val,
      sorted.Perm ((seg temp 0 len).filterMap id) ∧ e.log = writeLog sorted 0 len := by
  unfold continueAfterCallback at hd
  split at hd
  · next r1 hr =>
    obtain ⟨sorted, hp, hlog⟩ := continueFromSnapshot_perm hsm hl hv hd
    exact ⟨r1, hr, sorted, hp, by rw [hlog]; rfl⟩
  · cases hd

end ArraySort
