import ArraySort.Writeback

namespace ArraySort

open Torque

theorem gstep_len (b : Bool) (acc : List Val × Nat) (x : Option Val) :
    (gstep b acc x).1.length + (gstep b acc x).2 ≤ acc.1.length + acc.2 + 1 ∧
      ((b = true ∨ x ≠ none) → (gstep b acc x).1.length + (gstep b acc x).2 = acc.1.length + acc.2 + 1) := by
  cases x with
  | none =>
    cases b <;> simp [gstep] <;> omega
  | some v =>
    by_cases hv : v = .undef
    · simp [gstep, hv]
      omega
    · simp [gstep, hv]
      omega

def GOut (b : Bool) (l : List (Option Val)) (acc res : List Val × Nat) : Prop :=
  ∃ ws, res.1 = acc.1 ++ ws ∧ (∀ v ∈ ws, some v ∈ l ∧ v ≠ .undef) ∧
    res.1.length + res.2 ≤ acc.1.length + acc.2 + l.length ∧
    ((b = true ∨ none ∉ l) → res.1.length + res.2 = acc.1.length + acc.2 + l.length) ∧
    (acc.2 < res.2 → some .undef ∈ l ∨ (b = true ∧ none ∈ l))

theorem fold_gout (b : Bool) : ∀ (l : List (Option Val)) (acc : List Val × Nat),
    GOut b l acc (l.foldl (gstep b) acc)
  | [], acc => ⟨[], by simp, by simp, by simp, by simp, by simp⟩
  | x :: l, acc => by
    rw [List.foldl_cons]
    obtain ⟨ws, h1, h2, h3, h4, h5⟩ := fold_gout b l (gstep b acc x)
    generalize l.foldl (gstep b) (gstep b acc x) = res at h1 h3 h4 h5
    have hm : ∀ w ∈ ws, some w ∈ x :: l ∧ w ≠ .undef := fun w hw =>
      ⟨List.mem_cons_of_mem _ (h2 w hw).1, (h2 w hw).2⟩
    have hn : (b = true ∨ none ∉ x :: l) → (b = true ∨ none ∉ l) := by
      rintro (h | h)
      · exact Or.inl h
      · exact Or.inr fun hm => h (List.mem_cons_of_mem _ hm)
    cases x with
    | none =>
      cases b with
      | false =>
        simp only [gstep, Bool.false_eq_true, ite_false] at h1 h3 h4 h5
        refine ⟨ws, h1, hm, by simp only [List.length_cons]; omega, fun h => ?_, fun h => ?_⟩
        · rcases h with h | h
          · cases h
          · exact absurd List.mem_cons_self h
        · rcases h5 h with h5 | ⟨h5, _⟩
          · exact Or.inl (List.mem_cons_of_mem _ h5)
          · cases h5
      | true =>
        simp only [gstep, ite_true] at h1 h3 h4 h5
        refine ⟨ws, h1, hm, by simp only [List.length_cons]; omega, fun _ => ?_,
          fun _ => Or.inr ⟨rfl, List.mem_cons_self⟩⟩
        have := h4 (Or.inl trivial)
        simp only [List.length_cons]
        omega
    | some v =>
      by_cases hv : v = .undef
      · subst hv
        simp only [gstep, ite_true] at h1 h3 h4 h5
        refine ⟨ws, h1, hm, by simp only [List.length_cons]; omega, fun h => ?_,
          fun _ => Or.inl List.mem_cons_self⟩
        have := h4 (hn h)
        simp only [List.length_cons]
        omega
      · simp only [gstep, hv, ite_false] at h1 h3 h4 h5
        refine ⟨v :: ws, by rw [h1]; simp, fun w hw => ?_, ?_, fun h => ?_, fun h => ?_⟩
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact ⟨List.mem_cons_self, hv⟩
          · exact hm w hw
        · simp only [List.length_cons, List.length_append, List.length_nil] at h3 ⊢
          omega
        · have := h4 (hn h)
          simp only [List.length_cons, List.length_append, List.length_nil] at this ⊢
          omega
        · rcases h5 h with h5 | h5
          · exact Or.inl (List.mem_cons_of_mem _ h5)
          · exact Or.inr ⟨h5.1, List.mem_cons_of_mem _ h5.2⟩

theorem gatherGen_len {env : Env} {b : Bool} {len : Nat} :
    ∀ d i (e : Ext) (acc : List Val × Nat) vs u e', len - i = d →
      gatherGen env b len i e acc = some (vs, u, e') →
      vs.length + u ≤ acc.1.length + acc.2 + (len - i) ∧
        (b = true → vs.length + u = acc.1.length + acc.2 + (len - i))
  | 0, i, e, acc, vs, u, e', hd, h => by
    rw [gatherGen, dite_eq_right (by omega)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    omega
  | d + 1, i, e, acc, vs, u, e', hd, h => by
    rw [gatherGen, dite_eq_left (by omega)] at h
    split at h
    · next x r _ =>
      have := gatherGen_len d (i + 1) (e.step r) (gstep b acc x) vs u e' (by omega) h
      have hl := gstep_len b acc x
      constructor
      · omega
      · intro hb
        have := this.2 hb
        have := hl.2 (Or.inl hb)
        omega
    · cases h

theorem gather_len {env : Env} {b : Bool} {len : Nat} {e e' : Ext} {vs : List Val} {u : Nat}
    (hl : e.recv.arr.fast = true → len ≤ e.recv.arr.store.length)
    (h : gather env b len e = some (vs, u, e')) :
    vs.length + u ≤ len ∧ (b = true → vs.length + u = len) := by
  unfold gather at h
  split at h
  · next hf =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨ws, h1, -, h3, h4, -⟩ := fold_gout b (e.recv.arr.store.take len) ([], 0)
    have hlen : (e.recv.arr.store.take len).length = len := by
      simp only [List.length_take]
      exact Nat.min_eq_left (hl hf)
    simp only [List.length_nil, Nat.zero_add, hlen] at h3 h4
    exact ⟨h3, fun hb => h4 (Or.inl hb)⟩
  · have := gatherGen_len (len - 0) 0 e ([], 0) vs u e' rfl h
    simp only [List.length_nil, Nat.zero_add, Nat.sub_zero] at this
    exact this

theorem compactLoad_good {cfg : Cfg} {mp : Maps} {r1 : Recv} {env : Env} (henv : EnvOK cfg mp env)
    {b : Bool} {len : Nat} {e : Ext} {c : Core} (hr : Reach cfg mp r1 e)
    (hl : e.recv.arr.fast = true → len ≤ e.recv.arr.store.length)
    (hd : e.recv.arr.fast = true → e.recv.arr.kind.isDouble = true → e.recv.arr.store ≠ []) :
    ((compactLoad env b len ⟨c.work, c.work.length, 0⟩) e c).Good (fun r e' c' => c' = c ∧
      ∃ vs u, gather env b len e = some (vs, u, e') ∧ GInv r.1 vs ∧ r.2 = u ∧ Reach cfg mp r1 e' ∧
        e'.log = e.log) := by
  have hg0 : GInv ⟨c.work, c.work.length, 0⟩ [] := ⟨rfl, rfl, by simp [seg]⟩
  unfold compactLoad
  simp only [good_bind, good_getExt]
  have hfast : ∀ (hf : e.recv.arr.fast = true),
      ((compactFast b e.recv.arr.store len 0 ⟨c.work, c.work.length, 0⟩ 0) e c).Good
        (fun r e' c' => c' = c ∧ ∃ vs u, gather env b len e = some (vs, u, e') ∧ GInv r.1 vs ∧ r.2 = u ∧
          Reach cfg mp r1 e' ∧ e'.log = e.log) := by
    intro hf
    refine (compactFast_good (hl hf) (len - 0) 0 _ 0 rfl (Nat.zero_le _) hg0 (by simp) rfl).mono ?_
    rintro r e' c' ⟨h1, h2, h3, h4⟩
    subst e'
    subst c'
    refine ⟨rfl, _, _, ?_, h3, h4, hr, rfl⟩
    simp [gather, hf]
  rw [good_ite]
  split
  · next hf =>
    rw [good_ite]
    split
    · next hdb =>
      rw [good_bind, good_doIf, ite_eq_right (hd hf hdb)]
      exact hfast hf
    · exact hfast hf
  · next hf =>
    refine (compactGeneric_good (r1 := r1) (c := c) henv (len - 0) 0 _ e ([], 0) rfl hg0 (by simp) hr).mono ?_
    rintro r e' c' ⟨h1, h2, h3, vs, u, h4, h5, h6⟩
    refine ⟨h1, vs, u, ?_, h5, h6, h3, h2⟩
    simp only [gather, Bool.not_eq_true] at hf ⊢
    simp only [hf]
    exact h4

theorem compact_good {cfg : Cfg} {mp : Maps} {r1 : Recv} {env : Env} (henv : EnvOK cfg mp env)
    {b : Bool} {len : Nat} {e : Ext} {c : Core} (hr : Reach cfg mp r1 e)
    (hl : e.recv.arr.fast = true → len ≤ e.recv.arr.store.length)
    (hd : e.recv.arr.fast = true → e.recv.arr.kind.isDouble = true → e.recv.arr.store ≠ []) :
    ((compact env b len) e c).Good (fun r e' c' => ∃ vs u, gather env b len e = some (vs, u, e') ∧
      r = (vs.length, u) ∧ c'.size = c.size ∧ vs.length ≤ c'.work.length ∧
        seg c'.work 0 vs.length = vs.map some ∧ Reach cfg mp r1 e' ∧ e'.log = e.log) := by
  unfold compact
  simp only [good_bind, good_getCore]
  refine (compactLoad_good henv hr hl hd).mono ?_
  rintro r e' c' ⟨h1, vs, u, h2, ⟨g1, g2, g3⟩, h4, h5, h6⟩
  subst c'
  simp only [good_setCore, good_pure]
  refine ⟨vs, u, h2, by rw [← g2, ← h4], trivial, ?_, ?_, h5, h6⟩
  · have := congrArg List.length g3
    simp only [seg, Nat.sub_zero, List.drop_zero, List.length_take, List.length_map] at this
    omega
  · rw [← g2]
    exact g3

theorem checkAccessor_good {cfg : Cfg} {initMap initLen : Nat} {e : Ext} {c : Core}
    (h : initLen ≤ cfg.smiMax) :
    ((checkAccessor cfg initMap initLen) e c).Good (fun ok e' c' => e' = e ∧ c' = c ∧
      (ok = true → e.recv.arr.fast = true ∧ e.recv.map = initMap ∧ e.recv.arr.length = initLen)) := by
  unfold checkAccessor
  simp only [good_bind, good_getExt]
  rw [good_ite]
  split
  · rw [good_pure]
    exact ⟨rfl, rfl, fun h => by cases h⟩
  · next hf =>
    rw [good_ite]
    split
    · rw [good_pure]
      exact ⟨rfl, rfl, fun h => by cases h⟩
    · next hm =>
      rw [good_bind, good_dcheck]
      refine ⟨h, ?_⟩
      rw [good_pure]
      exact ⟨rfl, rfl, fun hd => ⟨by simpa using hf, by simpa using hm, by simpa using hd⟩⟩

theorem sortCompare_step {env : Env} {user : Bool} {e e' : Ext} {x y : Val} {o : Int}
    (h : sortCompare env user e x y = some (o, e')) :
    e' = e ∨ ∃ r, e' = e.step r ∧ ((∃ k, env.call e.tick e.recv x y = some (k, r)) ∨
      (∃ z, env.str e.tick e.recv x y = some (z, r))) := by
  unfold sortCompare at h
  cases user with
  | true =>
    simp only [ite_true] at h
    split at h
    · next r hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inr ⟨r, h.2.symm, Or.inl ⟨_, hc⟩⟩
    · next z r hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inr ⟨r, h.2.symm, Or.inl ⟨_, hc⟩⟩
    · cases h
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inl h.2.symm
    · split at h
      · next z r hc =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact Or.inr ⟨r, h.2.symm, Or.inr ⟨_, hc⟩⟩
      · cases h

theorem sortCompare_reach {cfg : Cfg} {mp : Maps} {r1 : Recv} {env : Env} (henv : EnvOK cfg mp env)
    {user : Bool} : ∀ e x y o e', Reach cfg mp r1 e → sortCompare env user e x y = some (o, e') →
      Reach cfg mp r1 e' := by
  intro e x y o e' hr h
  rcases sortCompare_step h with rfl | ⟨r, rfl, ⟨k, hk⟩ | ⟨z, hz⟩⟩
  · exact hr
  · exact reach_step hr (henv.1 _ _ _ _ _ _ hk hr.1)
  · exact reach_step hr (henv.2.1 _ _ _ _ _ _ hz hr.1)

theorem AccFacts.perm {cfg : Cfg} {acc : Acc} {r : Recv} {vs vs' : List Val} {nu sl : Nat}
    (hp : vs'.Perm vs) (h : AccFacts cfg acc r vs nu sl) : AccFacts cfg acc r vs' nu sl := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun v hv => h1 v (hp.mem_iff.1 hv), h2, ?_⟩
  rcases h3 with h3 | h3
  · exact Or.inl h3
  · exact Or.inr ⟨h3.1, h3.2.1, fun h => h3.2.2 (by rw [← hp.length_eq]; exact h)⟩

theorem good_and_ok {ε α : Type} {Q R : α → ε → Core → Prop} {r : Res ε α} (h1 : r.Good Q)
    (h2 : ∀ a e c, r = .ok a e c → R a e c) : r.Good (fun a e c => Q a e c ∧ R a e c) := by
  cases r with
  | ok a e c => exact ⟨h1, h2 a e c rfl⟩
  | throw e => trivial
  | ub => exact h1
  | abort => exact h1

theorem sortTail_good {cfg : Cfg} {env : Env} {user : Bool} {initMap initLen : Nat} {reset : Bool}
    {n nu sortLength : Nat} {vs : List Val} {I : Ext → Prop} {R : List Val → Prop} {e : Ext} {c : Core}
    (hI : ∀ e x y o e', I e → sortCompare env user e x y = some (o, e') → I e')
    (he : I e) (hsm : cfg.smiMax < 2 ^ 31) (hn : n ≤ cfg.smiMax) (hil : initLen ≤ cfg.smiMax)
    (hnl : n ≤ c.work.length) (hw : seg c.work 0 n = vs.map some) (hsz : c.size = 0)
    (hs : n + nu ≤ sortLength)
    (hacc : ∀ e', I e' → reset = false → e'.recv.arr.fast = true → e'.recv.map = initMap →
      e'.recv.arr.length = initLen → AccFacts cfg (selectAcc false e'.recv) e'.recv vs nu sortLength)
    (hR : ∀ a e' c', (sortCore (sortCompare env user) cfg.smiMax (n : Int)) e c = .ok a e' c' →
      R ((seg c'.work 0 n).filterMap id)) :
    ((sortTail cfg env user initMap initLen reset n nu sortLength) e c).Good (fun _ e' _ =>
      ∃ vs', vs'.Perm vs ∧ R vs' ∧ e'.log = e.log ++ writeLog vs' nu sortLength) := by
  have hJ : ∀ e1 x y o e2, (fun e' => I e' ∧ e'.log = e.log) e1 → sortCompare env user e1 x y = some (o, e2) →
      (fun e' => I e' ∧ e'.log = e.log) e2 := by
    rintro e1 x y o e2 ⟨h1, h2⟩ h
    refine ⟨hI e1 x y o e2 h1 h, ?_⟩
    rcases sortCompare_step h with rfl | ⟨r, rfl, -⟩
    · exact h2
    · exact h2
  have hv : Vals c.work 0 n := ⟨hnl, fun i _ hi => ⟨_, getD_seg_map hnl hw hi⟩⟩
  unfold sortTail
  rw [good_bind]
  have h1 := good_and_ok (good_inv (sortCore_good (sortCompare env user) cfg.smiMax hn hsm (e := e) hv hsz)
    ((pres_sortCore _ hJ cfg.smiMax (n : Int)).apply ⟨he, rfl⟩)) hR
  refine h1.mono ?_
  rintro _ e2 c2 ⟨⟨hp, hI2, hl2⟩, hR2⟩
  rw [good_bind]
  refine (checkAccessor_good hil).mono ?_
  rintro ok e3 c3 ⟨he3, hc3, hok⟩
  subst e3
  subst c3
  have hperm : (seg c2.work 0 n).Perm (vs.map some) := hw ▸ hp.perm
  have hall : ∀ x ∈ seg c2.work 0 n, x ≠ none := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 (hperm.mem_iff.1 hx)
    simp
  have hw2 : seg c2.work 0 n = ((seg c2.work 0 n).filterMap id).map some :=
    (map_some_filterMap_id _ hall).symm
  have hvp : ((seg c2.work 0 n).filterMap id).Perm vs := by
    have := hperm.filterMap id
    simpa using this
  refine (copyBack_good (by rw [hp.len]; exact hnl) hw2 hs ?_ ?_).mono ?_
  · intro hr
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hr
    exact (hok hr.2).1
  · cases hres : (reset || !ok) with
    | true => exact ⟨fun _ _ => trivial, fun _ => trivial, Or.inl rfl⟩
    | false =>
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hres
      obtain ⟨hf, hm, hlen⟩ := hok hres.2
      exact (hacc e2 hI2 hres.1 hf hm hlen).perm hvp
  · rintro _ e4 c4 ⟨-, hlog⟩
    exact ⟨_, hvp, hR2, by rw [hlog, hl2]⟩

end ArraySort
