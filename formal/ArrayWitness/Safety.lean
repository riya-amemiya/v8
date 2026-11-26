import ArrayWitness.Model

namespace ArrayWitness

open Torque

def Inv {α : Type} (K : Kind) (s : St α) : Prop := s.arr.WF ∧ (s.ok = true → s.arr.kind = K)

theorem inv_start {α : Type} {a : JSArr} (hw : a.WF) (acc : α) : Inv a.kind ⟨acc, a, true⟩ :=
  ⟨hw, fun _ => rfl⟩

theorem inv_same {α : Type} {K : Kind} {a : JSArr} (hw : a.WF) (hk : a.kind = K) (acc : α) :
    Inv K ⟨acc, a, true⟩ :=
  ⟨hw, fun _ => hk⟩

theorem inv_post {ι ρ α : Type} {K : Kind} {cb : Nat → ι → JSArr → Post ρ} (hcb : CallbackOk K cb)
    (k : Nat) (x : ι) (a : JSArr) (acc : α) : Inv K ⟨acc, (cb k x a).arr, (cb k x a).recheck⟩ := by
  refine ⟨(hcb k x a).1, fun h => (hcb k x a).2 ?_⟩
  simp only [Post.recheck, Bool.and_eq_true] at h
  exact h.1

theorem load_ok {K : Kind} {a : JSArr} {k : Nat} (hw : a.WF) (hk : a.kind = K)
    (hl : k < a.length) : load K.isDouble a k = some (get a k) := by
  have hs : k < a.store.length := Nat.lt_of_lt_of_le hl hw.length_le
  unfold load get JSArr.elems
  rw [ite_eq_left (by rw [hk]), List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hl,
    List.getElem?_eq_getElem hs]
  rfl

theorem get_mem {a : JSArr} {k : Nat} {v : Val} (h : get a k = some v) : some v ∈ a.elems := by
  unfold get at h
  rw [List.getD_eq_getElem?_getD] at h
  cases hx : a.elems[k]? with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h
    have hx' : x = some v := h
    subst hx'
    exact List.mem_iff_getElem?.mpr ⟨k, hx⟩

theorem get_kindOk {a : JSArr} {k : Nat} {v : Val} (hw : a.WF) (h : get a k = some v) :
    kindOk a.kind (some v) = true :=
  hw.kind_ok _ (get_mem h)

def StepOk {α β ρ σ : Type} (K : Kind) (R : α → β → Prop) (Q : ρ → σ → Prop) :
    Body α ρ → SBody β σ → Prop
  | .next s, .next b a => R s.acc b ∧ s.arr = a ∧ Inv K s
  | .stop r, .stop r' => Q r r'
  | _, _ => False

def FinOk {α ρ σ : Type} (Q : ρ → σ → Prop) : Res α ρ → σ → Prop
  | .done r, r' => Q r r'
  | _, _ => False

structure Sim {α β ρ σ : Type} (K : Kind) (body : BodyFn α ρ) (sbody : SBodyFn β σ)
    (fin : FinFn α ρ) (sfin : SFinFn β σ) (R : List Nat → α → β → Prop) (Q : ρ → σ → Prop) :
    Prop where
  step : ∀ k ks acc b a, R (k :: ks) acc b → a.WF → a.kind = K → k < a.length →
    StepOk K (R ks) Q (body acc k (get a k) a) (sbody b k (get a k) a)
  fin : ∀ s b, R [] s.acc b → FinOk Q (fin s) (sfin b s.arr)

def LoopOk {α β ρ σ : Type} (K : Kind) (sbody : SBodyFn β σ) (sfin : SFinFn β σ)
    (R : List Nat → α → β → Prop) (Q : ρ → σ → Prop) (ks : List Nat) (b : β) (a : JSArr) :
    Res α ρ → Prop
  | .done r => Q r (spec sbody sfin ks b a)
  | .bailout ks' s =>
    ∃ b', Reaches sbody ks b a ks' b' s.arr ∧ R ks' s.acc b' ∧ Inv K s ∧ ks' <:+ ks
  | .fatal => False
  | .ub => False

section Generic

variable {α β ρ σ : Type} {K : Kind} {body : BodyFn α ρ} {sbody : SBodyFn β σ}
  {fin : FinFn α ρ} {sfin : SFinFn β σ} {R : List Nat → α → β → Prop} {Q : ρ → σ → Prop}

theorem loopOk_cons {k : Nat} {ks : List Nat} {b b' : β} {a a' : JSArr}
    (hsb : sbody b k (get a k) a = .next b' a') :
    ∀ r : Res α ρ, LoopOk K sbody sfin R Q ks b' a' r → LoopOk K sbody sfin R Q (k :: ks) b a r
  | .done r, h => by
    simp only [LoopOk, spec, hsb] at h ⊢
    exact h
  | .bailout ks' s, h => by
    obtain ⟨b'', hr, hR, hI, hsuf⟩ := h
    exact ⟨b'', .step hsb hr, hR, hI, hsuf.trans (List.suffix_cons k ks)⟩
  | .fatal, h => h.elim
  | .ub, h => h.elim

theorem loop_ok (hs : Sim K body sbody fin sfin R Q) :
    ∀ (ks : List Nat) (s : St α) (b : β), Inv K s → R ks s.acc b →
      LoopOk K sbody sfin R Q ks b s.arr (loop K.isDouble body fin ks s)
  | [], s, b, _, hr => by
    have hf := hs.fin s b hr
    simp only [loop]
    cases h : fin s with
    | done r =>
      rw [h] at hf
      exact hf
    | bailout _ _ =>
      rw [h] at hf
      exact hf.elim
    | fatal =>
      rw [h] at hf
      exact hf.elim
    | ub =>
      rw [h] at hf
      exact hf.elim
  | k :: ks, s, b, hi, hr => by
    simp only [loop]
    by_cases hok : s.ok = false
    · rw [ite_eq_left hok]
      exact ⟨b, .refl _ _ _, hr, hi, List.suffix_refl _⟩
    rw [ite_eq_right hok]
    by_cases hlen : s.arr.length ≤ k
    · rw [ite_eq_left hlen]
      exact ⟨b, .refl _ _ _, hr, hi, List.suffix_refl _⟩
    rw [ite_eq_right hlen]
    have hk : s.arr.kind = K := hi.2 (by simpa using hok)
    rw [load_ok hi.1 hk (by omega)]
    have hst := hs.step k ks s.acc b s.arr hr hi.1 hk (by omega)
    simp only []
    cases hb : body s.acc k (get s.arr k) s.arr with
    | next s' =>
      cases hsb : sbody b k (get s.arr k) s.arr with
      | next b' a' =>
        rw [hb, hsb] at hst
        obtain ⟨hR, ha, hI⟩ := hst
        have ih := loop_ok hs ks s' b' hI hR
        rw [ha] at ih
        exact loopOk_cons hsb _ ih
      | stop r' =>
        rw [hb, hsb] at hst
        exact hst.elim
    | stop r =>
      cases hsb : sbody b k (get s.arr k) s.arr with
      | next b' a' =>
        rw [hb, hsb] at hst
        exact hst.elim
      | stop r' =>
        rw [hb, hsb] at hst
        simp only [LoopOk, spec, hsb]
        exact hst
    | fatal =>
      rw [hb] at hst
      cases hsb : sbody b k (get s.arr k) s.arr <;> rw [hsb] at hst <;> exact hst.elim
    | ub =>
      rw [hb] at hst
      cases hsb : sbody b k (get s.arr k) s.arr <;> rw [hsb] at hst <;> exact hst.elim

theorem loop_ne_fatal (hs : Sim K body sbody fin sfin R Q) {ks : List Nat} {s : St α} {b : β}
    (hi : Inv K s) (hr : R ks s.acc b) : loop K.isDouble body fin ks s ≠ .fatal := by
  intro h
  have := loop_ok hs ks s b hi hr
  rw [h] at this
  exact this

theorem loop_ne_ub (hs : Sim K body sbody fin sfin R Q) {ks : List Nat} {s : St α} {b : β}
    (hi : Inv K s) (hr : R ks s.acc b) : loop K.isDouble body fin ks s ≠ .ub := by
  intro h
  have := loop_ok hs ks s b hi hr
  rw [h] at this
  exact this

theorem loop_done (hs : Sim K body sbody fin sfin R Q) {ks : List Nat} {s : St α} {b : β}
    (hi : Inv K s) (hr : R ks s.acc b) {r : ρ} (h : loop K.isDouble body fin ks s = .done r) :
    Q r (spec sbody sfin ks b s.arr) := by
  have := loop_ok hs ks s b hi hr
  rw [h] at this
  exact this

theorem loop_bailout (hs : Sim K body sbody fin sfin R Q) {ks : List Nat} {s : St α} {b : β}
    (hi : Inv K s) (hr : R ks s.acc b) {ks' : List Nat} {s' : St α}
    (h : loop K.isDouble body fin ks s = .bailout ks' s') :
    ∃ b', Reaches sbody ks b s.arr ks' b' s'.arr ∧ R ks' s'.acc b' ∧ Inv K s' ∧ ks' <:+ ks := by
  have := loop_ok hs ks s b hi hr
  rw [h] at this
  exact this

theorem Reaches.spec_eq {ks ks' : List Nat} {b b' : β} {a a' : JSArr}
    (h : Reaches sbody ks b a ks' b' a') : spec sbody sfin ks b a = spec sbody sfin ks' b' a' := by
  induction h with
  | refl => rfl
  | step hsb _ ih =>
    simp only [spec, hsb]
    exact ih

end Generic

theorem suffix_range' : ∀ (n s : Nat) (ks : List Nat), ks <:+ List.range' s n →
    ∃ k, s ≤ k ∧ k ≤ s + n ∧ ks = List.range' k (s + n - k)
  | 0, s, ks, h => by
    simp only [List.range'] at h
    rw [List.suffix_nil] at h
    exact ⟨s, Nat.le_refl s, by omega, by simp [h]⟩
  | n + 1, s, ks, h => by
    rw [List.range'_succ, List.suffix_cons_iff] at h
    rcases h with h | h
    · refine ⟨s, Nat.le_refl s, by omega, ?_⟩
      rw [h, show s + (n + 1) - s = n + 1 by omega, List.range'_succ]
    · obtain ⟨k, h1, h2, h3⟩ := suffix_range' n (s + 1) ks h
      exact ⟨k, by omega, by omega, by rw [h3]; congr 1; omega⟩

theorem suffix_forward {len : Nat} {ks : List Nat} (h : ks <:+ forward len) :
    ∃ k, k ≤ len ∧ ks = List.range' k (len - k) := by
  obtain ⟨k, _, h2, h3⟩ := suffix_range' len 0 ks h
  exact ⟨k, by omega, by rw [h3]; congr 1; omega⟩

theorem backward_succ (n : Nat) : backward (n + 1) = n :: backward n := by
  simp [backward, List.range_succ]

theorem suffix_backward : ∀ (n : Nat) (ks : List Nat), ks <:+ backward n →
    ∃ m, m ≤ n ∧ ks = backward m
  | 0, ks, h => by
    simp only [backward, List.range_zero, List.reverse_nil] at h
    rw [List.suffix_nil] at h
    exact ⟨0, Nat.le_refl 0, by simp [h, backward]⟩
  | n + 1, ks, h => by
    rw [backward_succ, List.suffix_cons_iff] at h
    rcases h with h | h
    · exact ⟨n + 1, Nat.le_refl _, by rw [h, backward_succ]⟩
    · obtain ⟨m, h1, h2⟩ := suffix_backward n ks h
      exact ⟨m, by omega, h2⟩

theorem mem_forward {len k : Nat} : k ∈ forward len ↔ k < len := by
  simp [forward, List.mem_range'_1]

theorem mem_backward {len k : Nat} : k ∈ backward len ↔ k < len := by
  simp [backward]

section Bailouts

variable {α β ρ σ : Type} {K : Kind} {body : BodyFn α ρ} {sbody : SBodyFn β σ}
  {fin : FinFn α ρ} {sfin : SFinFn β σ} {R : List Nat → α → β → Prop} {Q : ρ → σ → Prop}

theorem forward_bailout (hs : Sim K body sbody fin sfin R Q) {len : Nat} {s : St α} {b : β}
    (hi : Inv K s) (hr : R (forward len) s.acc b) {ks : List Nat} {s' : St α}
    (h : loop K.isDouble body fin (forward len) s = .bailout ks s') :
    ∃ k b', k ≤ len ∧ ks = List.range' k (len - k) ∧
      Reaches sbody (forward len) b s.arr ks b' s'.arr ∧ R ks s'.acc b' ∧ Inv K s' := by
  obtain ⟨b', hreach, hR, hI, hsuf⟩ := loop_bailout hs hi hr h
  obtain ⟨k, hk, hks⟩ := suffix_forward hsuf
  exact ⟨k, b', hk, hks, hreach, hR, hI⟩

theorem backward_bailout (hs : Sim K body sbody fin sfin R Q) {len : Nat} {s : St α} {b : β}
    (hi : Inv K s) (hr : R (backward len) s.acc b) {ks : List Nat} {s' : St α}
    (h : loop K.isDouble body fin (backward len) s = .bailout ks s') :
    ∃ m b', m ≤ len ∧ ks = backward m ∧
      Reaches sbody (backward len) b s.arr ks b' s'.arr ∧ R ks s'.acc b' ∧ Inv K s' := by
  obtain ⟨b', hreach, hR, hI, hsuf⟩ := loop_bailout hs hi hr h
  obtain ⟨m, hm, hks⟩ := suffix_backward len ks hsuf
  exact ⟨m, b', hm, hks, hreach, hR, hI⟩

end Bailouts

end ArrayWitness
