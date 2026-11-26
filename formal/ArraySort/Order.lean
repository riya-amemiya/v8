import ArraySort.Basic

namespace ArraySort

open Torque

structure TotalPreorder (le : Val → Val → Bool) : Prop where
  total : ∀ a b, le a b = true ∨ le b a = true
  trans : ∀ a b c, le a b = true → le b c = true → le a c = true

def oleq (le : Val → Val → Bool) : Option Val → Option Val → Bool
  | none, _ => true
  | some _, none => false
  | some a, some b => le a b

def eqv (le : Val → Val → Bool) (x y : Option Val) : Bool := oleq le x y && oleq le y x

def msort (le : Val → Val → Bool) (l : List (Option Val)) : List (Option Val) := l.mergeSort (oleq le)

def Srt (le : Val → Val → Bool) (l : List (Option Val)) : Prop := l.Pairwise (fun a b => oleq le a b = true)

theorem merge_split {α : Type} (s : α → α → Bool) (X1 : List α) :
    ∀ (Y1 X2 Y2 : List α), (∀ x ∈ X1, ∀ y ∈ Y2, s x y = true) → (∀ y ∈ Y1, ∀ x ∈ X2, s x y = false) →
      List.merge (X1 ++ X2) (Y1 ++ Y2) s = List.merge X1 Y1 s ++ List.merge X2 Y2 s := by
  induction X1 with
  | nil =>
    intro Y1
    induction Y1 with
    | nil =>
      intro X2 Y2 _ _
      simp
    | cons y Y1 ih =>
      intro X2 Y2 h1 h2
      cases X2 with
      | nil => simp
      | cons x X2 =>
        have hxy : s x y = false := h2 y List.mem_cons_self x List.mem_cons_self
        rw [List.nil_append, List.cons_append, List.cons_merge_cons_neg s _ _ (by simp [hxy])]
        have := ih (x :: X2) Y2 (by simp) (fun b hb a ha => h2 b (List.mem_cons_of_mem _ hb) a ha)
        rw [List.nil_append] at this
        rw [this]
        simp
  | cons x X1 ihx =>
    intro Y1
    induction Y1 with
    | nil =>
      intro X2 Y2 h1 h2
      cases Y2 with
      | nil => simp
      | cons y Y2 =>
        have hxy : s x y = true := h1 x List.mem_cons_self y List.mem_cons_self
        rw [List.cons_append, List.nil_append, List.cons_merge_cons_pos s _ _ hxy]
        have := ihx [] X2 (y :: Y2) (fun a ha b hb => h1 a (List.mem_cons_of_mem _ ha) b hb) (by simp)
        rw [List.nil_append] at this
        rw [this]
        simp
    | cons y Y1 ihy =>
      intro X2 Y2 h1 h2
      rw [List.cons_append, List.cons_append]
      by_cases hxy : s x y = true
      · rw [List.cons_merge_cons_pos s _ _ hxy, List.cons_merge_cons_pos s _ _ hxy, List.cons_append]
        have := ihx (y :: Y1) X2 Y2 (fun a ha b hb => h1 a (List.mem_cons_of_mem _ ha) b hb) h2
        rw [List.cons_append] at this
        rw [this]
      · rw [List.cons_merge_cons_neg s _ _ hxy, List.cons_merge_cons_neg s _ _ hxy, List.cons_append]
        have := ihy X2 Y2 h1 (fun b hb a ha => h2 b (List.mem_cons_of_mem _ hb) a ha)
        rw [List.cons_append] at this
        rw [this]

theorem merge_take_left {α : Type} (s : α → α → Bool) {A1 A2 B : List α}
    (h : ∀ x ∈ A1, ∀ y ∈ B, s x y = true) : List.merge (A1 ++ A2) B s = A1 ++ List.merge A2 B s := by
  have := merge_split s A1 [] A2 B h (by simp)
  simpa using this

theorem merge_take_right {α : Type} (s : α → α → Bool) {A B1 B2 : List α}
    (h : ∀ y ∈ B1, ∀ x ∈ A, s x y = false) : List.merge A (B1 ++ B2) s = B1 ++ List.merge A B2 s := by
  have := merge_split s [] B1 A B2 (by simp) h
  simpa using this

theorem merge_drop_left {α : Type} (s : α → α → Bool) {A1 A2 B : List α}
    (h : ∀ y ∈ B, ∀ x ∈ A2, s x y = false) : List.merge (A1 ++ A2) B s = List.merge A1 B s ++ A2 := by
  have := merge_split s A1 B A2 [] (by simp) h
  simpa using this

theorem merge_drop_right {α : Type} (s : α → α → Bool) {A B1 B2 : List α}
    (h : ∀ x ∈ A, ∀ y ∈ B2, s x y = true) : List.merge A (B1 ++ B2) s = List.merge A B1 s ++ B2 := by
  have := merge_split s A B1 [] B2 h (by simp)
  simpa using this

theorem pairwise_of_all {α : Type} {R : α → α → Prop} {l : List α} (h : ∀ a ∈ l, ∀ b ∈ l, R a b) :
    l.Pairwise R := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    exact List.Pairwise.cons (fun b hb => h a List.mem_cons_self b (List.mem_cons_of_mem _ hb))
      (ih fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))

section

variable {le : Val → Val → Bool} (hle : TotalPreorder le)

include hle

theorem oleq_total : ∀ x y, (oleq le x y || oleq le y x) = true
  | none, _ => by simp [oleq]
  | some _, none => by simp [oleq]
  | some a, some b => by
    rcases hle.total a b with h | h <;> simp [oleq, h]

theorem oleq_trans : ∀ x y z, oleq le x y = true → oleq le y z = true → oleq le x z = true
  | none, _, _, _, _ => by simp [oleq]
  | some _, none, _, h, _ => by simp [oleq] at h
  | some _, some _, none, _, h => by simp [oleq] at h
  | some a, some b, some c, h1, h2 => by
    simp only [oleq] at h1 h2 ⊢
    exact hle.trans a b c h1 h2

theorem oleq_refl (x : Option Val) : oleq le x x = true := by
  have := oleq_total hle x x
  simpa using this

theorem oleq_of_not {x y : Option Val} (h : oleq le x y = false) : oleq le y x = true := by
  have := oleq_total hle x y
  simpa [h] using this

theorem oleq_false_of_le {x y z : Option Val} (h1 : oleq le x y = false) (h2 : oleq le x z = true) :
    oleq le z y = false := by
  cases h : oleq le z y
  · rfl
  · rw [oleq_trans hle x z y h2 h] at h1
    cases h1

theorem oleq_false_of_le' {x y z : Option Val} (h1 : oleq le x y = false) (h2 : oleq le z y = true) :
    oleq le x z = false := by
  cases h : oleq le x z
  · rfl
  · rw [oleq_trans hle x z y h h2] at h1
    cases h1

theorem srt_cons_lt {a y : Option Val} {A : List (Option Val)} (hs : Srt le (a :: A))
    (h : oleq le a y = false) : ∀ x ∈ a :: A, oleq le x y = false := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact h
  · exact oleq_false_of_le hle h ((List.pairwise_cons.1 hs).1 x hx)

theorem srt_cons_ge {b y : Option Val} {B : List (Option Val)} (hs : Srt le (b :: B))
    (h : oleq le y b = true) : ∀ x ∈ b :: B, oleq le y x = true := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact h
  · exact oleq_trans hle y b x h ((List.pairwise_cons.1 hs).1 x hx)

theorem pairwise_msort (l : List (Option Val)) : Srt le (msort le l) :=
  List.pairwise_mergeSort (oleq_trans hle) (oleq_total hle) l

theorem filter_msort (l : List (Option Val)) (x : Option Val) :
    (msort le l).filter (eqv le x) = l.filter (eqv le x) := by
  have hs : Srt le (l.filter (eqv le x)) := by
    apply pairwise_of_all
    intro a ha b hb
    simp only [List.mem_filter, eqv, Bool.and_eq_true] at ha hb
    exact oleq_trans hle a x b ha.2.2 hb.2.1
  have hsub := List.sublist_mergeSort (oleq_trans hle) (oleq_total hle) hs (List.filter_sublist (p := eqv le x))
  have h2 := hsub.filter (eqv le x)
  rw [List.filter_filter, show (fun a => eqv le x a && eqv le x a) = eqv le x by funext a; simp] at h2
  have hlen := ((List.mergeSort_perm l (oleq le)).filter (eqv le x)).length_eq
  exact (h2.eq_of_length hlen.symm).symm

theorem eq_of_char : ∀ (r1 r2 : List (Option Val)), r1.Perm r2 → Srt le r1 → Srt le r2 →
    (∀ x, r1.filter (eqv le x) = r2.filter (eqv le x)) → r1 = r2
  | [], r2, hp, _, _, _ => by
    cases r2 with
    | nil => rfl
    | cons b r2 => exact absurd hp.length_eq (by simp)
  | a :: r1, r2, hp, h1, h2, hf => by
    cases r2 with
    | nil => exact absurd hp.length_eq (by simp)
    | cons b r2 =>
      have ha : a ∈ b :: r2 := hp.subset List.mem_cons_self
      have hb : b ∈ a :: r1 := hp.symm.subset List.mem_cons_self
      have hab : eqv le a b = true := by
        rcases List.mem_cons.1 ha with rfl | ha'
        · simp [eqv, oleq_refl hle]
        · rcases List.mem_cons.1 hb with rfl | hb'
          · simp [eqv, oleq_refl hle]
          · simp only [eqv, Bool.and_eq_true]
            exact ⟨(List.pairwise_cons.1 h1).1 b hb', (List.pairwise_cons.1 h2).1 a ha'⟩
      have hfa := hf a
      simp only [List.filter_cons, show eqv le a a = true by simp [eqv, oleq_refl hle], hab, ite_true] at hfa
      have : a = b := (List.cons.inj hfa).1
      subst this
      have ht := eq_of_char r1 r2 hp.cons_inv (List.pairwise_cons.1 h1).2 (List.pairwise_cons.1 h2).2 (by
        intro x
        have := hf x
        simp only [List.filter_cons] at this
        split at this
        · exact (List.cons.inj this).2
        · exact this)
      rw [ht]

theorem msort_char {r l : List (Option Val)} (hp : r.Perm l) (hs : Srt le r)
    (hf : ∀ x, r.filter (eqv le x) = l.filter (eqv le x)) : r = msort le l :=
  eq_of_char hle r (msort le l) (hp.trans (List.mergeSort_perm l (oleq le)).symm) hs (pairwise_msort hle l)
    fun x => by rw [hf x, filter_msort hle]

theorem filter_merge (x : Option Val) (A : List (Option Val)) :
    ∀ (B : List (Option Val)), Srt le A → Srt le B →
      (List.merge A B (oleq le)).filter (eqv le x) = A.filter (eqv le x) ++ B.filter (eqv le x) := by
  induction A with
  | nil => intro B _ _; simp
  | cons a A iha =>
    intro B
    induction B with
    | nil => intro _ _; simp
    | cons b B ihb =>
      intro hA hB
      by_cases hab : oleq le a b = true
      · rw [List.cons_merge_cons_pos _ _ _ hab, List.filter_cons, iha (b :: B) (List.pairwise_cons.1 hA).2 hB,
          List.filter_cons (x := a)]
        split <;> simp
      · rw [List.cons_merge_cons_neg _ _ _ hab, List.filter_cons, ihb hA (List.pairwise_cons.1 hB).2,
          List.filter_cons (x := b)]
        split
        · next hxb =>
          have hnil : (a :: A).filter (eqv le x) = [] := by
            rw [List.filter_eq_nil_iff]
            intro y hy hxy
            simp only [eqv, Bool.and_eq_true] at hxb hxy
            have hlt := srt_cons_lt hle hA (by simpa using hab) y hy
            rw [oleq_trans hle y x b hxy.2 hxb.1] at hlt
            cases hlt
          rw [hnil]
          simp
        · simp

theorem msort_append (l1 l2 : List (Option Val)) :
    msort le (l1 ++ l2) = List.merge (msort le l1) (msort le l2) (oleq le) := by
  symm
  apply msort_char hle
  · exact (List.merge_perm_append (oleq le)).trans ((List.mergeSort_perm l1 _).append (List.mergeSort_perm l2 _))
  · exact List.pairwise_merge (oleq_trans hle) (oleq_total hle) _ _ (pairwise_msort hle l1) (pairwise_msort hle l2)
  · intro x
    rw [filter_merge hle x _ _ (pairwise_msort hle l1) (pairwise_msort hle l2), filter_msort hle, filter_msort hle,
      List.filter_append]

omit hle in
theorem msort_sorted {l : List (Option Val)} (h : Srt le l) : msort le l = l :=
  List.mergeSort_of_pairwise h

theorem msort_desc {l : List (Option Val)} (h : l.Pairwise (fun a b => oleq le a b = false)) :
    msort le l = l.reverse := by
  symm
  apply msort_char hle (List.reverse_perm l)
  · unfold Srt
    rw [List.pairwise_reverse]
    exact h.imp fun hab => oleq_of_not hle hab
  · intro x
    rw [List.filter_reverse]
    have hs : (l.filter (eqv le x)).Pairwise (fun a b => oleq le a b = false) :=
      h.sublist List.filter_sublist
    generalize hf : l.filter (eqv le x) = f at hs
    have hm : ∀ y ∈ f, eqv le x y = true := by
      intro y hy
      rw [← hf] at hy
      exact (List.mem_filter.1 hy).2
    match f, hs, hm with
    | [], _, _ => rfl
    | [_], _, _ => rfl
    | a :: b :: t, hs, hm =>
      have h1 := (List.pairwise_cons.1 hs).1 b (by simp)
      have ha := hm a (by simp)
      have hb := hm b (by simp)
      simp only [eqv, Bool.and_eq_true] at ha hb
      rw [oleq_trans hle a x b ha.2 hb.1] at h1
      cases h1

omit hle in
theorem msort_single (x : Option Val) : msort le [x] = [x] := by
  simp [msort]

omit hle in
theorem merge_insert {S1 S2 : List (Option Val)} {p : Option Val} (h1 : ∀ s ∈ S1, oleq le s p = true)
    (h2 : ∀ s ∈ S2, oleq le s p = false) : List.merge (S1 ++ S2) [p] (oleq le) = S1 ++ p :: S2 := by
  rw [merge_take_left (oleq le) (fun x hx y hy => by
    simp only [List.mem_singleton] at hy
    subst hy
    exact h1 x hx)]
  have := merge_take_right (oleq le) (A := S2) (B1 := [p]) (B2 := []) (fun y hy x hx => by
    simp only [List.mem_singleton] at hy
    subst hy
    exact h2 x hx)
  simp only [List.append_nil, List.merge_right] at this
  rw [this]
  rfl

end

end ArraySort
