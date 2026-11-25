import ArrayFlat.Safety

namespace ArrayFlat

open Torque

theorem step1_stack {cfg : Config} {H : Heap} (s t : P1) (hs : s.stack.length ≤ 1024)
    (h : step1 cfg H s = .cont t) : t.stack.length ≤ 1024 := by
  unfold step1 at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hst : s.stack with
    | nil => simp [hst] at h
    | cons g rest =>
      simp only [hst] at h
      split at h
      · cases h
        rw [hst] at hs
        simp at hs ⊢
        omega
      · cases h
  | bail => simp [hf] at h
  | oob => simp [hf] at h
  | elem x =>
    cases x with
    | none =>
      simp only [hf] at h
      cases h
      exact hs
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        exact hs
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        · exact hs
        · exact hs
        · simp only [List.length_cons, kMaxFlatFastStackEntries] at *
          omega

theorem stepGen_stack {cfg : Config} {H : Heap} (s t : P2) (hs : s.stack.length ≤ 1024)
    (h : stepGen cfg H s = .cont t) : t.stack.length ≤ 1024 := by
  unfold stepGen at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hst : s.stack with
    | nil => simp [hst] at h
    | cons g rest =>
      simp only [hst] at h
      split at h
      · cases h
        rw [hst] at hs
        simp at hs ⊢
        omega
      · cases h
  | bail => simp [hf] at h
  | oob => simp [hf] at h
  | elem x =>
    cases x with
    | none =>
      simp only [hf] at h
      cases h
      exact hs
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        exact hs
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        · exact hs
        · simp only [List.length_cons, kMaxFlatFastStackEntries] at *
          omega

theorem pass1_stack_bound {cfg : Config} {H : Heap} {root srcLen depth : Nat} {t : P1}
    (hr : Reach (step1 cfg H) (init1 root srcLen depth) t) : t.stack.length ≤ 1024 :=
  hr.invariant (P := fun s => s.stack.length ≤ 1024) (fun s t hs h => step1_stack s t hs h)
    (by simp [init1])

theorem gen_stack_bound {cfg : Config} {H : Heap} {root srcLen depth len : Nat} {t : P2}
    (hr : Reach (stepGen cfg H) (init2 root srcLen depth len) t) : t.stack.length ≤ 1024 :=
  hr.invariant (P := fun s => s.stack.length ≤ 1024) (fun s t hs h => stepGen_stack s t hs h)
    (by simp [init2])

def nest1 (H : Heap) : Nat → List (Option Val) → Nat
  | 0, _ => 0
  | d + 1, l => (l.map fun
    | some (.arr q) =>
      if (H q).kind = .packedSmi ∨ (H q).kind = .packedDouble then 0
      else nest1 H d (H q).elems + 1
    | _ => 0).foldr max 0

def nestDbl (H : Heap) : Nat → List (Option Val) → Nat
  | 0, _ => 0
  | d + 1, l => (l.map fun
    | some (.arr q) => if (H q).kind = .packedDouble then 0 else nestDbl H d (H q).elems + 1
    | _ => 0).foldr max 0

theorem nest1_nil (H : Heap) (d : Nat) : nest1 H d [] = 0 := by
  cases d <;> simp [nest1]

theorem nest1_none (H : Heap) (d : Nat) (l : List (Option Val)) :
    nest1 H d (none :: l) = nest1 H d l := by
  cases d <;> simp [nest1]

theorem nest1_leaf (H : Heap) {d : Nat} {v : Val} (l : List (Option Val))
    (h : descend? d v = none) : nest1 H d (some v :: l) = nest1 H d l := by
  cases d with
  | zero => simp [nest1]
  | succ n => cases v <;> simp_all [nest1, descend?]

theorem nest1_descend (H : Heap) {d d' q : Nat} {v : Val} (l : List (Option Val))
    (h : descend? d v = some (d', q)) :
    nest1 H d (some v :: l) =
      max (if (H q).kind = .packedSmi ∨ (H q).kind = .packedDouble then 0
        else nest1 H d' (H q).elems + 1) (nest1 H d l) := by
  obtain ⟨rfl, rfl⟩ := descend?_some h
  simp [nest1]

theorem nestDbl_nil (H : Heap) (d : Nat) : nestDbl H d [] = 0 := by
  cases d <;> simp [nestDbl]

theorem nestDbl_none (H : Heap) (d : Nat) (l : List (Option Val)) :
    nestDbl H d (none :: l) = nestDbl H d l := by
  cases d <;> simp [nestDbl]

theorem nestDbl_leaf (H : Heap) {d : Nat} {v : Val} (l : List (Option Val))
    (h : descend? d v = none) : nestDbl H d (some v :: l) = nestDbl H d l := by
  cases d with
  | zero => simp [nestDbl]
  | succ n => cases v <;> simp_all [nestDbl, descend?]

theorem nestDbl_descend (H : Heap) {d d' q : Nat} {v : Val} (l : List (Option Val))
    (h : descend? d v = some (d', q)) :
    nestDbl H d (some v :: l) =
      max (if (H q).kind = .packedDouble then 0 else nestDbl H d' (H q).elems + 1)
        (nestDbl H d l) := by
  obtain ⟨rfl, rfl⟩ := descend?_some h
  simp [nestDbl]

theorem nestDbl_noArr (H : Heap) (d : Nat) :
    ∀ l : List (Option Val), (∀ x ∈ l, ∃ v, x = some v ∧ ∀ p, v ≠ .arr p) → nestDbl H d l = 0
  | [], _ => nestDbl_nil H d
  | x :: l, hl => by
    obtain ⟨v, rfl, hv⟩ := hl x (by simp)
    rw [nestDbl_leaf H l (descend?_none_of_ne hv)]
    exact nestDbl_noArr H d l (fun y hy => hl y (by simp [hy]))

theorem nestDbl_le_nest1 {H : Heap} (hH : HeapWF H) :
    ∀ d (l : List (Option Val)), nestDbl H d l ≤ nest1 H d l + 1
  | 0, _ => by simp [nestDbl]
  | d + 1, [] => by simp [nestDbl_nil]
  | d + 1, none :: l => by
    rw [nestDbl_none, nest1_none]
    exact nestDbl_le_nest1 hH (d + 1) l
  | d + 1, some v :: l => by
    have ih := nestDbl_le_nest1 hH (d + 1) l
    cases hd : descend? (d + 1) v with
    | none =>
      rw [nestDbl_leaf H l hd, nest1_leaf H l hd]
      exact ih
    | some p =>
      obtain ⟨d', q⟩ := p
      obtain ⟨hdd, -⟩ := descend?_some hd
      have hdd : d' = d := by omega
      subst hdd
      rw [nestDbl_descend H l hd, nest1_descend H l hd]
      have hq := nestDbl_le_nest1 hH d' (H q).elems
      by_cases h1 : (H q).kind = .packedDouble
      · rw [ite_eq_left h1]
        omega
      · by_cases h2 : (H q).kind = .packedSmi
        · have h0 : nestDbl H d' (H q).elems = 0 := by
            apply nestDbl_noArr
            intro x hx
            obtain ⟨u, rfl, hu⟩ := packedSmi_elem (hH q) h2 hx
            exact ⟨u, rfl, not_arr_of_isNumber (isNumber_of_isSmi hu)⟩
          rw [ite_eq_right h1, ite_eq_left (Or.inl h2), h0]
          omega
        · rw [ite_eq_right h1, ite_eq_right (by rintro (h | h) <;> contradiction)]
          omega

def Frame.nest1 (H : Heap) (f : Frame) : Nat := ArrayFlat.nest1 H f.depth (f.rest H)

def Frame.nestDbl (H : Heap) (f : Frame) : Nat := ArrayFlat.nestDbl H f.depth (f.rest H)

def GoodStack (H : Heap) : List Frame → Prop
  | [] => True
  | f :: S => (0 < f.nest1 H → S.length + f.nest1 H ≤ 1024) ∧ GoodStack H S

def Good (H : Heap) (s : P1) : Prop :=
  (0 < s.cur.nest1 H → s.stack.length + s.cur.nest1 H ≤ 1024) ∧ GoodStack H s.stack

theorem nest1_hole {H : Heap} {f : Frame} (h : fetch H f = .elem none) :
    f.nest1 H = f.next.nest1 H := by
  simp only [Frame.nest1, rest_of_elem h, nest1_none]
  rfl

theorem nest1_leafF {H : Heap} {f : Frame} {v : Val} (h : fetch H f = .elem (some v))
    (hd : descend? f.depth v = none) : f.nest1 H = f.next.nest1 H := by
  simp only [Frame.nest1, rest_of_elem h, nest1_leaf H _ hd]
  rfl

theorem nest1_descendF {H : Heap} {f : Frame} {v : Val} {d q : Nat}
    (h : fetch H f = .elem (some v)) (hd : descend? f.depth v = some (d, q)) :
    f.nest1 H = max (if (H q).kind = .packedSmi ∨ (H q).kind = .packedDouble then 0
      else nest1 H d (H q).elems + 1) (f.next.nest1 H) := by
  simp only [Frame.nest1, rest_of_elem h, nest1_descend H _ hd]
  rfl

theorem nest1_exhausted {H : Heap} {f : Frame} (h : fetch H f = .exhausted) :
    f.nest1 H = 0 := by
  simp [Frame.nest1, rest_of_exhausted h, nest1_nil]

theorem step1_good_back {cfg : Config} {H : Heap} (s t : P1) (h : step1 cfg H s = .cont t)
    (ht : Good H t) : Good H s := by
  unfold step1 at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hst : s.stack with
    | nil => simp [hst] at h
    | cons g rest =>
      simp only [hst] at h
      split at h
      · cases h
        obtain ⟨h1, h2⟩ := ht
        refine ⟨?_, ?_⟩
        · intro hpos
          rw [nest1_exhausted hf] at hpos
          omega
        · rw [hst]
          exact ⟨h1, h2⟩
      · cases h
  | bail => simp [hf] at h
  | oob => simp [hf] at h
  | elem x =>
    cases x with
    | none =>
      simp only [hf] at h
      cases h
      obtain ⟨h1, h2⟩ := ht
      exact ⟨by rw [nest1_hole hf]; exact h1, h2⟩
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        obtain ⟨h1, h2⟩ := ht
        exact ⟨by rw [nest1_leafF hf hd]; exact h1, h2⟩
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        · obtain ⟨h1, h2⟩ := ht
          refine ⟨?_, h2⟩
          rw [nest1_descendF hf hd, ite_eq_left (Or.inl ‹_›)]
          simpa using h1
        · obtain ⟨h1, h2⟩ := ht
          refine ⟨?_, h2⟩
          rw [nest1_descendF hf hd, ite_eq_left (Or.inr ‹_›)]
          simpa using h1
        · obtain ⟨h1, h2, h3⟩ := ht
          refine ⟨?_, h3⟩
          have hk : ¬((H q).kind = .packedSmi ∨ (H q).kind = .packedDouble) := by
            rintro (hk | hk)
            · exact ‹¬(H q).kind = .packedSmi› hk
            · exact ‹¬(H q).kind = .packedDouble› hk
          rw [nest1_descendF hf hd, ite_eq_right hk]
          have hg : (⟨q, (H q).length, 0, d⟩ : Frame).nest1 H = nest1 H d (H q).elems := by
            simp [Frame.nest1, Frame.rest_new]
          rw [hg] at h1
          have hguard : s.stack.length < 1024 := by
            have := ‹¬kMaxFlatFastStackEntries ≤ 4 * s.stack.length›
            simp only [kMaxFlatFastStackEntries] at this
            omega
          intro _
          rcases Nat.le_total (nest1 H d (H q).elems + 1) (s.cur.next.nest1 H) with hle | hle
          · rw [Nat.max_eq_right hle]
            have := h2 (by omega)
            omega
          · rw [Nat.max_eq_left hle]
            by_cases hn : 0 < nest1 H d (H q).elems
            · have := h1 hn
              simp only [List.length_cons] at this
              omega
            · omega

theorem step1_done_good {cfg : Config} {H : Heap} (s : P1) (r : Nat × Kind)
    (h : step1 cfg H s = .done r) : Good H s := by
  unfold step1 at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hst : s.stack with
    | nil =>
      refine ⟨?_, ?_⟩
      · intro hpos
        rw [nest1_exhausted hf] at hpos
        omega
      · rw [hst]
        trivial
    | cons g rest =>
      simp only [hst] at h
      split at h <;> cases h
  | bail => simp [hf] at h
  | oob => simp [hf] at h
  | elem x =>
    cases x with
    | none => simp [hf] at h
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        repeat' split at h
        all_goals cases h

theorem run1_nest {cfg : Config} {H : Heap} {root srcLen depth : Nat} {r : Nat × Kind}
    (h : run1 cfg H (init1 root srcLen depth) = .ok r) :
    nest1 H depth (((H root).elems.take srcLen).drop 0) ≤ 1024 := by
  obtain ⟨t, ht, hd⟩ := run_ok h
  have hg := ht.backward (P := Good H) (fun s t h ht => step1_good_back s t h ht)
    (step1_done_good t r hd)
  obtain ⟨h1, _⟩ := hg
  by_cases hpos : 0 < (init1 root srcLen depth).cur.nest1 H
  · have := h1 hpos
    simpa [init1, Frame.nest1, Frame.rest] using this
  · simp only [init1, Frame.nest1, Frame.rest] at hpos
    omega

def DblStack (H : Heap) (N : Nat) : List Frame → Prop
  | [] => True
  | f :: S => S.length + f.nestDbl H ≤ N ∧ DblStack H N S

def DblInv (H : Heap) (N : Nat) (s : P2) : Prop :=
  s.stack.length + s.cur.nestDbl H ≤ N ∧ DblStack H N s.stack

theorem nestDbl_hole {H : Heap} {f : Frame} (h : fetch H f = .elem none) :
    f.nestDbl H = f.next.nestDbl H := by
  simp only [Frame.nestDbl, rest_of_elem h, nestDbl_none]
  rfl

theorem nestDbl_leafF {H : Heap} {f : Frame} {v : Val} (h : fetch H f = .elem (some v))
    (hd : descend? f.depth v = none) : f.nestDbl H = f.next.nestDbl H := by
  simp only [Frame.nestDbl, rest_of_elem h, nestDbl_leaf H _ hd]
  rfl

theorem nestDbl_descendF {H : Heap} {f : Frame} {v : Val} {d q : Nat}
    (h : fetch H f = .elem (some v)) (hd : descend? f.depth v = some (d, q)) :
    f.nestDbl H = max (if (H q).kind = .packedDouble then 0 else nestDbl H d (H q).elems + 1)
      (f.next.nestDbl H) := by
  simp only [Frame.nestDbl, rest_of_elem h, nestDbl_descend H _ hd]
  rfl

theorem stepDbl_fwd {cfg : Config} {H : Heap} {N : Nat} (s t : P2) (hs : DblInv H N s)
    (h : stepDbl cfg H s = .cont t) : DblInv H N t := by
  unfold stepDbl at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hst : s.stack with
    | nil => simp [hst] at h
    | cons g rest =>
      simp only [hst] at h
      split at h
      · cases h
        obtain ⟨_, h2⟩ := hs
        rw [hst] at h2
        exact h2
      · cases h
  | bail => simp [hf] at h
  | oob => simp [hf] at h
  | elem x =>
    cases x with
    | none =>
      simp only [hf] at h
      cases h
      obtain ⟨h1, h2⟩ := hs
      exact ⟨by rw [← nestDbl_hole hf]; exact h1, h2⟩
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        obtain ⟨h1, h2⟩ := hs
        exact ⟨by rw [← nestDbl_leafF hf hd]; exact h1, h2⟩
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        · obtain ⟨h1, h2⟩ := hs
          refine ⟨?_, h2⟩
          rw [nestDbl_descendF hf hd, ite_eq_left ‹_›] at h1
          simp only at h1 ⊢
          omega
        · obtain ⟨h1, h2⟩ := hs
          rw [nestDbl_descendF hf hd, ite_eq_right ‹_›] at h1
          have hg : (⟨q, (H q).length, 0, d⟩ : Frame).nestDbl H = nestDbl H d (H q).elems := by
            simp [Frame.nestDbl, Frame.rest_new]
          refine ⟨?_, ?_, h2⟩
          · simp only [List.length_cons, hg]
            omega
          · omega

theorem dbl_stack_le {cfg : Config} {H : Heap} {root srcLen depth len : Nat} {t : P2}
    (hr : Reach (stepDbl cfg H) (init2 root srcLen depth len) t) :
    t.stack.length ≤ nestDbl H depth (((H root).elems.take srcLen).drop 0) := by
  have := hr.invariant
    (P := DblInv H (nestDbl H depth (((H root).elems.take srcLen).drop 0)))
    (fun s t hs h => stepDbl_fwd s t hs h)
    ⟨by simp [init2, Frame.nestDbl, Frame.rest], trivial⟩
  exact Nat.le_trans (Nat.le_add_right _ _) this.1

theorem dbl_stack_bound {cfg : Config} {H : Heap} (hH : HeapWF H) {root srcLen depth len : Nat}
    (hc : calcLength cfg H root srcLen depth = .ok (len, .packedDouble)) {t : P2}
    (hr : Reach (stepDbl cfg H) (init2 root srcLen depth len) t) : t.stack.length ≤ 1025 := by
  have hle := dbl_stack_le hr
  unfold calcLength at hc
  split at hc
  · rename_i hk
    have h0 : nestDbl H depth (((H root).elems.take srcLen).drop 0) = 0 := by
      apply nestDbl_noArr
      intro x hx
      obtain ⟨v, rfl, hv⟩ := numeric_elems (hH root) hk x
        (List.mem_of_mem_take (by simpa using hx))
      exact ⟨v, rfl, not_arr_of_isNumber hv⟩
    omega
  · split at hc
    · cases hc
    · have h1 := run1_nest hc
      have h2 := nestDbl_le_nest1 hH depth (((H root).elems.take srcLen).drop 0)
      omega

end ArrayFlat
