import ArrayJoin.Buffer

namespace ArrayJoin

abbrev Stack := Option (List (Option Nat))

def minStack : Nat := 2

def pushScan (r : Nat) : List (Option Nat) → Option (Option (List (Option Nat)))
  | [] => none
  | none :: rest => some (some (some r :: rest))
  | some x :: rest => if x = r then some none else (pushScan r rest).map (Option.map (some x :: ·))

def joinStackPush (s : List (Option Nat)) (r : Nat) : Bool × List (Option Nat) :=
  match pushScan r s with
  | some none => (false, s)
  | some (some s') => (true, s')
  | none => (true, s ++ [some r] ++ List.replicate (grow s.length - s.length - 1) none)

def pushInline (st : Stack) (r : Nat) : Option (Bool × Stack) :=
  match st with
  | none => some (true, some (some r :: List.replicate (minStack - 1) none))
  | some [] => none
  | some (none :: rest) => some (true, some (some r :: rest))
  | some (some x :: rest) => some ((joinStackPush (some x :: rest) r).1,
      some (joinStackPush (some x :: rest) r).2)

def findIdx (r : Nat) : List (Option Nat) → Option Nat
  | [] => none
  | x :: xs => if x = some r then some 0 else (findIdx r xs).map (· + 1)

def joinStackPop (s : List (Option Nat)) (r : Nat) : Option (List (Option Nat)) :=
  match findIdx r s with
  | none => none
  | some i => if i = 0 ∧ minStack < s.length then some (List.replicate minStack none)
    else some (s.set i none)

def popInline (st : Stack) (r : Nat) : Option Stack :=
  match st with
  | none => none
  | some s =>
    if s.head? = some (some r) ∧ s.length = minStack then some (some (none :: s.tail))
    else (joinStackPop s r).map some

structure Lens (σ : Type) where
  get : σ → Stack
  set : σ → Stack → σ
  get_set : ∀ w s, get (set w s) = s

inductive Out (σ R : Type) where
  | ok (r : R) (w : σ)
  | thrown (w : σ)
  | bad

def cycleJoin {σ R : Type} (L : Lens σ) (r len : Nat) (empty : R) (inner : σ → Out σ R) (w : σ) :
    Out σ R :=
  if 0 < len then
    match pushInline (L.get w) r with
    | none => .bad
    | some (false, st) => .ok empty (L.set w st)
    | some (true, st) =>
      match inner (L.set w st) with
      | .ok res w' =>
        match popInline (L.get w') r with
        | some st' => .ok res (L.set w' st')
        | none => .bad
      | .thrown w' =>
        match popInline (L.get w') r with
        | some st' => .thrown (L.set w' st')
        | none => .bad
      | .bad => .bad
  else .ok empty w

def Rep (act : List Nat) (st : Stack) : Prop :=
  (st = none ∧ act = []) ∨
    ∃ m, st = some (act.map some ++ List.replicate m none) ∧ minStack ≤ act.length + m ∧ act.Nodup

def Preserves {σ R : Type} (L : Lens σ) (act : List Nat) (f : σ → Out σ R) : Prop :=
  ∀ w, Rep act (L.get w) →
    (∃ res w', f w = .ok res w' ∧ Rep act (L.get w')) ∨ (∃ w', f w = .thrown w' ∧ Rep act (L.get w'))

theorem pushScan_mem {r : Nat} : ∀ {act : List Nat} (m : Nat), r ∈ act →
    pushScan r (act.map some ++ List.replicate m none) = some none
  | [], _, h => absurd h (List.not_mem_nil)
  | x :: act, m, h => by
    simp only [List.map_cons, List.cons_append, pushScan]
    by_cases hx : x = r
    · rw [ite_eq_left hx]
    · rw [ite_eq_right hx]
      have : r ∈ act := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact h
      rw [pushScan_mem m this]
      rfl

theorem pushScan_hole {r : Nat} : ∀ {act : List Nat} (m : Nat), r ∉ act →
    pushScan r (act.map some ++ List.replicate (m + 1) none) =
      some (some ((act ++ [r]).map some ++ List.replicate m none))
  | [], m, _ => by simp [pushScan, List.replicate_succ]
  | x :: act, m, h => by
    simp only [List.map_cons, List.cons_append, pushScan]
    have hx : x ≠ r := fun e => h (e ▸ List.mem_cons_self)
    rw [ite_eq_right hx, pushScan_hole m (fun h' => h (List.mem_cons_of_mem _ h'))]
    simp

theorem pushScan_full {r : Nat} : ∀ {act : List Nat}, r ∉ act →
    pushScan r (act.map some) = none
  | [], _ => rfl
  | x :: act, h => by
    simp only [List.map_cons, pushScan]
    have hx : x ≠ r := fun e => h (e ▸ List.mem_cons_self)
    rw [ite_eq_right hx, pushScan_full (fun h' => h (List.mem_cons_of_mem _ h'))]
    rfl

theorem push_mem {act : List Nat} {st : Stack} (hr : Rep act st) {r : Nat} (h : r ∈ act) :
    pushInline st r = some (false, st) := by
  rcases hr with ⟨_, rfl⟩ | ⟨m, rfl, _, _⟩
  · exact absurd h List.not_mem_nil
  · cases act with
    | nil => exact absurd h List.not_mem_nil
    | cons x act =>
      simp only [List.map_cons, List.cons_append, pushInline]
      have := pushScan_mem (r := r) (act := x :: act) m h
      simp only [List.map_cons, List.cons_append] at this
      simp [joinStackPush, this]

theorem push_new {act : List Nat} {st : Stack} (hr : Rep act st) {r : Nat} (h : r ∉ act) :
    ∃ st', pushInline st r = some (true, st') ∧ Rep (act ++ [r]) st' := by
  rcases hr with ⟨rfl, rfl⟩ | ⟨m, rfl, hlen, hnd⟩
  · refine ⟨_, rfl, Or.inr ⟨minStack - 1, by simp, by simp [minStack], by simp⟩⟩
  · have hnd' : (act ++ [r]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hnd, by simp, fun a ha b hb e => h ?_⟩
      rw [List.mem_singleton] at hb
      rw [← hb, ← e]
      exact ha
    cases act with
    | nil =>
      cases m with
      | zero => simp [minStack] at hlen
      | succ m =>
        refine ⟨_, rfl, Or.inr ⟨m, by simp, by simp at hlen ⊢; omega, by simp⟩⟩
    | cons x act =>
      cases m with
      | zero =>
        have hs := pushScan_full (r := r) (act := x :: act) h
        have hj : joinStackPush ((x :: act).map some) r = (true, (x :: act).map some ++ [some r] ++
            List.replicate (grow (act.length + 1) - (act.length + 1) - 1) none) := by
          simp only [joinStackPush, hs, List.length_map, List.length_cons]
        refine ⟨some ((x :: act).map some ++ [some r] ++
            List.replicate (grow (act.length + 1) - (act.length + 1) - 1) none), ?_,
          Or.inr ⟨grow (act.length + 1) - (act.length + 1) - 1, by simp, ?_, hnd'⟩⟩
        · show pushInline (some ((x :: act).map some ++ [])) r = _
          rw [List.append_nil]
          show some ((joinStackPush ((x :: act).map some) r).1,
            some (joinStackPush ((x :: act).map some) r).2) = _
          rw [hj]
        · simp only [grow, minStack, List.length_append, List.length_cons, List.length_nil]
          omega
      | succ m =>
        have hs := pushScan_hole (r := r) (act := x :: act) m h
        have hj : joinStackPush ((x :: act).map some ++ List.replicate (m + 1) none) r =
            (true, (x :: act ++ [r]).map some ++ List.replicate m none) := by
          simp only [joinStackPush, hs]
        refine ⟨some ((x :: act ++ [r]).map some ++ List.replicate m none), ?_,
          Or.inr ⟨m, rfl, ?_, hnd'⟩⟩
        · show some ((joinStackPush ((x :: act).map some ++ List.replicate (m + 1) none) r).1,
            some (joinStackPush ((x :: act).map some ++ List.replicate (m + 1) none) r).2) = _
          rw [hj]
        · simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
          omega

theorem findIdx_last {r : Nat} : ∀ {act : List Nat} (m : Nat), r ∉ act →
    findIdx r ((act ++ [r]).map some ++ List.replicate m none) = some act.length
  | [], m, _ => by simp [findIdx]
  | x :: act, m, h => by
    simp only [List.cons_append, List.map_cons, findIdx]
    have hx : some x ≠ some r := fun e => h (Option.some.inj e ▸ List.mem_cons_self)
    rw [ite_eq_right hx, findIdx_last m (fun h' => h (List.mem_cons_of_mem _ h'))]
    simp

theorem pop_last {act : List Nat} {r : Nat} {st : Stack} (hr : Rep (act ++ [r]) st) :
    ∃ st', popInline st r = some st' ∧ Rep act st' := by
  rcases hr with ⟨_, h⟩ | ⟨m, rfl, hlen, hnd⟩
  · simp at h
  have hra : r ∉ act := by
    rw [List.nodup_append] at hnd
    intro h
    exact hnd.2.2 r h r (by simp) rfl
  have hnd0 : act.Nodup := (List.nodup_append.mp hnd).1
  unfold popInline
  dsimp only
  by_cases hfast : ((act ++ [r]).map some ++ List.replicate m none).head? = some (some r) ∧
      ((act ++ [r]).map some ++ List.replicate m none).length = minStack
  · rw [ite_eq_left hfast]
    have hact : act = [] := by
      cases act with
      | nil => rfl
      | cons x act =>
        have := hfast.1
        simp at this
        subst this
        exact absurd List.mem_cons_self hra
    subst hact
    refine ⟨_, rfl, Or.inr ⟨m + 1, by simp [List.replicate_succ], ?_, List.nodup_nil⟩⟩
    have := hfast.2
    simp [minStack] at this ⊢
    omega
  · rw [ite_eq_right hfast]
    unfold joinStackPop
    rw [findIdx_last m hra]
    dsimp only
    by_cases hshrink : act.length = 0 ∧ minStack < ((act ++ [r]).map some ++ List.replicate m none).length
    · rw [ite_eq_left hshrink]
      have : act = [] := List.eq_nil_of_length_eq_zero hshrink.1
      subst this
      exact ⟨_, rfl, Or.inr ⟨minStack, by simp, by simp, List.nodup_nil⟩⟩
    · rw [ite_eq_right hshrink]
      refine ⟨_, rfl, Or.inr ⟨m + 1, ?_, ?_, hnd0⟩⟩
      · congr 1
        rw [List.map_append, List.append_assoc, List.set_append_right _ _ (by simp),
          List.length_map, Nat.sub_self]
        simp [List.replicate_succ]
      · simp at hlen
        omega

theorem cycleJoin_preserves {σ R : Type} (L : Lens σ) {act : List Nat} {r len : Nat} (empty : R)
    {inner : σ → Out σ R} (hin : r ∉ act → Preserves L (act ++ [r]) inner) :
    Preserves L act (cycleJoin L r len empty inner) := by
  intro w hw
  unfold cycleJoin
  by_cases hlen : 0 < len
  · rw [ite_eq_left hlen]
    by_cases hra : r ∈ act
    · rw [push_mem hw hra]
      exact Or.inl ⟨empty, _, rfl, by rw [L.get_set]; exact hw⟩
    · obtain ⟨st', hp, hrep⟩ := push_new hw hra
      rw [hp]
      dsimp only
      have hrep' : Rep (act ++ [r]) (L.get (L.set w st')) := by rw [L.get_set]; exact hrep
      rcases hin hra _ hrep' with ⟨res, w', he, hr'⟩ | ⟨w', he, hr'⟩
      · rw [he]
        dsimp only
        obtain ⟨st2, hpop, hrep2⟩ := pop_last hr'
        rw [hpop]
        exact Or.inl ⟨res, _, rfl, by rw [L.get_set]; exact hrep2⟩
      · rw [he]
        dsimp only
        obtain ⟨st2, hpop, hrep2⟩ := pop_last hr'
        rw [hpop]
        exact Or.inr ⟨_, rfl, by rw [L.get_set]; exact hrep2⟩
  · rw [ite_eq_right hlen]
    exact Or.inl ⟨empty, w, rfl, hw⟩

theorem cycleJoin_cycle {σ R : Type} (L : Lens σ) {act : List Nat} {r len : Nat} (empty : R)
    (inner : σ → Out σ R) {w : σ} (hw : Rep act (L.get w)) (hr : r ∈ act) (hlen : 0 < len) :
    cycleJoin L r len empty inner w = .ok empty (L.set w (L.get w)) := by
  unfold cycleJoin
  rw [ite_eq_left hlen, push_mem hw hr]

end ArrayJoin
