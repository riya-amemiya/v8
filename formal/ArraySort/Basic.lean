import ArraySort.Model

namespace ArraySort

open Torque

def Res.Good {ε α : Type} (Q : α → ε → Core → Prop) : Res ε α → Prop
  | .ok a e c => Q a e c
  | .throw _ => True
  | .ub => False
  | .abort => False

section Good

variable {ε α β : Type}

theorem Res.Good.mono {Q Q' : α → ε → Core → Prop} {r : Res ε α}
    (h : ∀ a e c, Q a e c → Q' a e c) (hr : r.Good Q) : r.Good Q' := by
  cases r <;> simp_all [Res.Good]

@[simp] theorem good_ok {Q : α → ε → Core → Prop} {a : α} {e : ε} {c : Core} :
    (Res.ok a e c).Good Q ↔ Q a e c := Iff.rfl

@[simp] theorem good_throw {Q : α → ε → Core → Prop} {e : ε} : (Res.throw e).Good Q ↔ True :=
  Iff.rfl

@[simp] theorem good_ub {Q : α → ε → Core → Prop} : (Res.ub : Res ε α).Good Q ↔ False := Iff.rfl

@[simp] theorem good_abort {Q : α → ε → Core → Prop} : (Res.abort : Res ε α).Good Q ↔ False :=
  Iff.rfl

theorem good_bind {m : M ε α} {f : α → M ε β} {Q : β → ε → Core → Prop} {e : ε} {c : Core} :
    ((m >>= f) e c).Good Q ↔ (m e c).Good (fun a e' c' => (f a e' c').Good Q) := by
  show (M.bind m f e c).Good Q ↔ _
  unfold M.bind
  cases m e c <;> simp [Res.Good]

theorem good_seq {m : M ε Unit} {f : M ε β} {Q : β → ε → Core → Prop} {e : ε} {c : Core} :
    ((do m; f) e c).Good Q ↔ (m e c).Good (fun _ e' c' => (f e' c').Good Q) := good_bind

@[simp] theorem good_pure {Q : α → ε → Core → Prop} {a : α} {e : ε} {c : Core} :
    ((pure a : M ε α) e c).Good Q ↔ Q a e c := Iff.rfl

theorem good_ite {p : Prop} [Decidable p] {m1 m2 : M ε α} {Q : α → ε → Core → Prop} {e : ε}
    {c : Core} : ((if p then m1 else m2) e c).Good Q ↔
      (if p then (m1 e c).Good Q else (m2 e c).Good Q) := by
  split <;> rfl

theorem good_dite {p : Prop} [Decidable p] {m1 : p → M ε α} {m2 : ¬p → M ε α}
    {Q : α → ε → Core → Prop} {e : ε} {c : Core} :
    ((if h : p then m1 h else m2 h) e c).Good Q ↔
      (if h : p then (m1 h e c).Good Q else (m2 h e c).Good Q) := by
  split <;> rfl

@[simp] theorem good_ubM {Q : α → ε → Core → Prop} {e : ε} {c : Core} :
    ((ub : M ε α) e c).Good Q ↔ False := Iff.rfl

@[simp] theorem good_abortM {Q : α → ε → Core → Prop} {e : ε} {c : Core} :
    ((abort : M ε α) e c).Good Q ↔ False := Iff.rfl

theorem good_if_abort {p : Prop} [Decidable p] {r : Res ε α} {Q : α → ε → Core → Prop} :
    (if p then r else .abort).Good Q ↔ p ∧ r.Good Q := by
  by_cases h : p
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    simp [h]

theorem good_if_ub {p : Prop} [Decidable p] {r : Res ε α} {Q : α → ε → Core → Prop} :
    (if p then r else .ub).Good Q ↔ p ∧ r.Good Q := by
  by_cases h : p
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    simp [h]

@[simp] theorem good_dcheck {p : Prop} [Decidable p] {Q : Unit → ε → Core → Prop} {e : ε}
    {c : Core} : ((dcheck p) e c).Good Q ↔ p ∧ Q () e c := by
  unfold dcheck
  exact good_if_ub

@[simp] theorem good_jsAny {x : Option Val} {Q : Val → ε → Core → Prop} {e : ε} {c : Core} :
    ((jsAny x) e c).Good Q ↔ ∃ v, x = some v ∧ Q v e c := by
  cases x <;> simp [jsAny, Res.Good, ub] <;> rfl

@[simp] theorem good_getCore {Q : Core → ε → Core → Prop} {e : ε} {c : Core} :
    ((getCore : M ε Core) e c).Good Q ↔ Q c e c := Iff.rfl

@[simp] theorem good_setCore {Q : Unit → ε → Core → Prop} {e : ε} {c c' : Core} :
    ((setCore c' : M ε Unit) e c).Good Q ↔ Q () e c' := Iff.rfl

@[simp] theorem good_getExt {Q : ε → ε → Core → Prop} {e : ε} {c : Core} :
    ((getExt : M ε ε) e c).Good Q ↔ Q e e c := Iff.rfl

@[simp] theorem good_ld {a : Arr} {i : Int} {Q : Option Val → ε → Core → Prop} {e : ε}
    {c : Core} : ((ld a i) e c).Good Q ↔
      (0 ≤ i ∧ i < (c.get a).length) ∧ Q ((c.get a).getD i.toNat none) e c := by
  unfold ld
  exact good_if_abort

@[simp] theorem good_st {a : Arr} {i : Int} {x : Option Val} {Q : Unit → ε → Core → Prop}
    {e : ε} {c : Core} : ((st a i x) e c).Good Q ↔
      (0 ≤ i ∧ i < (c.get a).length) ∧ Q () e (c.put a ((c.get a).set i.toNat x)) := by
  unfold st
  exact good_if_abort

theorem good_mv {a b : Arr} {i j : Int} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core} :
    ((mv a i b j) e c).Good Q ↔ (0 ≤ i ∧ i < (c.get a).length) ∧ (0 ≤ j ∧ j < (c.get b).length) ∧
      Q () e (c.put b ((c.get b).set j.toNat ((c.get a).getD i.toNat none))) := by
  unfold mv
  rw [good_bind]
  simp

@[simp] theorem good_compare {cmp : Cmp ε} {x y : Val} {Q : Int → ε → Core → Prop} {e : ε}
    {c : Core} : ((compare cmp x y) e c).Good Q ↔ ∀ o e', cmp e x y = some (o, e') → Q o e' c := by
  unfold compare
  split <;> simp_all [Res.Good]

@[simp] theorem good_ldInt {l : List Int} {i : Int} {Q : Int → ε → Core → Prop} {e : ε}
    {c : Core} : ((ldInt l i) e c).Good Q ↔ (0 ≤ i ∧ i < l.length) ∧ Q (l.getD i.toNat 0) e c := by
  unfold ldInt
  exact good_if_abort

@[simp] theorem good_getSize {Q : Int → ε → Core → Prop} {e : ε} {c : Core} :
    ((getSize : M ε Int) e c).Good Q ↔ 0 ≤ c.size ∧ Q c.size e c := by
  unfold getSize
  exact good_if_ub

@[simp] theorem good_setSize {s : Int} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core} :
    ((setSize s : M ε Unit) e c).Good Q ↔ Q () e { c with size := s } := Iff.rfl

@[simp] theorem good_getMinGallop {Q : Int → ε → Core → Prop} {e : ε} {c : Core} :
    ((getMinGallop : M ε Int) e c).Good Q ↔ Q c.minGallop e c := Iff.rfl

@[simp] theorem good_setMinGallop {g : Int} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core} :
    ((setMinGallop g : M ε Unit) e c).Good Q ↔ Q () e { c with minGallop := g } := Iff.rfl

@[simp] theorem good_runBase {r : Int} {Q : Int → ε → Core → Prop} {e : ε} {c : Core} :
    ((runBase r : M ε Int) e c).Good Q ↔
      (0 ≤ 2 * r ∧ 2 * r < c.runs.length) ∧ Q (c.runs.getD (2 * r).toNat 0) e c := by
  unfold runBase
  exact good_ldInt

@[simp] theorem good_runLen {r : Int} {Q : Int → ε → Core → Prop} {e : ε} {c : Core} :
    ((runLen r : M ε Int) e c).Good Q ↔
      (0 ≤ 2 * r + 1 ∧ 2 * r + 1 < c.runs.length) ∧ Q (c.runs.getD (2 * r + 1).toNat 0) e c := by
  unfold runLen
  exact good_ldInt

@[simp] theorem good_setRun {i v : Int} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core} :
    ((setRun i v : M ε Unit) e c).Good Q ↔
      (0 ≤ i ∧ i < c.runs.length) ∧ Q () e { c with runs := c.runs.set i.toNat v } := by
  unfold setRun
  exact good_if_abort

@[simp] theorem good_setRunBase {r v : Int} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core} :
    ((setRunBase r v : M ε Unit) e c).Good Q ↔
      (0 ≤ 2 * r ∧ 2 * r < c.runs.length) ∧ Q () e { c with runs := c.runs.set (2 * r).toNat v } := by
  unfold setRunBase
  exact good_setRun

@[simp] theorem good_setRunLen {r v : Int} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core} :
    ((setRunLen r v : M ε Unit) e c).Good Q ↔
      (0 ≤ 2 * r + 1 ∧ 2 * r + 1 < c.runs.length) ∧
        Q () e { c with runs := c.runs.set (2 * r + 1).toNat v } := by
  unfold setRunLen
  exact good_setRun

@[simp] theorem good_getPower {r : Int} {Q : Int → ε → Core → Prop} {e : ε} {c : Core} :
    ((getPower r : M ε Int) e c).Good Q ↔
      (0 ≤ r ∧ r < c.powers.length) ∧ Q (c.powers.getD r.toNat 0) e c := by
  unfold getPower
  exact good_ldInt

@[simp] theorem good_setPower {r v : Int} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core} :
    ((setPower r v : M ε Unit) e c).Good Q ↔
      (0 ≤ r ∧ r < c.powers.length) ∧ Q () e { c with powers := c.powers.set r.toNat v } := by
  unfold setPower
  exact good_if_abort

@[simp] theorem good_getTempArray {r : Int} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core} :
    ((getTempArray r : M ε Unit) e c).Good Q ↔
      if max kSortStateTempSize r ≤ c.temp.length then Q () e c
      else Q () e { c with temp := List.replicate (max kSortStateTempSize r).toNat (some (.smi 0)) } := by
  unfold getTempArray
  split <;> rfl

end Good

@[simp] theorem Core.get_work (c : Core) : c.get .work = c.work := rfl

@[simp] theorem Core.get_temp (c : Core) : c.get .temp = c.temp := rfl

@[simp] theorem Core.put_work (c : Core) (l : List (Option Val)) : c.put .work l = { c with work := l } :=
  rfl

@[simp] theorem Core.put_temp (c : Core) (l : List (Option Val)) : c.put .temp l = { c with temp := l } :=
  rfl

theorem Core.get_put_same (c : Core) (a : Arr) (l : List (Option Val)) : (c.put a l).get a = l := by
  cases a <;> rfl

theorem Core.get_put_ne (c : Core) {a b : Arr} (h : a ≠ b) (l : List (Option Val)) :
    (c.put a l).get b = c.get b := by
  cases a <;> cases b <;> simp_all

theorem Core.put_put (c : Core) (a : Arr) (l l' : List (Option Val)) :
    (c.put a l).put a l' = c.put a l' := by
  cases a <;> rfl

theorem Core.put_get (c : Core) (a : Arr) : c.put a (c.get a) = c := by
  cases a <;> rfl

theorem Core.put_runs (c : Core) (a : Arr) (l : List (Option Val)) : (c.put a l).runs = c.runs := by
  cases a <;> rfl

theorem Core.put_powers (c : Core) (a : Arr) (l : List (Option Val)) :
    (c.put a l).powers = c.powers := by
  cases a <;> rfl

theorem Core.put_size (c : Core) (a : Arr) (l : List (Option Val)) : (c.put a l).size = c.size := by
  cases a <;> rfl

theorem Core.put_minGallop (c : Core) (a : Arr) (l : List (Option Val)) :
    (c.put a l).minGallop = c.minGallop := by
  cases a <;> rfl

section Seg

variable {α : Type}

def seg (l : List α) (lo hi : Nat) : List α := (l.drop lo).take (hi - lo)

theorem getElem?_seg (l : List α) (lo hi k : Nat) :
    (seg l lo hi)[k]? = if k < hi - lo then l[lo + k]? else none := by
  simp [seg, List.getElem?_take, List.getElem?_drop]

theorem length_seg {l : List α} {lo hi : Nat} (h : hi ≤ l.length) : (seg l lo hi).length = hi - lo := by
  simp [seg, List.length_take, List.length_drop]
  omega

theorem seg_split (l : List α) {lo m hi : Nat} (h1 : lo ≤ m) (h2 : m ≤ hi) :
    seg l lo hi = seg l lo m ++ seg l m hi := by
  unfold seg
  rw [show hi - lo = (m - lo) + (hi - m) by omega, List.take_add, List.drop_drop]
  congr 3
  omega

theorem seg_congr {l l' : List α} {lo hi : Nat} (h : ∀ i, lo ≤ i → i < hi → l'[i]? = l[i]?) :
    seg l' lo hi = seg l lo hi := by
  apply List.ext_getElem?
  intro k
  rw [getElem?_seg, getElem?_seg]
  split
  · exact h _ (by omega) (by omega)
  · rfl

theorem seg_self (l : List α) (lo : Nat) : seg l lo lo = [] := by
  simp [seg]

theorem seg_single {l : List α} {i : Nat} (h : i < l.length) : seg l i (i + 1) = [l[i]] := by
  apply List.ext_getElem?
  intro k
  rw [getElem?_seg]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp [List.getElem?_eq_getElem h]
  · rw [ite_eq_right (by omega)]
    cases k with
    | zero => omega
    | succ k => simp

theorem seg_snoc {l : List α} {lo hi : Nat} (h1 : lo ≤ hi) (h2 : hi < l.length) :
    seg l lo (hi + 1) = seg l lo hi ++ [l[hi]] := by
  rw [seg_split l h1 (Nat.le_succ hi), seg_single h2]

theorem seg_cons {l : List α} {lo hi : Nat} (h1 : lo < hi) (h2 : lo < l.length) :
    seg l lo hi = l[lo] :: seg l (lo + 1) hi := by
  rw [seg_split l (Nat.le_succ lo) h1, seg_single h2]
  rfl

theorem mem_seg {l : List α} {lo hi : Nat} {x : α} :
    x ∈ seg l lo hi ↔ ∃ i, lo ≤ i ∧ i < hi ∧ l[i]? = some x := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨k, hk⟩
    rw [getElem?_seg] at hk
    split at hk
    · exact ⟨lo + k, by omega, by omega, hk⟩
    · simp at hk
  · rintro ⟨i, h1, h2, hx⟩
    refine ⟨i - lo, ?_⟩
    rw [getElem?_seg, ite_eq_left (by omega), show lo + (i - lo) = i by omega]
    exact hx

def over (l : List α) (pos : Nat) (s : List α) : List α :=
  l.take pos ++ s ++ l.drop (pos + s.length)

theorem getElem?_over {l s : List α} {pos : Nat} (h : pos + s.length ≤ l.length) (j : Nat) :
    (over l pos s)[j]? =
      if j < pos then l[j]? else if j < pos + s.length then s[j - pos]? else l[j]? := by
  have htake : (l.take pos).length = pos := by
    simp [List.length_take]
    omega
  unfold over
  rw [List.append_assoc]
  by_cases h1 : j < pos
  · rw [List.getElem?_append_left (by omega), List.getElem?_take]
    simp [h1]
  · rw [List.getElem?_append_right (by omega), htake]
    by_cases h2 : j < pos + s.length
    · rw [List.getElem?_append_left (by omega)]
      simp [h1, h2]
    · rw [List.getElem?_append_right (by omega), List.getElem?_drop]
      simp only [h1, h2, ite_false]
      congr 1
      omega

theorem length_over {l s : List α} {pos : Nat} (h : pos + s.length ≤ l.length) :
    (over l pos s).length = l.length := by
  simp [over, List.length_take]
  omega

theorem over_nil (l : List α) (pos : Nat) : over l pos [] = l := by
  simp [over]

theorem set_eq_over {l : List α} {i : Nat} {x : α} (h : i < l.length) : l.set i x = over l i [x] := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set, getElem?_over (by simp; omega)]
  by_cases h1 : j < i
  · simp [h1, show ¬ i = j by omega]
  · by_cases h2 : j = i
    · subst h2
      simp [h]
    · simp [h1, Ne.symm h2, show ¬ j < i + 1 by omega]

theorem over_snoc {l s : List α} {pos : Nat} {x : α}
    (h : pos + s.length < l.length) : (over l pos s).set (pos + s.length) x = over l pos (s ++ [x]) := by
  have h1 : pos + s.length ≤ l.length := Nat.le_of_lt h
  have h2 : pos + (s ++ [x]).length ≤ l.length := by simp; omega
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set, getElem?_over h1, getElem?_over h2, length_over h1, List.length_append,
    List.length_singleton]
  by_cases h3 : j < pos
  · simp [h3, show ¬ pos + s.length = j by omega]
  · by_cases h4 : j < pos + s.length
    · simp [h3, h4, show ¬ pos + s.length = j by omega, show j < pos + (s.length + 1) by omega,
        List.getElem?_append_left (show j - pos < s.length by omega)]
    · by_cases h5 : j = pos + s.length
      · subst h5
        simp [h, show ¬ pos + s.length < pos by omega]
      · simp [h3, h4, Ne.symm h5, show ¬ j < pos + (s.length + 1) by omega]

theorem over_cons {l s : List α} {pos : Nat} {x : α} (hp : 0 < pos)
    (h : pos + s.length ≤ l.length) : (over l pos s).set (pos - 1) x = over l (pos - 1) (x :: s) := by
  have h2 : pos - 1 + (x :: s).length ≤ l.length := by simp; omega
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set, getElem?_over h, getElem?_over h2, length_over h, List.length_cons]
  by_cases h3 : j < pos - 1
  · simp [h3, show ¬ pos - 1 = j by omega, show j < pos by omega]
  · by_cases h4 : j = pos - 1
    · subst h4
      simp [show pos - 1 < l.length by omega]
    · by_cases h5 : j < pos + s.length
      · simp [h3, Ne.symm h4, show ¬ j < pos by omega, h5, show j < pos - 1 + (s.length + 1) by omega,
          show j - (pos - 1) = (j - pos) + 1 by omega]
      · simp [h3, Ne.symm h4, show ¬ j < pos by omega, h5,
          show ¬ j < pos - 1 + (s.length + 1) by omega]

theorem getElem?_over_out {l s : List α} {pos j : Nat} (h : pos + s.length ≤ l.length)
    (hj : j < pos ∨ pos + s.length ≤ j) : (over l pos s)[j]? = l[j]? := by
  rw [getElem?_over h]
  rcases hj with hj | hj
  · simp [hj]
  · simp [show ¬ j < pos by omega, show ¬ j < pos + s.length by omega]

theorem seg_over_out {l s : List α} {pos lo hi : Nat} (h : pos + s.length ≤ l.length)
    (hd : hi ≤ pos ∨ pos + s.length ≤ lo) : seg (over l pos s) lo hi = seg l lo hi := by
  apply seg_congr
  intro i h1 h2
  exact getElem?_over_out h (by omega)

theorem seg_over_in {l s : List α} {pos : Nat} (h : pos + s.length ≤ l.length) :
    seg (over l pos s) pos (pos + s.length) = s := by
  apply List.ext_getElem?
  intro k
  rw [getElem?_seg, getElem?_over h]
  by_cases hk : k < s.length
  · simp [hk, show pos + k - pos = k by omega, show ¬ pos + k < pos by omega]
  · rw [ite_eq_right (by omega), List.getElem?_eq_none (by omega)]

theorem seg_over_left {l s : List α} {pos lo : Nat} (h : pos + s.length ≤ l.length) (hl : lo ≤ pos) :
    seg (over l pos s) lo (pos + s.length) = seg l lo pos ++ s := by
  rw [seg_split _ hl (Nat.le_add_right pos s.length), seg_over_out h (Or.inl (Nat.le_refl _)),
    seg_over_in h]

theorem seg_over_right {l s : List α} {pos hi : Nat} (h : pos + s.length ≤ l.length)
    (hh : pos + s.length ≤ hi) : seg (over l pos s) pos hi = s ++ seg l (pos + s.length) hi := by
  rw [seg_split _ (Nat.le_add_right pos s.length) hh, seg_over_in h,
    seg_over_out h (Or.inr (Nat.le_refl _))]

theorem seg_set_out {l : List α} {lo hi i : Nat} {x : α} (h : i < lo ∨ hi ≤ i) :
    seg (l.set i x) lo hi = seg l lo hi := by
  apply seg_congr
  intro j h1 h2
  rw [List.getElem?_set]
  split
  · omega
  · rfl

theorem seg_set_snoc {l : List α} {lo i : Nat} {x : α} (h1 : lo ≤ i) (h2 : i < l.length) :
    seg (l.set i x) lo (i + 1) = seg l lo i ++ [x] := by
  rw [set_eq_over h2]
  exact seg_over_left (s := [x]) (by simp; omega) h1

theorem seg_set_cons {l : List α} {i hi : Nat} {x : α} (h1 : i < hi) (h2 : i < l.length) :
    seg (l.set i x) i hi = x :: seg l (i + 1) hi := by
  rw [set_eq_over h2, seg_over_right (by simp; omega) (by simp; omega)]
  rfl

end Seg

end ArraySort
