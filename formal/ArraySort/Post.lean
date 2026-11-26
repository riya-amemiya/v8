import ArraySort.Order
import ArraySort.Safety

namespace ArraySort

open Torque

def Res.Post {ε α : Type} (Q : α → ε → Core → Prop) : Res ε α → Prop
  | .ok a e c => Q a e c
  | _ => True

section

variable {ε α β : Type}

theorem Res.Post.mono {Q Q' : α → ε → Core → Prop} {r : Res ε α}
    (h : ∀ a e c, Q a e c → Q' a e c) (hr : r.Post Q) : r.Post Q' := by
  cases r <;> simp_all [Res.Post]

theorem post_of_good {Q : α → ε → Core → Prop} {r : Res ε α} (h : r.Good Q) : r.Post Q := by
  cases r <;> simp_all [Res.Post, Res.Good]

theorem good_post {Q Q' : α → ε → Core → Prop} {r : Res ε α} (h1 : r.Good Q) (h2 : r.Post Q') :
    r.Good (fun a e c => Q a e c ∧ Q' a e c) := by
  cases r <;> simp_all [Res.Post, Res.Good]

theorem post_bind {m : M ε α} {f : α → M ε β} {Q : β → ε → Core → Prop} {e : ε} {c : Core} :
    ((m >>= f) e c).Post Q ↔ (m e c).Post (fun a e' c' => (f a e' c').Post Q) := by
  show (M.bind m f e c).Post Q ↔ _
  unfold M.bind
  cases m e c <;> simp [Res.Post]

theorem post_bind_of {m : M ε α} {f : α → M ε β} {P : α → ε → Core → Prop} {Q : β → ε → Core → Prop}
    {e : ε} {c : Core} (hm : (m e c).Post P) (hf : ∀ a e' c', P a e' c' → (f a e' c').Post Q) :
    ((m >>= f) e c).Post Q := by
  rw [post_bind]
  exact hm.mono hf

@[simp] theorem post_pure {Q : α → ε → Core → Prop} {a : α} {e : ε} {c : Core} :
    ((pure a : M ε α) e c).Post Q ↔ Q a e c := Iff.rfl

theorem post_ite {p : Prop} [Decidable p] {m1 m2 : M ε α} {Q : α → ε → Core → Prop} {e : ε}
    {c : Core} : ((if p then m1 else m2) e c).Post Q ↔
      (if p then (m1 e c).Post Q else (m2 e c).Post Q) := by
  split <;> rfl

theorem post_dite {p : Prop} [Decidable p] {m1 : p → M ε α} {m2 : ¬p → M ε α}
    {Q : α → ε → Core → Prop} {e : ε} {c : Core} :
    ((if h : p then m1 h else m2 h) e c).Post Q ↔
      (if h : p then (m1 h e c).Post Q else (m2 h e c).Post Q) := by
  split <;> rfl

@[simp] theorem post_ubM {Q : α → ε → Core → Prop} {e : ε} {c : Core} :
    ((ub : M ε α) e c).Post Q ↔ True := Iff.rfl

@[simp] theorem post_abortM {Q : α → ε → Core → Prop} {e : ε} {c : Core} :
    ((abort : M ε α) e c).Post Q ↔ True := Iff.rfl

@[simp] theorem post_dcheck {p : Prop} [Decidable p] {Q : Unit → ε → Core → Prop} {e : ε}
    {c : Core} : ((dcheck p) e c).Post Q ↔ (p → Q () e c) := by
  unfold dcheck
  split <;> simp_all [Res.Post]

theorem post_doIf {p : Prop} [Decidable p] {m : M ε Unit} {Q : Unit → ε → Core → Prop} {e : ε}
    {c : Core} : ((doIf p m) e c).Post Q ↔ (if p then (m e c).Post Q else Q () e c) := by
  unfold doIf
  split <;> rfl

@[simp] theorem post_jsAny {x : Option Val} {Q : Val → ε → Core → Prop} {e : ε} {c : Core} :
    ((jsAny x) e c).Post Q ↔ ∀ v, x = some v → Q v e c := by
  cases x <;> simp [jsAny, Res.Post, ub] <;> rfl

@[simp] theorem post_getCore {Q : Core → ε → Core → Prop} {e : ε} {c : Core} :
    ((getCore : M ε Core) e c).Post Q ↔ Q c e c := Iff.rfl

@[simp] theorem post_setCore {Q : Unit → ε → Core → Prop} {e : ε} {c c' : Core} :
    ((setCore c' : M ε Unit) e c).Post Q ↔ Q () e c' := Iff.rfl

theorem post_if_abort {p : Prop} [Decidable p] {r : Res ε α} {Q : α → ε → Core → Prop} :
    (if p then r else .abort).Post Q ↔ (p → r.Post Q) := by
  by_cases h : p
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    simp [h, Res.Post]

theorem post_if_ub {p : Prop} [Decidable p] {r : Res ε α} {Q : α → ε → Core → Prop} :
    (if p then r else .ub).Post Q ↔ (p → r.Post Q) := by
  by_cases h : p
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    simp [h, Res.Post]

@[simp] theorem post_ld {a : Arr} {i : Int} {Q : Option Val → ε → Core → Prop} {e : ε}
    {c : Core} : ((ld a i) e c).Post Q ↔
      (0 ≤ i ∧ i < (c.get a).length → Q ((c.get a).getD i.toNat none) e c) := by
  unfold ld
  exact post_if_abort

@[simp] theorem post_st {a : Arr} {i : Int} {x : Option Val} {Q : Unit → ε → Core → Prop}
    {e : ε} {c : Core} : ((st a i x) e c).Post Q ↔
      (0 ≤ i ∧ i < (c.get a).length → Q () e (c.put a ((c.get a).set i.toNat x))) := by
  unfold st
  exact post_if_abort

theorem post_mv {a b : Arr} {i j : Int} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core} :
    ((mv a i b j) e c).Post Q ↔ (0 ≤ i ∧ i < (c.get a).length → 0 ≤ j ∧ j < (c.get b).length →
      Q () e (c.put b ((c.get b).set j.toNat ((c.get a).getD i.toNat none)))) := by
  unfold mv
  rw [post_bind]
  simp only [post_ld, post_st]

@[simp] theorem post_compare {cmp : Cmp ε} {x y : Val} {Q : Int → ε → Core → Prop} {e : ε}
    {c : Core} : ((compare cmp x y) e c).Post Q ↔ ∀ o e', cmp e x y = some (o, e') → Q o e' c := by
  unfold compare
  split <;> simp_all [Res.Post]

@[simp] theorem post_compareKey {cmp : Cmp ε} {keyFirst : Bool} {key el : Val}
    {Q : Int → ε → Core → Prop} {e : ε} {c : Core} :
    ((compareKey cmp keyFirst key el) e c).Post Q ↔
      ∀ o e', cmp e (if keyFirst then key else el) (if keyFirst then el else key) = some (o, e') →
        Q o e' c := by
  unfold compareKey
  cases keyFirst <;> simp

@[simp] theorem post_ldInt {l : List Int} {i : Int} {Q : Int → ε → Core → Prop} {e : ε}
    {c : Core} : ((ldInt l i) e c).Post Q ↔ (0 ≤ i ∧ i < l.length → Q (l.getD i.toNat 0) e c) := by
  unfold ldInt
  exact post_if_abort

@[simp] theorem post_getSize {Q : Int → ε → Core → Prop} {e : ε} {c : Core} :
    ((getSize : M ε Int) e c).Post Q ↔ (0 ≤ c.size → Q c.size e c) := by
  unfold getSize
  exact post_if_ub

@[simp] theorem post_setSize {s : Int} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core} :
    ((setSize s : M ε Unit) e c).Post Q ↔ Q () e { c with size := s } := Iff.rfl

@[simp] theorem post_getMinGallop {Q : Int → ε → Core → Prop} {e : ε} {c : Core} :
    ((getMinGallop : M ε Int) e c).Post Q ↔ Q c.minGallop e c := Iff.rfl

@[simp] theorem post_setMinGallop {g : Int} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core} :
    ((setMinGallop g : M ε Unit) e c).Post Q ↔ Q () e { c with minGallop := g } := Iff.rfl

@[simp] theorem post_runBase {r : Int} {Q : Int → ε → Core → Prop} {e : ε} {c : Core} :
    ((runBase r : M ε Int) e c).Post Q ↔
      (0 ≤ 2 * r ∧ 2 * r < c.runs.length → Q (c.runs.getD (2 * r).toNat 0) e c) := by
  unfold runBase
  exact post_ldInt

@[simp] theorem post_runLen {r : Int} {Q : Int → ε → Core → Prop} {e : ε} {c : Core} :
    ((runLen r : M ε Int) e c).Post Q ↔
      (0 ≤ 2 * r + 1 ∧ 2 * r + 1 < c.runs.length → Q (c.runs.getD (2 * r + 1).toNat 0) e c) := by
  unfold runLen
  exact post_ldInt

@[simp] theorem post_setRun {i v : Int} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core} :
    ((setRun i v : M ε Unit) e c).Post Q ↔
      (0 ≤ i ∧ i < c.runs.length → Q () e { c with runs := c.runs.set i.toNat v }) := by
  unfold setRun
  exact post_if_abort

@[simp] theorem post_setRunBase {r v : Int} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core} :
    ((setRunBase r v : M ε Unit) e c).Post Q ↔
      (0 ≤ 2 * r ∧ 2 * r < c.runs.length → Q () e { c with runs := c.runs.set (2 * r).toNat v }) := by
  unfold setRunBase
  exact post_setRun

@[simp] theorem post_setRunLen {r v : Int} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core} :
    ((setRunLen r v : M ε Unit) e c).Post Q ↔
      (0 ≤ 2 * r + 1 ∧ 2 * r + 1 < c.runs.length →
        Q () e { c with runs := c.runs.set (2 * r + 1).toNat v }) := by
  unfold setRunLen
  exact post_setRun

@[simp] theorem post_getPower {r : Int} {Q : Int → ε → Core → Prop} {e : ε} {c : Core} :
    ((getPower r : M ε Int) e c).Post Q ↔
      (0 ≤ r ∧ r < c.powers.length → Q (c.powers.getD r.toNat 0) e c) := by
  unfold getPower
  exact post_ldInt

@[simp] theorem post_setPower {r v : Int} {Q : Unit → ε → Core → Prop} {e : ε} {c : Core} :
    ((setPower r v : M ε Unit) e c).Post Q ↔
      (0 ≤ r ∧ r < c.powers.length → Q () e { c with powers := c.powers.set r.toNat v }) := by
  unfold setPower
  exact post_if_abort

end

def CmpOK {ε : Type} (le : Val → Val → Bool) (cmp : Cmp ε) : Prop :=
  ∀ e x y o e', cmp e x y = some (o, e') → (o < 0 ↔ le y x = false)

def SrtAt (le : Val → Val → Bool) (l : List (Option Val)) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i ≤ j → j < hi → oleq le (l.getD i none) (l.getD j none) = true

theorem srtAt_of_srt {le : Val → Val → Bool} (hle : TotalPreorder le) {l : List (Option Val)} {lo hi : Nat}
    (hh : hi ≤ l.length) (hs : Srt le (seg l lo hi)) : SrtAt le l lo hi := by
  intro i j h1 h2 h3
  rcases Nat.lt_or_ge i j with hij | hij
  · have hlen : (seg l lo hi).length = hi - lo := length_seg hh
    have := List.pairwise_iff_getElem.1 hs (i - lo) (j - lo) (by omega) (by omega) (by omega)
    have ei := getElem?_seg l lo hi (i - lo)
    have ej := getElem?_seg l lo hi (j - lo)
    rw [ite_eq_left (by omega), show lo + (i - lo) = i by omega, List.getElem?_eq_getElem (by omega)] at ei
    rw [ite_eq_left (by omega), show lo + (j - lo) = j by omega, List.getElem?_eq_getElem (by omega)] at ej
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, ← ei, ← ej]
    exact this
  · have : i = j := by omega
    subst this
    exact oleq_refl hle _

theorem srt_of_srtAt {le : Val → Val → Bool} {l : List (Option Val)} {lo hi : Nat}
    (hh : hi ≤ l.length) (hs : SrtAt le l lo hi) : Srt le (seg l lo hi) := by
  unfold Srt
  rw [List.pairwise_iff_getElem]
  intro i j hi' hj hij
  have hlen : (seg l lo hi).length = hi - lo := length_seg hh
  have ei := getElem?_seg l lo hi i
  have ej := getElem?_seg l lo hi j
  rw [ite_eq_left (by omega), List.getElem?_eq_getElem (by omega)] at ei
  rw [ite_eq_left (by omega), List.getElem?_eq_getElem (by omega)] at ej
  have := hs (lo + i) (lo + j) (by omega) (by omega) (by omega)
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, ← ei, ← ej] at this
  exact this

end ArraySort
