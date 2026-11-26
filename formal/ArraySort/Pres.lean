import ArraySort.Impl

namespace ArraySort

open Torque

def Res.Inv {ε α : Type} (I : ε → Prop) : Res ε α → Prop
  | .ok _ e _ => I e
  | _ => True

def Pres {ε α : Type} (I : ε → Prop) (m : M ε α) : Prop := ∀ e c, I e → (m e c).Inv I

section

variable {ε : Type} (I : ε → Prop)

theorem pres_bind {α β : Type} {m : M ε α} {f : α → M ε β} (hm : Pres I m) (hf : ∀ a, Pres I (f a)) :
    Pres I (m >>= f) := by
  intro e c he
  show (M.bind m f e c).Inv I
  unfold M.bind
  have := hm e c he
  revert this
  cases m e c with
  | ok a e' c' => exact fun h => hf a e' c' h
  | throw _ => intro; trivial
  | ub => intro; trivial
  | abort => intro; trivial

theorem pres_pure {α : Type} (a : α) : Pres I (pure a : M ε α) := fun _ _ h => h

theorem pres_ite {α : Type} {p : Prop} [Decidable p] {m1 m2 : M ε α} (h1 : Pres I m1) (h2 : Pres I m2) :
    Pres I (if p then m1 else m2) := by
  split
  · exact h1
  · exact h2

theorem pres_dite {α : Type} {p : Prop} [Decidable p] {m1 : p → M ε α} {m2 : ¬p → M ε α}
    (h1 : ∀ h, Pres I (m1 h)) (h2 : ∀ h, Pres I (m2 h)) : Pres I (if h : p then m1 h else m2 h) := by
  split
  · exact h1 _
  · exact h2 _

theorem pres_ub {α : Type} : Pres I (ub : M ε α) := fun _ _ _ => trivial

theorem pres_abort {α : Type} : Pres I (abort : M ε α) := fun _ _ _ => trivial

theorem pres_dcheck {p : Prop} [Decidable p] : Pres I (dcheck p : M ε Unit) := by
  intro e c h
  unfold dcheck
  split <;> trivial

theorem pres_doIf {p : Prop} [Decidable p] {m : M ε Unit} (hm : Pres I m) : Pres I (doIf p m) := by
  unfold doIf
  exact pres_ite I hm (pres_pure I ())

theorem pres_jsAny {x : Option Val} : Pres I (jsAny x : M ε Val) := by
  cases x
  · exact pres_ub I
  · exact pres_pure I _

theorem pres_ld {a : Arr} {i : Int} : Pres I (ld a i : M ε (Option Val)) := by
  intro e c h
  unfold ld
  split
  · exact h
  · trivial

theorem pres_st {a : Arr} {i : Int} {x : Option Val} : Pres I (st a i x : M ε Unit) := by
  intro e c h
  unfold st
  split
  · exact h
  · trivial

theorem pres_mv {a b : Arr} {i j : Int} : Pres I (mv a i b j : M ε Unit) :=
  pres_bind I (pres_ld I) fun _ => pres_st I

theorem pres_ldInt {l : List Int} {i : Int} : Pres I (ldInt l i : M ε Int) := by
  intro e c h
  unfold ldInt
  split
  · exact h
  · trivial

theorem pres_runBase {r : Int} : Pres I (runBase r : M ε Int) := fun e c h => pres_ldInt I e c h

theorem pres_runLen {r : Int} : Pres I (runLen r : M ε Int) := fun e c h => pres_ldInt I e c h

theorem pres_getPower {r : Int} : Pres I (getPower r : M ε Int) := fun e c h => pres_ldInt I e c h

theorem pres_setRun {i v : Int} : Pres I (setRun i v : M ε Unit) := by
  intro e c h
  unfold setRun
  split
  · exact h
  · trivial

theorem pres_setRunBase {r v : Int} : Pres I (setRunBase r v : M ε Unit) := pres_setRun I

theorem pres_setRunLen {r v : Int} : Pres I (setRunLen r v : M ε Unit) := pres_setRun I

theorem pres_setPower {r v : Int} : Pres I (setPower r v : M ε Unit) := by
  intro e c h
  unfold setPower
  split
  · exact h
  · trivial

theorem pres_getSize : Pres I (getSize : M ε Int) := by
  intro e c h
  unfold getSize
  split
  · exact h
  · trivial

theorem pres_setSize {s : Int} : Pres I (setSize s : M ε Unit) := fun _ _ h => h

theorem pres_getMinGallop : Pres I (getMinGallop : M ε Int) := fun _ _ h => h

theorem pres_setMinGallop {g : Int} : Pres I (setMinGallop g : M ε Unit) := fun _ _ h => h

theorem pres_getCore : Pres I (getCore : M ε Core) := fun _ _ h => h

theorem pres_setCore {c' : Core} : Pres I (setCore c' : M ε Unit) := fun _ _ h => h

theorem pres_getTempArray {r : Int} : Pres I (getTempArray r : M ε Unit) := by
  intro e c h
  unfold getTempArray
  split
  · exact h
  · exact h

variable {cmp : Cmp ε} (hI : ∀ e x y o e', I e → cmp e x y = some (o, e') → I e')

include hI

theorem pres_compare {x y : Val} : Pres I (compare cmp x y) := by
  intro e c h
  unfold compare
  split
  · next o e' heq => exact hI e x y o e' h heq
  · trivial

theorem pres_compareKey {keyFirst : Bool} {key el : Val} : Pres I (compareKey cmp keyFirst key el) := by
  unfold compareKey
  exact pres_ite I (pres_compare I hI) (pres_compare I hI)

omit hI

theorem pres_copyFwd {src dst : Arr} {to : Int} : ∀ srcIdx dstIdx : Int,
    Pres I (copyFwd src dst to srcIdx dstIdx : M ε Unit)
  | srcIdx, dstIdx => by
    rw [copyFwd]
    exact pres_dite I (fun _ => pres_bind I (pres_mv I) fun _ => pres_copyFwd _ _) fun _ => pres_pure I _
termination_by srcIdx => (to - srcIdx).toNat
decreasing_by omega

theorem pres_copyBwd {src dst : Arr} {srcPos : Int} : ∀ srcIdx dstIdx : Int,
    Pres I (copyBwd src dst srcPos srcIdx dstIdx : M ε Unit)
  | srcIdx, dstIdx => by
    rw [copyBwd]
    exact pres_dite I (fun _ => pres_bind I (pres_mv I) fun _ => pres_copyBwd _ _) fun _ => pres_pure I _
termination_by srcIdx => (srcIdx + 1 - srcPos).toNat
decreasing_by omega

theorem pres_copy {src dst : Arr} {sp dp n : Int} : Pres I (copy src sp dst dp n : M ε Unit) := by
  unfold copy
  exact pres_bind I (pres_dcheck I) fun _ => pres_bind I (pres_dcheck I) fun _ =>
    pres_bind I (pres_getCore I) fun _ => pres_bind I (pres_dcheck I) fun _ =>
    pres_bind I (pres_dcheck I) fun _ => pres_ite I (pres_copyBwd I _ _) (pres_copyFwd I _ _)

attribute [irreducible] Pres

macro "pres_step" : tactic => `(tactic| first
  | with_reducible exact pres_pure _ _
  | with_reducible exact pres_ub _
  | with_reducible exact pres_abort _
  | with_reducible exact pres_dcheck _
  | with_reducible exact pres_jsAny _
  | with_reducible exact pres_ld _
  | with_reducible exact pres_st _
  | with_reducible exact pres_mv _
  | with_reducible exact pres_runBase _
  | with_reducible exact pres_runLen _
  | with_reducible exact pres_getPower _
  | with_reducible exact pres_setRunBase _
  | with_reducible exact pres_setRunLen _
  | with_reducible exact pres_setPower _
  | with_reducible exact pres_getSize _
  | with_reducible exact pres_setSize _
  | with_reducible exact pres_getMinGallop _
  | with_reducible exact pres_setMinGallop _
  | with_reducible exact pres_getCore _
  | with_reducible exact pres_setCore _
  | with_reducible exact pres_getTempArray _
  | with_reducible exact pres_copy _
  | with_reducible exact pres_compare _ (by assumption)
  | with_reducible exact pres_compareKey _ (by assumption)
  | with_reducible apply pres_bind
  | with_reducible apply pres_ite
  | with_reducible apply pres_dite
  | with_reducible apply pres_doIf
  | assumption
  | (solve_by_elim (maxDepth := 2) only [*])
  | (dsimp only [])
  | (intro _))

macro "pres_auto" : tactic => `(tactic| repeat' pres_step)

variable (smiMax : Nat)

include hI

theorem pres_bisSearch {pivot : Val} : ∀ left right : Int, Pres I (bisSearch cmp pivot left right)
  | left, right => by
    rw [bisSearch]
    refine pres_dite I (fun h => ?_) fun _ => pres_pure I _
    have h1 := pres_bisSearch (pivot := pivot) left (left + (right - left) / 2)
    have h2 := pres_bisSearch (pivot := pivot) (left + (right - left) / 2 + 1) right
    pres_auto
termination_by left right => (right - left).toNat
decreasing_by all_goals omega

omit hI in
theorem pres_bisShift (left : Int) : ∀ p : Int, Pres I (bisShift left p : M ε Unit)
  | p => by
    rw [bisShift]
    refine pres_dite I (fun h => ?_) fun _ => pres_pure I _
    have h1 := pres_bisShift left (p - 1)
    pres_auto
termination_by p => (p - left).toNat
decreasing_by omega

theorem pres_bisLoop (low high : Int) : ∀ start : Int, Pres I (bisLoop cmp low high start)
  | start => by
    rw [bisLoop]
    refine pres_dite I (fun h => ?_) fun _ => pres_pure I _
    have h1 := pres_bisLoop low high (start + 1)
    have h2 := pres_bisShift I
    have h3 := fun p => pres_bisSearch I hI (pivot := p)
    pres_auto
termination_by start => (high - start).toNat
decreasing_by omega

theorem pres_binaryInsertionSort (low startArg high : Int) :
    Pres I (binaryInsertionSort cmp low startArg high) := by
  unfold binaryInsertionSort
  have := pres_bisLoop I hI low high
  pres_auto

theorem pres_countRunLoop (isDesc : Bool) (high : Int) : ∀ (prev : Val) (idx runLength : Int),
    Pres I (countRunLoop cmp isDesc high prev idx runLength)
  | prev, idx, runLength => by
    rw [countRunLoop]
    refine pres_dite I (fun h => ?_) fun _ => pres_pure I _
    have h1 := fun v => pres_countRunLoop isDesc high v (idx + 1) (runLength + 1)
    pres_auto
termination_by _ idx => (high - idx).toNat
decreasing_by all_goals omega

omit hI in
theorem pres_reverseLoop : ∀ low high : Int, Pres I (reverseLoop low high : M ε Unit)
  | low, high => by
    rw [reverseLoop]
    refine pres_dite I (fun h => ?_) fun _ => pres_pure I _
    have h1 := pres_reverseLoop (low + 1) (high - 1)
    pres_auto
termination_by low high => (high - low).toNat
decreasing_by omega

theorem pres_countAndMakeRun (lowArg high : Int) : Pres I (countAndMakeRun cmp lowArg high) := by
  unfold countAndMakeRun reverseRange
  have h1 := pres_countRunLoop I hI
  have h2 := pres_reverseLoop I (ε := ε)
  pres_auto

theorem pres_gallopPhase (a : Arr) (key : Val) (keyFirst plus breakNeg : Bool) (base hint maxOfs : Int) :
    ∀ lastOfs offset : Nat,
      Pres I (gallopPhase cmp smiMax a key keyFirst plus breakNeg base hint maxOfs lastOfs offset)
  | lastOfs, offset => by
    rw [gallopPhase]
    refine pres_dite I (fun h => ?_) fun _ => pres_pure I _
    have h1 := pres_gallopPhase a key keyFirst plus breakNeg base hint maxOfs offset
      (gallopNext smiMax maxOfs offset)
    pres_auto
termination_by _ offset => (maxOfs - offset).toNat
decreasing_by
  unfold gallopNext
  split <;> omega

theorem pres_gallopSearch (a : Arr) (key : Val) (keyFirst : Bool) (base : Int) :
    ∀ lastOfs offset : Int, Pres I (gallopSearch cmp a key keyFirst base lastOfs offset)
  | lastOfs, offset => by
    rw [gallopSearch]
    refine pres_dite I (fun h => ?_) fun _ => pres_pure I _
    have h1 := pres_gallopSearch a key keyFirst base lastOfs (lastOfs + (offset - lastOfs) / 2)
    have h2 := pres_gallopSearch a key keyFirst base (lastOfs + (offset - lastOfs) / 2 + 1) offset
    pres_auto
termination_by lastOfs offset => (offset - lastOfs).toNat
decreasing_by all_goals omega

theorem pres_gallop (isRight : Bool) (a : Arr) (key : Val) (base length hint : Int) :
    Pres I (gallop cmp smiMax isRight a key base length hint) := by
  unfold gallop
  have h1 := pres_gallopPhase I hI smiMax a key
  have h2 := pres_gallopSearch I hI a key
  pres_auto

theorem pres_lowGallopStep (s : MS) : Pres I (lowGallopStep cmp smiMax s) := by
  unfold lowGallopStep lowGallopB lowGallopC
  have h1 := pres_gallop I hI smiMax
  pres_auto

theorem pres_highGallopStep (baseA : Int) (s : MS) : Pres I (highGallopStep cmp smiMax baseA s) := by
  unfold highGallopStep highGallopB highGallopC
  have h1 := pres_gallop I hI smiMax
  pres_auto

theorem pres_lowLoop : ∀ (mg : Int) (ph : Ph) (s : MS), Pres I (lowLoop cmp smiMax mg ph s)
  | mg, .simple wa wb, s => by
    rw [lowLoop]
    refine pres_dite I (fun h => ?_) fun _ => pres_ub I
    have h1 := pres_lowLoop (mg + 1) (.gallop true 0 (wb + 1)) ⟨s.dest + 1, s.ct, s.cur + 1, s.la, s.lb - 1⟩
    have h2 := pres_lowLoop mg (.simple 0 (wb + 1)) ⟨s.dest + 1, s.ct, s.cur + 1, s.la, s.lb - 1⟩
    have h3 := pres_lowLoop (mg + 1) (.gallop true (wa + 1) 0) ⟨s.dest + 1, s.ct + 1, s.cur, s.la - 1, s.lb⟩
    have h4 := pres_lowLoop mg (.simple (wa + 1) 0) ⟨s.dest + 1, s.ct + 1, s.cur, s.la - 1, s.lb⟩
    pres_auto
  | mg, .gallop first wa wb, s => by
    rw [lowLoop]
    refine pres_ite I ?_ ?_
    · refine pres_bind I (pres_dcheck I) fun _ => pres_bind I (pres_setMinGallop I) fun _ =>
        pres_bind I (pres_lowGallopStep I hI smiMax s) fun r => ?_
      cases r with
      | exit x => exact pres_pure I x
      | cont s' na nb =>
        exact pres_dite I (fun h => pres_lowLoop (max 1 (mg - 1)) (.gallop false na nb) s') fun _ => pres_ub I
    · exact pres_bind I (pres_setMinGallop I) fun _ => pres_lowLoop (mg + 1) (.simple 0 0) s
termination_by _ ph s => 2 * (s.la.toNat + s.lb.toNat) + ph.rank
decreasing_by all_goals simp only [Ph.rank]; omega

theorem pres_highLoop (baseA : Int) : ∀ (mg : Int) (ph : Ph) (s : MS),
    Pres I (highLoop cmp smiMax baseA mg ph s)
  | mg, .simple wa wb, s => by
    rw [highLoop]
    refine pres_dite I (fun h => ?_) fun _ => pres_ub I
    have h1 := pres_highLoop baseA (mg + 1) (.gallop true (wa + 1) 0) ⟨s.dest - 1, s.ct, s.cur - 1, s.la - 1, s.lb⟩
    have h2 := pres_highLoop baseA mg (.simple (wa + 1) 0) ⟨s.dest - 1, s.ct, s.cur - 1, s.la - 1, s.lb⟩
    have h3 := pres_highLoop baseA (mg + 1) (.gallop true 0 (wb + 1)) ⟨s.dest - 1, s.ct - 1, s.cur, s.la, s.lb - 1⟩
    have h4 := pres_highLoop baseA mg (.simple 0 (wb + 1)) ⟨s.dest - 1, s.ct - 1, s.cur, s.la, s.lb - 1⟩
    pres_auto
  | mg, .gallop first wa wb, s => by
    rw [highLoop]
    refine pres_ite I ?_ ?_
    · refine pres_bind I (pres_dcheck I) fun _ => pres_bind I (pres_setMinGallop I) fun _ =>
        pres_bind I (pres_highGallopStep I hI smiMax baseA s) fun r => ?_
      cases r with
      | exit x => exact pres_pure I x
      | cont s' na nb =>
        exact pres_dite I (fun h => pres_highLoop baseA (max 1 (mg - 1)) (.gallop false na nb) s')
          fun _ => pres_ub I
    · exact pres_bind I (pres_setMinGallop I) fun _ => pres_highLoop baseA (mg + 1) (.simple 0 0) s
termination_by _ ph s => 2 * (s.la.toNat + s.lb.toNat) + ph.rank
decreasing_by all_goals simp only [Ph.rank]; omega

theorem pres_mergeLow (a b c d : Int) : Pres I (mergeLow cmp smiMax a b c d) := by
  unfold mergeLow
  refine pres_bind I (pres_dcheck I) fun _ => pres_bind I (pres_dcheck I) fun _ =>
    pres_bind I (pres_dcheck I) fun _ => pres_bind I (pres_getTempArray I) fun _ =>
    pres_bind I (pres_copy I) fun _ => pres_bind I (pres_mv I) fun _ => pres_bind I ?_ fun x => ?_
  · unfold lowRun
    have := pres_lowLoop I hI smiMax
    pres_auto
  · cases x <;> unfold lowFinish <;> pres_auto

theorem pres_mergeHigh (a b c d : Int) : Pres I (mergeHigh cmp smiMax a b c d) := by
  unfold mergeHigh
  refine pres_bind I (pres_dcheck I) fun _ => pres_bind I (pres_dcheck I) fun _ =>
    pres_bind I (pres_dcheck I) fun _ => pres_bind I (pres_getTempArray I) fun _ =>
    pres_bind I (pres_copy I) fun _ => pres_bind I (pres_mv I) fun _ => pres_bind I ?_ fun x => ?_
  · unfold highRun
    have := pres_highLoop I hI smiMax a
    pres_auto
  · cases x <;> unfold highFinish <;> pres_auto

theorem pres_mergeAt (i : Int) : Pres I (mergeAt cmp smiMax i) := by
  unfold mergeAt mergeAtTail
  have h1 := pres_gallop I hI smiMax
  have h2 := pres_mergeLow I hI smiMax
  have h3 := pres_mergeHigh I hI smiMax
  pres_auto

theorem pres_mergeCollapse (p : Int) : ∀ stackSize : Int, Pres I (mergeCollapse cmp smiMax p stackSize)
  | stackSize => by
    rw [mergeCollapse]
    refine pres_dite I (fun h => ?_) fun _ => pres_pure I _
    refine pres_bind I (pres_getPower I) fun pw => pres_ite I ?_ (pres_pure I _)
    refine pres_bind I (pres_mergeAt I hI smiMax _) fun _ => pres_bind I (pres_getSize I) fun s' => ?_
    exact pres_dite I (fun h2 => pres_mergeCollapse p s') fun _ => pres_ub I
termination_by stackSize => stackSize.toNat
decreasing_by omega

theorem pres_collapseAndPush (length low cur : Int) : Pres I (collapseAndPush cmp smiMax length low cur) := by
  unfold collapseAndPush pushRun nodePower
  have h1 := pres_mergeCollapse I hI smiMax
  pres_auto

theorem pres_mainLoop (length mrStep mrRemainder mrThreshold : Int) : ∀ low remaining mrAccum : Int,
    Pres I (mainLoop cmp smiMax length mrStep mrRemainder mrThreshold low remaining mrAccum)
  | low, remaining, mrAccum => by
    rw [mainLoop]
    refine pres_dite I (fun h => ?_) fun _ => pres_pure I _
    refine pres_bind I (pres_dcheck I) fun _ => pres_bind I (pres_countAndMakeRun I hI _ _) fun r =>
      pres_bind I ?_ fun cur => pres_bind I (pres_collapseAndPush I hI smiMax _ _ _) fun _ => ?_
    · unfold extendRun
      have := pres_binaryInsertionSort I hI
      pres_auto
    · exact pres_dite I (fun h2 => pres_mainLoop length mrStep mrRemainder mrThreshold _ _ _) fun _ => pres_ub I
termination_by _ remaining => remaining.toNat
decreasing_by omega

theorem pres_finalLoop : ∀ s : Int, Pres I (finalLoop cmp smiMax s)
  | s => by
    rw [finalLoop]
    refine pres_dite I (fun h => ?_) fun _ => pres_pure I _
    refine pres_bind I ?_ fun n => pres_bind I (pres_mergeAt I hI smiMax n) fun _ =>
      pres_bind I (pres_getSize I) fun s' => ?_
    · unfold finalPick
      pres_auto
    · exact pres_dite I (fun h2 => pres_finalLoop s') fun _ => pres_ub I
termination_by s => s.toNat
decreasing_by omega

theorem pres_sortCore (n : Int) : Pres I (sortCore cmp smiMax n) := by
  unfold sortCore powerSortImpl
  have h1 := pres_binaryInsertionSort I hI
  have h2 := pres_mainLoop I hI smiMax
  have h3 := pres_finalLoop I hI smiMax
  pres_auto

end

theorem good_inv {ε α : Type} {I : ε → Prop} {Q : α → ε → Core → Prop} {r : Res ε α} (h1 : r.Good Q)
    (h2 : r.Inv I) : r.Good (fun a e c => Q a e c ∧ I e) := by
  cases r <;> simp_all [Res.Good, Res.Inv]

theorem Pres.apply {ε α : Type} {I : ε → Prop} {m : M ε α} (h : Pres I m) {e : ε} {c : Core} (he : I e) :
    (m e c).Inv I := by
  unfold Pres at h
  exact h e c he

end ArraySort
