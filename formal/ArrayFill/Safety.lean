import ArrayFill.Model

namespace ArrayFill

open Torque

theorem kindOk_toHoley {k : Kind} {x : Option Val} (h : kindOk k x = true) :
    kindOk k.toHoley x = true := by
  cases k <;> rcases x with _ | v <;> simp_all [Kind.toHoley, kindOk]

theorem kindOk_toHoley_none (k : Kind) : kindOk k.toHoley none = true := by
  cases k <;> rfl

theorem toHoley_isDouble (k : Kind) : k.toHoley.isDouble = k.isDouble := by
  cases k <;> rfl

theorem toHoley_isFast (k : Kind) : k.toHoley.isFast = k.isFast := by
  cases k <;> rfl

theorem kindOk_transition {src t : Kind} {x : Option Val} (h : kindOk src x = true) :
    kindOk (src.transitionTarget (src.moreGeneral t)) x = true := by
  cases src <;> cases t <;> rcases x with _ | v <;>
    simp_all [Kind.transitionTarget, Kind.moreGeneral, Kind.isMoreGeneral, Kind.isHoley,
      Kind.toHoley, kindOk, isNumber_of_isSmi]

theorem kindOk_optimalKind (ud : Bool) (v : Val) : kindOk (optimalKind ud v) (some v) = true := by
  cases v <;> cases ud <;> rfl

theorem kindOk_transition_value (src : Kind) (ud : Bool) (v : Val) :
    kindOk (src.transitionTarget (src.moreGeneral (optimalKind ud v))) (some v) = true := by
  cases src <;> cases v <;> cases ud <;> rfl

theorem numberValueOk_optimalKind {c : FillConfig} {v : Val}
    (h : (optimalKind c.undefinedDouble v).isDouble = true) : numberValueOk c v = true := by
  cases hc : c.undefinedDouble <;> cases v <;>
    simp_all [optimalKind, Kind.isDouble, numberValueOk, Val.isNumber]

theorem numberValueOk_transition {c : FillConfig} {src : Kind} {v : Val}
    (h : (src.transitionTarget (src.moreGeneral (optimalKind c.undefinedDouble v))).isDouble =
      true) : numberValueOk c v = true := by
  cases hc : c.undefinedDouble <;> cases src <;> cases v <;>
    simp_all [optimalKind, Kind.transitionTarget, Kind.moreGeneral, Kind.isMoreGeneral,
      Kind.isHoley, Kind.toHoley, Kind.isDouble, numberValueOk, Val.isNumber]

theorem transition_isFast {src : Kind} (hf : src.isFast = true) (ud : Bool) (v : Val) :
    (src.transitionTarget (src.moreGeneral (optimalKind ud v))).isFast = true := by
  cases src <;> cases v <;> cases ud <;>
    simp_all [optimalKind, Kind.transitionTarget, Kind.moreGeneral, Kind.isMoreGeneral,
      Kind.isHoley, Kind.toHoley, Kind.isFast]

theorem optimalKind_isFast (ud : Bool) (v : Val) : (optimalKind ud v).isFast = true := by
  cases v <;> cases ud <;> rfl

theorem transition_kind (a : JSArr) (dst : Kind) :
    (transition a dst).kind = a.kind.transitionTarget dst := by
  unfold transition
  dsimp only
  split
  · assumption
  · split <;> rfl

theorem transition_cow (a : JSArr) (dst : Kind)
    (h : (a.kind.transitionTarget dst).isDouble = true) (hw : a.WF) :
    (transition a dst).cow = false := by
  unfold transition
  dsimp only
  split
  · next h1 =>
    cases hc : a.cow
    · rfl
    · have := hw.cow_not_double hc
      rw [h1, h] at this
      exact absurd this (by decide)
  · first
    | rfl
    | split
      · rfl
      · next h2 => exact absurd h h2

theorem transition_store (a : JSArr) (dst : Kind) : (transition a dst).store = a.store := by
  unfold transition
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem transition_length (a : JSArr) (dst : Kind) : (transition a dst).length = a.length := by
  unfold transition
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem transition_flags (a : JSArr) (dst : Kind) :
    (transition a dst).forRead = a.forRead ∧ (transition a dst).fast = a.fast ∧
      (transition a dst).forCopy = a.forCopy := by
  unfold transition
  dsimp only
  split
  · exact ⟨rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl⟩

structure Prepared (c : FillConfig) (a b : JSArr) (v : Val) (start fin : Nat) : Prop where
  length_eq : b.length = a.length
  length_le : b.length ≤ b.store.length
  slack : b.SlackHoles
  cow_double : b.kind.isDouble = true → b.cow = false
  num_double : b.kind.isDouble = true → numberValueOk c v = true
  value_ok : kindOk b.kind (some v) = true
  fast : b.kind.isFast = true
  forRead_eq : b.forRead = a.forRead
  fast_eq : b.fast = a.fast
  forCopy_eq : b.forCopy = a.forCopy
  elems_ok : (∀ x ∈ b.elems, kindOk b.kind x = true) ∨ (start = 0 ∧ fin = b.length)
  spec_eq : specFill b.elems v start fin = specFill a.elems v start fin

theorem specFill_full {xs ys : List (Option Val)} {v : Val} {fin : Nat}
    (hx : xs.length = fin) (hy : ys.length = fin) : specFill xs v 0 fin = specFill ys v 0 fin := by
  unfold specFill
  rw [hx, hy]
  apply List.map_congr_left
  intro i hi
  simp at hi
  simp [hi]

theorem prepare_length (c : FillConfig) (env : Env) (a : JSArr) (v : Val) (start fin : Nat) :
    (prepare c env a v start fin).length = a.length := by
  unfold prepare replaceAll
  dsimp only
  split
  · rfl
  · split
    · split <;> rfl
    · exact transition_length a _

theorem prepare_spec {c : FillConfig} {env : Env} {a : JSArr} {v : Val} {start fin : Nat}
    (hw : a.WF) (hsl : a.SlackHoles) (hf : a.kind.isFast = true) :
    Prepared c a (prepare c env a v start fin) v start fin := by
  unfold prepare
  by_cases h1 : optimalKind c.undefinedDouble v = a.kind
  · simp only [h1, ite_true]
    exact {
      length_eq := rfl
      length_le := hw.length_le
      slack := hsl
      cow_double := fun hd => by
        cases hc : a.cow
        · rfl
        · rw [hw.cow_not_double hc] at hd
          exact absurd hd (by decide)
      num_double := fun hd => numberValueOk_optimalKind (by rw [h1]; exact hd)
      value_ok := by rw [← h1]; exact kindOk_optimalKind _ v
      fast := hf
      forRead_eq := rfl
      fast_eq := rfl
      forCopy_eq := rfl
      elems_ok := Or.inl hw.kind_ok
      spec_eq := rfl }
  · rw [ite_eq_right h1]
    by_cases h2 : start = 0 ∧ fin = a.length ∧ env.replaced = true
    · rw [ite_eq_left h2]
      obtain ⟨hs0, hfin, _⟩ := h2
      subst hs0
      subst hfin
      unfold replaceAll
      by_cases h3 : a.kind.isDouble ≠ (optimalKind c.undefinedDouble v).isDouble ∨ a.cow = true
      · rw [ite_eq_left h3]
        have hlen : (if (optimalKind c.undefinedDouble v).isDouble then
            List.replicate a.length (none : Option Val)
            else List.replicate a.length (some (Val.smi 0))).length = a.length := by
          split <;> simp
        exact {
          length_eq := rfl
          length_le := Nat.le_of_eq hlen.symm
          slack := by
            intro x hx
            rw [List.drop_eq_nil_of_le (Nat.le_of_eq hlen)] at hx
            simp at hx
          cow_double := fun _ => rfl
          num_double := numberValueOk_optimalKind
          value_ok := kindOk_optimalKind _ v
          fast := optimalKind_isFast _ v
          forRead_eq := rfl
          fast_eq := rfl
          forCopy_eq := rfl
          elems_ok := Or.inr ⟨rfl, rfl⟩
          spec_eq := by
            apply specFill_full
            · simp only [JSArr.elems, List.length_take, hlen, Nat.min_self]
            · exact JSArr.elems_length hw }
      · rw [ite_eq_right h3]
        have hc : a.cow = false := by
          cases hc : a.cow
          · rfl
          · exact absurd (Or.inr hc) h3
        exact {
          length_eq := rfl
          length_le := hw.length_le
          slack := hsl
          cow_double := fun _ => hc
          num_double := numberValueOk_optimalKind
          value_ok := kindOk_optimalKind _ v
          fast := optimalKind_isFast _ v
          forRead_eq := rfl
          fast_eq := rfl
          forCopy_eq := rfl
          elems_ok := Or.inr ⟨rfl, rfl⟩
          spec_eq := rfl }
    · rw [ite_eq_right h2]
      have hk := transition_kind a (a.kind.moreGeneral (optimalKind c.undefinedDouble v))
      have hst := transition_store a (a.kind.moreGeneral (optimalKind c.undefinedDouble v))
      have hfl := transition_flags a (a.kind.moreGeneral (optimalKind c.undefinedDouble v))
      have hlen := transition_length a (a.kind.moreGeneral (optimalKind c.undefinedDouble v))
      have helems : (transition a (a.kind.moreGeneral (optimalKind c.undefinedDouble v))).elems =
          a.elems := by
        simp only [JSArr.elems, hst, hlen]
      exact {
        length_eq := hlen
        length_le := by rw [hst, hlen]; exact hw.length_le
        slack := by
          intro x hx
          rw [hst, hlen] at hx
          exact hsl x hx
        cow_double := fun hd => transition_cow a _ (by rw [← hk]; exact hd) hw
        num_double := fun hd => numberValueOk_transition (by rw [← hk]; exact hd)
        value_ok := by rw [hk]; exact kindOk_transition_value _ _ v
        fast := by rw [hk]; exact transition_isFast hf _ v
        forRead_eq := hfl.1
        fast_eq := hfl.2.1
        forCopy_eq := hfl.2.2
        elems_ok := Or.inl (by
          intro x hx
          rw [helems] at hx
          rw [hk]
          exact kindOk_transition (hw.kind_ok x hx))
        spec_eq := by rw [helems] }

theorem store_eq_elems {b : JSArr} (hsl : b.SlackHoles) :
    b.store = b.elems ++ List.replicate (b.store.length - b.length) none := by
  have hd : b.store.drop b.length = List.replicate (b.store.length - b.length) none := by
    rw [List.eq_replicate_iff]
    exact ⟨by simp [List.length_drop], hsl⟩
  rw [← hd]
  simp [JSArr.elems]

theorem writable_spec {b : JSArr} (hsl : b.SlackHoles)
    (hcow : b.kind.isDouble = true → b.cow = false) :
    ∃ k, (if b.kind.isDouble then b else ensureWritable b) =
      { b with cow := false, store := b.elems ++ List.replicate k none } := by
  have hn := store_eq_elems hsl
  by_cases hd : b.kind.isDouble = true
  · refine ⟨b.store.length - b.length, ?_⟩
    have hc := hcow hd
    simp only [hd, ite_true]
    obtain ⟨kind, forRead, fast, forCopy, cow, length, store⟩ := b
    simp only at hc
    subst hc
    exact congrArg (JSArr.mk kind forRead fast forCopy false length) hn
  · simp only [hd, ite_false, Bool.false_eq_true]
    unfold ensureWritable
    cases hc : b.cow
    · refine ⟨b.store.length - b.length, ?_⟩
      simp only [Bool.false_eq_true, ite_false]
      obtain ⟨kind, forRead, fast, forCopy, cow, length, store⟩ := b
      simp only at hc
      subst hc
      exact congrArg (JSArr.mk kind forRead fast forCopy false length) hn
    · refine ⟨0, ?_⟩
      simp [JSArr.elems]

theorem accessorFill_spec {c : FillConfig} {b : JSArr} {v : Val} {start fin : Nat}
    (hl : b.length ≤ b.store.length) (hsl : b.SlackHoles)
    (hcow : b.kind.isDouble = true → b.cow = false)
    (hnum : b.kind.isDouble = true → numberValueOk c v = true) (hs : start ≤ fin) :
    ∃ k, fin ≤ b.length + k ∧ accessorFill c b v start fin =
      some { b with
        cow := false
        store := blit (b.elems ++ List.replicate k none) start
          (List.replicate (fin - start) (some v)) } := by
  obtain ⟨k1, hb1⟩ := writable_spec hsl hcow
  have helen : b.elems.length = b.length := by
    simp only [JSArr.elems, List.length_take]
    exact Nat.min_eq_left hl
  have hnum' : (b.kind.isDouble = true ∧ numberValueOk c v = false) ↔ False := by
    constructor
    · intro ⟨hd, hn⟩
      rw [hnum hd] at hn
      exact absurd hn (by decide)
    · intro h
      exact h.elim
  unfold accessorFill
  simp only [hb1, List.length_append, List.length_replicate, helen]
  by_cases hg : b.length + k1 < fin
  · refine ⟨k1 + (fin - (b.length + k1)), by omega, ?_⟩
    simp only [hg, ite_true, growTo, List.length_append, List.length_replicate, helen,
      Bool.false_eq_true, ite_false, hnum', List.append_assoc, List.replicate_append_replicate]
    rw [ite_eq_left (by omega)]
  · refine ⟨k1, by omega, ?_⟩
    simp only [hg, ite_false, Bool.false_eq_true, hnum', List.length_append,
      List.length_replicate, helen]
    rw [ite_eq_left (by omega)]

theorem getElem?_fillStore {xs : List (Option Val)} {k start fin : Nat} {v : Val}
    (hs : start ≤ fin) (hf : fin ≤ xs.length + k) (j : Nat) :
    (blit (xs ++ List.replicate k none) start (List.replicate (fin - start) (some v)))[j]? =
      if j < xs.length + k then some (if start ≤ j ∧ j < fin then some v else xs.getD j none)
      else none := by
  have hbuf : ∀ i, (xs ++ List.replicate k none)[i]? =
      if i < xs.length + k then some (xs.getD i none) else none := by
    intro i
    rw [List.getElem?_append, List.getD_eq_getElem?_getD]
    by_cases h1 : i < xs.length
    · rw [ite_eq_left h1, ite_eq_left (by omega), List.getElem?_eq_getElem h1]
      rfl
    · rw [ite_eq_right h1, List.getElem?_replicate, List.getElem?_eq_none (by omega)]
      by_cases h2 : i - xs.length < k
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
        rfl
      · rw [ite_eq_right h2, ite_eq_right (by omega)]
  rw [getElem?_blit (by simp; omega), hbuf]
  simp only [List.length_replicate, List.getElem?_replicate]
  by_cases h1 : j < start
  · rw [ite_eq_left h1, ite_eq_right (show ¬(start ≤ j ∧ j < fin) by omega)]
  · rw [ite_eq_right h1]
    by_cases h2 : j < start + (fin - start)
    · rw [ite_eq_left h2, ite_eq_left (by omega), ite_eq_left (by omega),
        ite_eq_left (show start ≤ j ∧ j < fin by omega)]
    · rw [ite_eq_right h2, ite_eq_right (show ¬(start ≤ j ∧ j < fin) by omega)]

theorem getElem?_specFill (xs : List (Option Val)) (v : Val) (start fin j : Nat) :
    (specFill xs v start fin)[j]? =
      if j < max xs.length fin then some (if start ≤ j ∧ j < fin then some v else xs.getD j none)
      else none := by
  unfold specFill
  rw [List.getElem?_map]
  by_cases h : j < max xs.length fin
  · rw [List.getElem?_range h, ite_eq_left h]
    rfl
  · rw [List.getElem?_eq_none (by simp; omega), ite_eq_right h]
    rfl

theorem mem_specFill {xs : List (Option Val)} {v : Val} {start fin : Nat} {x : Option Val}
    (hx : x ∈ specFill xs v start fin) :
    x = some v ∨ (x ∈ xs ∧ ¬(start = 0 ∧ xs.length ≤ fin)) ∨ (x = none ∧ xs.length < fin) := by
  unfold specFill at hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  by_cases h1 : start ≤ i ∧ i < fin
  · left
    simp [h1]
  · right
    rw [ite_eq_right h1, List.getD_eq_getElem?_getD]
    by_cases h2 : i < xs.length
    · left
      rw [List.getElem?_eq_getElem h2]
      refine ⟨List.getElem_mem h2, ?_⟩
      intro ⟨hs0, hle⟩
      exact h1 ⟨by omega, by omega⟩
    · right
      rw [List.getElem?_eq_none (by omega)]
      exact ⟨rfl, by omega⟩

theorem fillStore_take {xs : List (Option Val)} {k start fin : Nat} {v : Val}
    (hs : start ≤ fin) (hf : fin ≤ xs.length + k) :
    (blit (xs ++ List.replicate k none) start (List.replicate (fin - start) (some v))).take
      (max xs.length fin) = specFill xs v start fin := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take, getElem?_fillStore hs hf, getElem?_specFill]
  by_cases h : j < max xs.length fin
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, ite_eq_right h]

theorem fillStore_slack {xs : List (Option Val)} {k start fin : Nat} {v : Val}
    (hs : start ≤ fin) (hf : fin ≤ xs.length + k) :
    ∀ x ∈ (blit (xs ++ List.replicate k none) start (List.replicate (fin - start) (some v))).drop
      (max xs.length fin), x = none := by
  intro x hx
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
  rw [List.getElem?_drop, getElem?_fillStore hs hf] at hj
  by_cases h : max xs.length fin + j < xs.length + k
  · rw [ite_eq_left h,
      ite_eq_right (show ¬(start ≤ max xs.length fin + j ∧ max xs.length fin + j < fin) by omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hj
    exact (Option.some.inj hj).symm
  · rw [ite_eq_right h] at hj
    cases hj

theorem length_fillStore {xs : List (Option Val)} {k start fin : Nat} {v : Val}
    (hs : start ≤ fin) (hf : fin ≤ xs.length + k) :
    (blit (xs ++ List.replicate k none) start (List.replicate (fin - start) (some v))).length =
      xs.length + k := by
  rw [length_blit (by simp; omega)]
  simp

theorem prepared_mem {c : FillConfig} {a b : JSArr} {v : Val} {start fin : Nat}
    (hp : Prepared c a b v start fin) {x : Option Val} (hx : x ∈ specFill b.elems v start fin) :
    kindOk b.kind x = true ∨ (x = none ∧ b.length < fin) := by
  have helen : b.elems.length = b.length := by
    simp only [JSArr.elems, List.length_take]
    exact Nat.min_eq_left hp.length_le
  rcases mem_specFill hx with rfl | ⟨hm, hn⟩ | ⟨rfl, hlt⟩
  · exact Or.inl hp.value_ok
  · rcases hp.elems_ok with hok | ⟨h0, hfin⟩
    · exact Or.inl (hok x hm)
    · exact absurd ⟨h0, by omega⟩ hn
  · exact Or.inr ⟨rfl, by omega⟩

theorem prepare_double {c : FillConfig} {env : Env} {a : JSArr} {v : Val} {start fin : Nat}
    (hw : a.WF) (hd : (prepare c env a v start fin).kind.isDouble = true) :
    (prepare c env a v start fin).cow = false ∧ numberValueOk c v = true := by
  unfold prepare at hd ⊢
  dsimp only at hd ⊢
  by_cases h1 : optimalKind c.undefinedDouble v = a.kind
  · rw [ite_eq_left h1] at hd ⊢
    refine ⟨?_, numberValueOk_optimalKind (by rw [h1]; exact hd)⟩
    cases hc : a.cow
    · rfl
    · rw [hw.cow_not_double hc] at hd
      exact absurd hd (by decide)
  · rw [ite_eq_right h1] at hd ⊢
    by_cases h2 : start = 0 ∧ fin = a.length ∧ env.replaced = true
    · rw [ite_eq_left h2] at hd ⊢
      unfold replaceAll at hd ⊢
      by_cases h3 : a.kind.isDouble ≠ (optimalKind c.undefinedDouble v).isDouble ∨ a.cow = true
      · rw [ite_eq_left h3] at hd ⊢
        exact ⟨rfl, numberValueOk_optimalKind hd⟩
      · rw [ite_eq_right h3] at hd ⊢
        refine ⟨?_, numberValueOk_optimalKind hd⟩
        cases hc : a.cow
        · rfl
        · exact absurd (Or.inr hc) h3
    · rw [ite_eq_right h2] at hd ⊢
      rw [transition_kind] at hd
      exact ⟨transition_cow a _ hd hw, numberValueOk_transition hd⟩

theorem accessorFill_some {c : FillConfig} {b b' : JSArr} {v : Val} {start fin : Nat}
    (h : accessorFill c b v start fin = some b') :
    b'.kind = b.kind ∧ b'.length = b.length ∧ b'.cow = false := by
  unfold accessorFill at h
  dsimp only at h
  generalize hb1 : (if b.kind.isDouble = true then b else ensureWritable b) = b1 at h
  have hk1 : b1.kind = b.kind ∧ b1.length = b.length := by
    subst hb1
    split
    · exact ⟨rfl, rfl⟩
    · unfold ensureWritable
      split <;> exact ⟨rfl, rfl⟩
  generalize hb2 : (if b1.store.length < fin then { b1 with store := growTo b1.store fin }
    else b1) = b2 at h
  have hk2 : b2.kind = b1.kind ∧ b2.length = b1.length := by
    subst hb2
    split <;> exact ⟨rfl, rfl⟩
  split at h
  · cases h
  · rename_i hc
    split at h
    · cases h
    · split at h
      · cases h
        exact ⟨hk2.1.trans hk1.1, hk2.2.trans hk1.2, by simpa using hc⟩
      · cases h

theorem accessorFill_ne_none {c : FillConfig} {b : JSArr} {v : Val} {start fin : Nat}
    (hcow : b.kind.isDouble = true → b.cow = false)
    (hnum : b.kind.isDouble = true → numberValueOk c v = true) (hs : start ≤ fin) :
    accessorFill c b v start fin ≠ none := by
  unfold accessorFill
  dsimp only
  generalize hb1 : (if b.kind.isDouble = true then b else ensureWritable b) = b1
  have hk1 : b1.kind = b.kind ∧ b1.cow = false := by
    subst hb1
    by_cases hd : b.kind.isDouble = true
    · rw [ite_eq_left hd]
      exact ⟨rfl, hcow hd⟩
    · rw [ite_eq_right hd]
      unfold ensureWritable
      split
      · exact ⟨rfl, rfl⟩
      · rename_i hc
        exact ⟨rfl, by simpa using hc⟩
  generalize hb2 : (if b1.store.length < fin then { b1 with store := growTo b1.store fin }
    else b1) = b2
  have hk2 : b2.kind = b.kind ∧ b2.cow = false ∧ fin ≤ b2.store.length := by
    subst hb2
    split
    · refine ⟨hk1.1, hk1.2, ?_⟩
      simp only [growTo, List.length_append, List.length_replicate]
      omega
    · rename_i hg
      exact ⟨hk1.1, hk1.2, by omega⟩
  rw [hk2.2.1, hk2.1]
  have hn : ¬(b.kind.isDouble = true ∧ numberValueOk c v = false) := by
    intro ⟨hd, hn⟩
    rw [hnum hd] at hn
    exact absurd hn (by decide)
  rw [ite_eq_right (by decide), ite_eq_right hn, ite_eq_left ⟨hs, hk2.2.2⟩]
  nofun

theorem setLength_ne_ub (c : FillConfig) (b : JSArr) (fin : Nat) : setLength c b fin ≠ .ub := by
  unfold setLength
  split <;> nofun

theorem tryFast_ne_ub {c : FillConfig} {env : Env} {a : JSArr} {v : Val} {start fin : Nat}
    (hw : a.WF) (hs : start ≤ fin) : tryFast c env a v start fin ≠ .ub := by
  unfold tryFast
  split
  · nofun
  split
  · nofun
  split
  · nofun
  split
  · nofun
  split
  · exact setLength_ne_ub c _ fin
  · rename_i hnone
    exact absurd hnone (accessorFill_ne_none (fun hd => (prepare_double hw hd).1)
      (fun hd => (prepare_double hw hd).2) hs)

theorem tryFast_dcheck {c : FillConfig} {env : Env} {a a' : JSArr} {v : Val} {start fin : Nat}
    (h : tryFast c env a v start fin = .done a' true) : a.length < fin ∧ c.maxFast < fin := by
  unfold tryFast at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · rename_i b' hb
    obtain ⟨_, hl, _⟩ := accessorFill_some hb
    rw [prepare_length] at hl
    unfold setLength at h
    split at h
    · rename_i hlt
      exact ⟨by omega, of_decide_eq_true (Result.done.inj h).2⟩
    · exact absurd (Result.done.inj h).2 (by decide)
  · cases h

theorem tryFast_done {c : FillConfig} {env : Env} {a a' : JSArr} {v : Val} {start fin : Nat}
    {d : Bool} (hw : a.WF) (hsl : a.SlackHoles) (hs : start < fin)
    (h : tryFast c env a v start fin = .done a' d) :
    a'.WF ∧ a'.SlackHoles ∧ a'.cow = false ∧ a'.length = max a.length fin ∧
      a'.elems = specFill a.elems v start fin ∧
      (d = true ↔ a.length < fin ∧ c.maxFast < fin) := by
  unfold tryFast at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i h1
  have hf : a.kind.isFast = true := by
    cases hk : a.kind.isFast
    · exact absurd (Or.inl hk) h1
    · rfl
  split at h
  · cases h
  split at h
  · cases h
  have hp := prepare_spec (c := c) (env := env) (v := v) (start := start) (fin := fin) hw hsl hf
  obtain ⟨k, hk, hacc⟩ := accessorFill_spec hp.length_le hp.slack hp.cow_double hp.num_double
    (Nat.le_of_lt hs)
  rw [hacc] at h
  dsimp only at h
  have hlen := hp.length_eq
  generalize prepare c env a v start fin = b at hp hk h hlen
  have helen : b.elems.length = b.length := by
    simp only [JSArr.elems, List.length_take]
    exact Nat.min_eq_left hp.length_le
  rw [← helen] at hk
  have hstore := length_fillStore (v := v) (Nat.le_of_lt hs) hk
  have htake := fillStore_take (v := v) (Nat.le_of_lt hs) hk
  have hslack := fillStore_slack (v := v) (Nat.le_of_lt hs) hk
  rw [helen, hp.spec_eq] at htake
  rw [helen] at hslack hstore
  unfold setLength at h
  split at h
  · rename_i hlt
    cases h
    have hmax : max b.length fin = fin := Nat.max_eq_right (Nat.le_of_lt hlt)
    rw [hmax] at htake hslack
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hslack, rfl, by rw [← hlen, hmax], htake, ?_⟩
    · show fin ≤ _
      rw [hstore]
      omega
    · intro x hx
      change x ∈ List.take fin _ at hx
      rw [htake, ← hp.spec_eq] at hx
      rcases prepared_mem hp hx with hok | ⟨rfl, _⟩
      · exact kindOk_toHoley hok
      · exact kindOk_toHoley_none _
    · intro _
      show b.kind.toHoley.isFast = true
      rw [toHoley_isFast]
      exact hp.fast
    · intro hfa
      show b.forRead = true
      rw [hp.forRead_eq]
      exact hw.fast_forRead (by rw [← hp.fast_eq]; exact hfa)
    · intro hfc
      show b.fast = true
      rw [hp.fast_eq]
      exact hw.forCopy_fast (by rw [← hp.forCopy_eq]; exact hfc)
    · nofun
    · rw [← hlen]
      simp [hlt]
  · rename_i hge0
    have hge : ¬b.length < fin := hge0
    cases h
    have hmax : max b.length fin = b.length := Nat.max_eq_left (Nat.le_of_not_lt hge)
    rw [hmax] at htake hslack
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hslack, rfl, by rw [← hlen, hmax], htake, ?_⟩
    · show b.length ≤ _
      rw [hstore]
      omega
    · intro x hx
      change x ∈ List.take b.length _ at hx
      rw [htake, ← hp.spec_eq] at hx
      rcases prepared_mem hp hx with hok | ⟨_, hlt⟩
      · exact hok
      · exact absurd hlt hge
    · intro _
      exact hp.fast
    · intro hfa
      show b.forRead = true
      rw [hp.forRead_eq]
      exact hw.fast_forRead (by rw [← hp.fast_eq]; exact hfa)
    · intro hfc
      show b.fast = true
      rw [hp.fast_eq]
      exact hw.forCopy_fast (by rw [← hp.forCopy_eq]; exact hfc)
    · nofun
    · rw [← hlen]
      simp [hge]

theorem tryFast_handles {c : FillConfig} {env : Env} {a : JSArr} {v : Val} {start fin : Nat}
    (hw : a.WF) (hs : start ≤ fin) (h32 : fin ≤ 2 ^ 32 - 1) (hf : a.kind.isFast = true)
    (hm : env.movingAllowed = true) (hp : env.isArrayPrototype = false) (hl : fin ≤ c.maxLen)
    (hr : env.readOnlyLength = false) : ∃ a' d, tryFast c env a v start fin = .done a' d := by
  unfold tryFast
  rw [ite_eq_right (by omega), ite_eq_right (by simp [hf, hm, hp]), ite_eq_right (by omega),
    ite_eq_right (by simp [hr])]
  split
  · unfold setLength
    split
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  · rename_i hnone
    exact absurd hnone (accessorFill_ne_none (fun hd => (prepare_double hw hd).1)
      (fun hd => (prepare_double hw hd).2) hs)

theorem relIndex_le {len init : Nat} (hi : init ≤ len) (idx : Option Int) :
    relIndex len idx init ≤ len := by
  unfold relIndex
  split
  · exact hi
  · split
    · split
      · exact Nat.zero_le _
      · omega
    · exact Nat.min_le_right _ _

theorem fastPath_ne_ub {c : FillConfig} {env : Env} {a : JSArr} {v : Val} {len : Nat}
    {args : Args} (hw : a.WF) : fastPath c env a v len args ≠ .ub := by
  unfold fastPath
  split
  · nofun
  · rename_i h
    exact tryFast_ne_ub hw (by omega)

theorem fastPath_done {c : FillConfig} {env : Env} {a a' : JSArr} {v : Val} {len : Nat}
    {args : Args} {d : Bool} (hw : a.WF) (hsl : a.SlackHoles)
    (h : fastPath c env a v len args = .done a' d) :
    (endIndex len args ≤ startIndex len args ∧ a' = a ∧ d = false) ∨
      (startIndex len args < endIndex len args ∧ a'.WF ∧ a'.SlackHoles ∧ a'.cow = false ∧
        a'.length = max a.length (endIndex len args) ∧
        a'.elems = specFill a.elems v (startIndex len args) (endIndex len args) ∧
        (d = true ↔ a.length < endIndex len args ∧ c.maxFast < endIndex len args)) := by
  unfold fastPath at h
  split at h
  · rename_i hle
    cases h
    exact Or.inl ⟨hle, rfl, rfl⟩
  · rename_i hlt
    exact Or.inr ⟨by omega, tryFast_done hw hsl (by omega) h⟩

theorem fastPath_dcheck {c : FillConfig} {env : Env} {a a' : JSArr} {v : Val} {len : Nat}
    {args : Args} (h : fastPath c env a v len args = .done a' true) :
    a.length < len ∧ c.maxFast < endIndex len args := by
  unfold fastPath at h
  split at h
  · exact absurd (Result.done.inj h).2 (by decide)
  · have := tryFast_dcheck h
    have hle : endIndex len args ≤ len := relIndex_le (Nat.le_refl len) args.final
    exact ⟨by omega, this.2⟩

end ArrayFill
