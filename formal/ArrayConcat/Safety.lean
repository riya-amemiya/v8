import ArrayConcat.Model

namespace ArrayConcat

open Torque ArrayBuild

theorem ofClone_ne_ub {r : CloneResult} (h : r ≠ .ub) : ofClone r ≠ .ub := by
  cases r with
  | done a => nofun
  | ub => exact absurd rfl h

theorem fastPath_ne_ub {env : Env} {H : Heap} {receiver : Val} {args : List Val}
    (hH : HeapWF H) : fastPath env H receiver args ≠ .ub := by
  unfold fastPath
  split
  · rename_i p
    by_cases h1 : args = [] ∧ forConcat env (H p) = true
    · rw [ite_eq_left h1]
      exact ofClone_ne_ub (clone_ne_ub (hH p))
    · rw [ite_eq_right h1]
      by_cases h2 : forConcat env (H p) = true ∧ (H p).length = 0
      · rw [ite_eq_left h2]
        split
        · next q =>
          by_cases h3 : (H q).forCopy = true
          · rw [ite_eq_left h3]
            exact ofClone_ne_ub (clone_ne_ub (hH q))
          · rw [ite_eq_right h3]
            nofun
        · nofun
      · rw [ite_eq_right h2]
        nofun
  · nofun

theorem forCopy_fast {a : JSArr} (hw : a.WF) (h : a.forCopy = true) :
    a.forRead = true ∧ a.fast = true :=
  ⟨hw.fast_forRead (hw.forCopy_fast h), hw.forCopy_fast h⟩

theorem clone_of_forCopy {a a' : JSArr} (hw : a.WF) (hsl : a.SlackHoles) (hc : a.forCopy = true)
    (h : ofClone (cloneFastJSArray false a) = .done a') :
    a'.WF ∧ a'.SlackHoles ∧ a'.elems = a.elems ∧ a'.length = a.length := by
  have hfc := forCopy_fast hw hc
  cases hcl : cloneFastJSArray false a with
  | ub =>
    rw [hcl] at h
    cases h
  | done b =>
    rw [hcl] at h
    cases h
    have hs := clone_spec hw hsl hfc.1 (fun _ => hfc.2) hcl
    refine ⟨hs.wf, hs.slack, ?_, hs.length⟩
    rw [hs.elems]
    rfl

theorem fastPath_done {env : Env} {H : Heap} {receiver : Val} {args : List Val} {a' : JSArr}
    (hH : HeapWF H) (hS : ∀ p, (H p).SlackHoles)
    (h : fastPath env H receiver args = .done a') :
    a'.WF ∧ a'.SlackHoles ∧ ∃ p, receiver = .arr p ∧
      ((args = [] ∧ a'.elems = specConcat [H p] ∧ a'.length = (H p).length) ∨
        (∃ q, args = [.arr q] ∧ (H p).length = 0 ∧ a'.elems = specConcat [H p, H q] ∧
          a'.length = (H p).length + (H q).length)) := by
  unfold fastPath at h
  split at h
  · rename_i p
    by_cases h1 : args = [] ∧ forConcat env (H p) = true
    · rw [ite_eq_left h1] at h
      have hfc : (H p).forCopy = true := by
        have := h1.2
        unfold forConcat at this
        simp only [Bool.and_eq_true] at this
        exact this.2
      obtain ⟨hw, hsl, he, hl⟩ := clone_of_forCopy (hH p) (hS p) hfc h
      refine ⟨hw, hsl, p, rfl, Or.inl ⟨h1.1, ?_, hl⟩⟩
      rw [he]
      simp [specConcat]
    · rw [ite_eq_right h1] at h
      by_cases h2 : forConcat env (H p) = true ∧ (H p).length = 0
      · rw [ite_eq_left h2] at h
        split at h
        · next q =>
          by_cases h3 : (H q).forCopy = true
          · rw [ite_eq_left h3] at h
            obtain ⟨hw, hsl, he, hl⟩ := clone_of_forCopy (hH q) (hS q) h3 h
            have hz : (H p).elems = [] := by
              rw [← List.length_eq_zero_iff, JSArr.elems_length (hH p), h2.2]
            refine ⟨hw, hsl, p, rfl, Or.inr ⟨q, rfl, h2.2, ?_, ?_⟩⟩
            · rw [he]
              simp [specConcat, hz]
            · rw [hl, h2.2]
              omega
          · rw [ite_eq_right h3] at h
            cases h
        · cases h
      · rw [ite_eq_right h2] at h
        cases h
  · cases h

end ArrayConcat
