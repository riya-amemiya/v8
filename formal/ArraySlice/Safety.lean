import ArraySlice.Model

namespace ArraySlice

open Torque ArrayCopyCommon

def aval (s : Aliased) (src : List (Option Val)) (i : Nat) : Option Val :=
  match s.mapped[i]? with
  | some (some j) => s.context[j]?
  | _ => src.getD i none

theorem mappedValue_eq {s : Aliased} {src : List (Option Val)} {i : Nat} (hs : s.OK)
    (hm : i < s.mapped.length) (hl : i < src.length) : mappedValue s src i = some (aval s src i) := by
  unfold mappedValue aval
  rw [List.getElem?_eq_getElem hm]
  cases h : s.mapped[i] with
  | none =>
    simp only
    rw [List.getElem?_eq_getElem hl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
    rfl
  | some j =>
    have hj := hs i j (by rw [List.getElem?_eq_getElem hm, h])
    simp only
    rw [List.getElem?_eq_getElem hj]
    rfl

theorem aliasedLoop_eq {s : Aliased} {src : List (Option Val)} (hs : s.OK) :
    ∀ n i (out : List (Option Val)), i + n ≤ s.mapped.length → i + n ≤ src.length →
      aliasedLoop s src n i out = some (out ++ (List.range n).map fun j => aval s src (i + j))
  | 0, i, out, _, _ => by simp [aliasedLoop]
  | n + 1, i, out, h1, h2 => by
    rw [aliasedLoop, mappedValue_eq hs (by omega) (by omega)]
    dsimp only
    rw [aliasedLoop_eq hs n (i + 1) _ (by omega) (by omega)]
    congr 1
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.append_assoc, List.cons_append, List.nil_append,
      Nat.add_zero]
    congr 2
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    congr 1
    omega

theorem blit_head_piece {head piece : List (Option Val)} {count h0 : Nat} (hh : head.length = h0)
    (hc : h0 + piece.length = count) :
    blit (blit (List.replicate count none) h0 piece) 0 head = head ++ piece := by
  subst hc
  subst hh
  simp [blit, List.take_replicate, List.drop_replicate]

theorem getElem?_aliasedSpec (s : Aliased) (src : List (Option Val)) (start count i : Nat) :
    (aliasedSpec s src start count)[i]? =
      if i < count then some (aval s src (start + i)) else none := by
  unfold aliasedSpec
  rw [List.getElem?_map]
  by_cases hi : i < count
  · rw [List.getElem?_range hi, ite_eq_left hi]
    rfl
  · rw [List.getElem?_eq_none (by simp; omega), ite_eq_right hi]
    rfl

theorem aliasedSpec_eq {s : Aliased} {src : List (Option Val)} {start count h0 : Nat}
    (hh0 : h0 = min s.mapped.length (start + count) - start) (hsrc : start + count ≤ src.length) :
    ((List.range h0).map fun j => aval s src (start + j)) ++
      ((src.drop (start + h0)).take (count - h0)) = aliasedSpec s src start count := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_aliasedSpec, List.getElem?_append]
  simp only [List.length_map, List.length_range]
  by_cases hi : i < h0
  · rw [ite_eq_left hi, List.getElem?_map, List.getElem?_range hi, ite_eq_left (by omega)]
    rfl
  · rw [ite_eq_right hi, List.getElem?_take, List.getElem?_drop]
    by_cases hc : i < count
    · rw [ite_eq_left (by omega), ite_eq_left hc,
        show start + h0 + (i - h0) = start + i by omega,
        List.getElem?_eq_getElem (show start + i < src.length by omega)]
      have hm : s.mapped[start + i]? = none := List.getElem?_eq_none (by omega)
      unfold aval
      rw [hm]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show start + i < src.length by
        omega)]
    · rw [ite_eq_right (by omega), ite_eq_right hc]

theorem aliasedArgs_spec {c : Config} {s : Aliased} {start count : Nat} (hs : s.OK) :
    aliasedArgs c s start count = .slow ∨
      ∃ src, s.unmapped = some src ∧ start + count ≤ src.length ∧
        aliasedArgs c s start count = .done (holeyArray (aliasedSpec s src start count)) := by
  unfold aliasedArgs
  cases hu : s.unmapped with
  | none => exact Or.inl rfl
  | some src =>
    dsimp only
    by_cases h1 : src.length < start + count
    · rw [ite_eq_left h1]
      exact Or.inl rfl
    rw [ite_eq_right h1]
    by_cases h2 : c.maxFolded < count
    · rw [ite_eq_left h2]
      exact Or.inl rfl
    rw [ite_eq_right h2]
    right
    refine ⟨src, rfl, by omega, ?_⟩
    have hloop : aliasedLoop s src (min s.mapped.length (start + count) - start) start [] =
        some ((List.range (min s.mapped.length (start + count) - start)).map
          fun j => aval s src (start + j)) := by
      by_cases hz : min s.mapped.length (start + count) - start = 0
      · rw [hz]
        simp [aliasedLoop]
      · rw [aliasedLoop_eq hs _ start [] (by omega) (by omega)]
        simp
    rw [hloop]
    dsimp only
    have hrf : min (max s.mapped.length start) (start + count) =
        start + (min s.mapped.length (start + count) - start) := by omega
    have hhl : ((List.range (min s.mapped.length (start + count) - start)).map
        fun j => aval s src (start + j)).length = min s.mapped.length (start + count) - start := by
      simp
    have hpl : ((src.drop (min (max s.mapped.length start) (start + count))).take
        (start + count - min (max s.mapped.length start) (start + count))).length =
        start + count - min (max s.mapped.length start) (start + count) :=
      length_take_drop (by omega)
    rw [hhl, copyElements_eq (by simp; omega) (by omega)]
    dsimp only
    rw [blit_head_piece hhl (by rw [hpl]; omega), hrf,
      show start + count - (start + (min s.mapped.length (start + count) - start)) =
        count - (min s.mapped.length (start + count) - start) by omega,
      aliasedSpec_eq rfl (by omega)]

theorem simpleArgs_spec {c : Config} {e : Option (List (Option Val))} {start count : Nat} :
    simpleArgs c e start count = .slow ∨
      ∃ src, e = some src ∧ start + count ≤ src.length ∧
        simpleArgs c e start count = .done (holeyArray (specSlice src start count)) := by
  unfold simpleArgs
  cases e with
  | none => exact Or.inl rfl
  | some src =>
    dsimp only
    by_cases h1 : src.length < start + count
    · rw [ite_eq_left h1]
      exact Or.inl rfl
    rw [ite_eq_right h1]
    by_cases h2 : c.maxFolded < count
    · rw [ite_eq_left h2]
      exact Or.inl rfl
    rw [ite_eq_right h2]
    right
    refine ⟨src, rfl, by omega, ?_⟩
    rw [copyElements_eq (by simp) (by omega),
      blit_zero_full (by rw [length_take_drop (by omega)]; simp),
      take_drop_eq_specSlice (by omega)]

theorem holeyArray_wf (store : List (Option Val)) : (holeyArray store).WF :=
  ⟨Nat.le_refl _, fun _ _ => rfl, fun _ => rfl, id, nofun, nofun⟩

theorem holeyArray_elems (store : List (Option Val)) : (holeyArray store).elems = store := by
  simp [holeyArray, JSArr.elems]

def StoreBound (c : Config) (a : JSArr) : Prop := a.store.length ≤ c.lim.maxLen

theorem array_spec {c : Config} {a : JSArr} {start count : Nat} (hw : a.WF)
    (hb : StoreBound c a) :
    handleFastSlice c (.array a) start count = .slow ∨
      (start + count ≤ a.length ∧ handleFastSlice c (.array a) start count =
        .done (newArray a.kind (specSlice a.elems start count))) := by
  unfold handleFastSlice
  split
  · exact Or.inl rfl
  dsimp only
  by_cases hf : a.forCopy = false
  · rw [ite_eq_left hf]
    exact Or.inl rfl
  rw [ite_eq_right hf]
  by_cases hl : a.length < start + count
  · rw [ite_eq_left hl]
    exact Or.inl rfl
  rw [ite_eq_right hl]
  have hfast : a.fast = true := hw.forCopy_fast (by simpa using hf)
  have hm : count ≤ c.lim.maxLen := by have := hw.length_le; unfold StoreBound at hb; omega
  right
  refine ⟨by omega, ?_⟩
  rw [extractFast_eq hfast hw.length_le (by omega) hm]
  rfl

theorem newArray_slice_wf {a : JSArr} {start count : Nat} (hw : a.WF) (hfc : a.forCopy = true)
    (h : start + count ≤ a.length) : (newArray a.kind (specSlice a.elems start count)).WF :=
  newArray_wf (hw.forRead_fast (hw.fast_forRead (hw.forCopy_fast hfc)))
    (kindOk_specSlice hw h)

def RecvOK (c : Config) : Recv → Prop
  | .array a => a.WF ∧ StoreBound c a
  | .aliasedArgs s => s.OK
  | _ => True

theorem handleFastSlice_safe {c : Config} {o : Recv} {start count : Nat} (ho : RecvOK c o) :
    handleFastSlice c o start count ≠ .ub ∧ handleFastSlice c o start count ≠ .fatal := by
  cases o with
  | array a =>
    rcases array_spec (start := start) (count := count) ho.1 ho.2 with h | ⟨_, h⟩ <;> rw [h] <;>
      exact ⟨nofun, nofun⟩
  | strictArgs e =>
    unfold handleFastSlice
    split
    · exact ⟨nofun, nofun⟩
    dsimp only
    rcases simpleArgs_spec (c := c) (e := e) (start := start) (count := count) with h | ⟨_, _, _, h⟩ <;>
      rw [h] <;> exact ⟨nofun, nofun⟩
  | sloppyArgs e =>
    unfold handleFastSlice
    split
    · exact ⟨nofun, nofun⟩
    dsimp only
    rcases simpleArgs_spec (c := c) (e := e) (start := start) (count := count) with h | ⟨_, _, _, h⟩ <;>
      rw [h] <;> exact ⟨nofun, nofun⟩
  | aliasedArgs s =>
    unfold handleFastSlice
    split
    · exact ⟨nofun, nofun⟩
    dsimp only
    rcases aliasedArgs_spec (c := c) (start := start) (count := count) ho with h | ⟨_, _, _, h⟩ <;>
      rw [h] <;> exact ⟨nofun, nofun⟩
  | other =>
    unfold handleFastSlice
    split <;> exact ⟨nofun, nofun⟩

theorem clone_path {a a' : JSArr} (hw : a.WF) (hsl : a.SlackHoles) (hfc : a.forCopy = true)
    (h : ofClone (ArrayBuild.cloneFastJSArray false a) = .done a') :
    a'.WF ∧ a'.elems = specSlice a.elems 0 a.length ∧ a'.length = a.length := by
  have hf := hw.forCopy_fast hfc
  cases hc : ArrayBuild.cloneFastJSArray false a with
  | ub =>
    rw [hc] at h
    cases h
  | done b =>
    rw [hc] at h
    cases h
    have hs := ArrayBuild.clone_spec hw hsl (hw.fast_forRead hf) (fun _ => hf) hc
    refine ⟨hs.wf, ?_, hs.length⟩
    rw [hs.elems, specSlice_full (JSArr.elems_length hw)]
    rfl

theorem ofClone_safe {a : JSArr} (hw : a.WF) :
    ofClone (ArrayBuild.cloneFastJSArray false a) ≠ .ub ∧
      ofClone (ArrayBuild.cloneFastJSArray false a) ≠ .fatal := by
  cases h : ArrayBuild.cloneFastJSArray false a with
  | ub => exact absurd h (ArrayBuild.clone_ne_ub hw)
  | done b => exact ⟨nofun, nofun⟩

theorem slice_safe {c : Config} {len : Nat} {receiver : Recv} {start : StartArg}
    {relEnd : Option Int} {o : Recv} (hrecv : RecvOK c receiver) (ho : RecvOK c o) :
    slice c len receiver start relEnd o ≠ .ub ∧ slice c len receiver start relEnd o ≠ .fatal := by
  unfold slice
  split
  · rename_i a
    split
    · exact ofClone_safe hrecv.1
    · exact handleFastSlice_safe ho
  · rename_i a
    split
    · exact ofClone_safe hrecv.1
    · exact handleFastSlice_safe ho
  · exact handleFastSlice_safe ho

end ArraySlice
