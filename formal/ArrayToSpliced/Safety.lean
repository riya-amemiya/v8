import ArrayToSpliced.Model

namespace ArrayToSpliced

open Torque ArrayCopyCommon

theorem relIndex_le (len : Nat) (rel : Int) : relIndex len rel ≤ len := by
  unfold relIndex
  split
  · split
    · exact Nat.zero_le _
    · omega
  · exact Nat.min_le_right _ _

theorem actualStart_le (len : Nat) (args : Args) : actualStart len args ≤ len := by
  cases args <;> exact relIndex_le _ _

theorem actualDeleteCount_le (len : Nat) (args : Args) :
    actualDeleteCount len args ≤ len - actualStart len args := by
  unfold actualDeleteCount
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _
  · exact Nat.min_le_right _ _

theorem step1 {src : List (Option Val)} {nl st : Nat} (hs : st ≤ src.length) (hn : st ≤ nl) :
    ∃ b1, (if 0 < st then copyElements (List.replicate nl none) 0 src 0 st
      else some (List.replicate nl none)) = some b1 ∧ b1.length = nl ∧
      ∀ j, b1[j]? = if j < nl then (if j < st then src[j]? else some none) else none := by
  by_cases h0 : 0 < st
  · rw [ite_eq_left h0, copyElements_eq (by simp; omega) (by omega)]
    refine ⟨_, rfl, ?_, ?_⟩
    · rw [length_blit (by rw [length_take_drop (by omega)]; simp; omega)]
      simp
    · intro j
      rw [getElem?_blit (by rw [length_take_drop (by omega)]; simp; omega),
        length_take_drop (by omega), List.getElem?_replicate]
      by_cases h1 : j < st
      · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
          ite_eq_left h1, List.getElem?_take, ite_eq_left (by omega), List.getElem?_drop]
        congr 1
        omega
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h1]
  · rw [ite_eq_right h0]
    refine ⟨_, rfl, by simp, ?_⟩
    intro j
    rw [List.getElem?_replicate, ite_eq_right (show ¬j < st by omega)]

theorem step2 {b1 src : List (Option Val)} {nl st ins : Nat} (hl : b1.length = nl)
    (hn : st + ins ≤ nl)
    (hb : ∀ j, b1[j]? = if j < nl then (if j < st then src[j]? else some none) else none) :
    ∃ b2, (if 0 < ins then fillZero b1 st ins else some b1) = some b2 ∧ b2.length = nl ∧
      ∀ j, b2[j]? = if j < nl then (if j < st then src[j]? else if j < st + ins then
        some (some (.smi 0)) else some none) else none := by
  by_cases h0 : 0 < ins
  · rw [ite_eq_left h0]
    unfold fillZero
    rw [ite_eq_left (by omega)]
    refine ⟨_, rfl, ?_, ?_⟩
    · rw [length_blit (by simp; omega), hl]
    · intro j
      rw [getElem?_blit (by simp; omega), List.length_replicate, List.getElem?_replicate]
      simp only [hb]
      repeat' split
      all_goals first | rfl | omega
  · rw [ite_eq_right h0]
    refine ⟨_, rfl, hl, ?_⟩
    intro j
    simp only [hb]
    repeat' split
    all_goals first | rfl | omega

def spliceAt (src : List (Option Val)) (nl st ins dc j : Nat) : Option (Option Val) :=
  if j < nl then (if j < st then src[j]? else if j < st + ins then some (some (.smi 0))
    else src[st + dc + (j - (st + ins))]?) else none

theorem step3 {b2 src : List (Option Val)} {nl st ins dc : Nat} (hl : b2.length = nl)
    (hn : st + ins ≤ nl) (hs : st + dc + (nl - (st + ins)) ≤ src.length)
    (hb : ∀ j, b2[j]? = if j < nl then (if j < st then src[j]? else if j < st + ins then
      some (some (.smi 0)) else some none) else none) :
    ∃ b3, (if 0 < nl - (st + ins) then
        copyElements b2 (st + ins) src (st + dc) (nl - (st + ins)) else some b2) = some b3 ∧
      b3.length = nl ∧ ∀ j, b3[j]? = spliceAt src nl st ins dc j := by
  by_cases h0 : 0 < nl - (st + ins)
  · rw [ite_eq_left h0, copyElements_eq (by omega) hs]
    refine ⟨_, rfl, ?_, ?_⟩
    · rw [length_blit (by rw [length_take_drop hs]; omega), hl]
    · intro j
      unfold spliceAt
      rw [getElem?_blit (by rw [length_take_drop hs]; omega), length_take_drop hs]
      simp only [hb, List.getElem?_take, List.getElem?_drop]
      repeat' split
      all_goals first | rfl | omega
  · rw [ite_eq_right h0]
    refine ⟨_, rfl, hl, ?_⟩
    intro j
    unfold spliceAt
    simp only [hb]
    repeat' split
    all_goals first | rfl | omega

theorem src_some {a : JSArr} (hw : a.WF) (hp : isFastPacked a.kind = true) {j : Nat}
    (hj : j < a.length) : ∃ w, a.store[j]? = some (some w) ∧ a.elems[j]? = some (some w) := by
  have hl := hw.length_le
  have hel := JSArr.elems_length hw
  have hmem : a.elems[j]'(by omega) ∈ a.elems := List.getElem_mem _
  obtain ⟨w, hw'⟩ := Option.ne_none_iff_exists'.mp (kindOk_packed_some hp (hw.kind_ok _ hmem))
  have he : a.elems[j]? = some (some w) := by rw [List.getElem?_eq_getElem (by omega), hw']
  refine ⟨w, ?_, he⟩
  have : a.elems[j]? = a.store[j]? := by
    simp only [JSArr.elems, List.getElem?_take]
    rw [ite_eq_left hj]
  rw [← this, he]

theorem copy_ok {lim : Limits} {a : JSArr} (hw : a.WF) (hp : isFastPacked a.kind = true)
    {len nl st ins dc : Nat} (hlen : len ≤ a.length) (hst : st + dc ≤ len)
    (hnl : nl = len + ins - dc) (hm : nl ≤ lim.maxLen) :
    ∃ b3, copyForToSpliced lim a.store nl st ins dc = .ok b3 ∧ b3.length = nl ∧
      ∀ j, b3[j]? = spliceAt a.store nl st ins dc j := by
  have hl := hw.length_le
  unfold copyForToSpliced
  rw [ite_eq_right (by omega)]
  obtain ⟨b1, h1, hl1, hb1⟩ := step1 (src := a.store) (nl := nl) (st := st) (by omega) (by omega)
  rw [h1]
  simp only
  obtain ⟨b2, h2, hl2, hb2⟩ := step2 (ins := ins) hl1 (by omega) hb1
  rw [h2]
  simp only
  obtain ⟨b3, h3, hl3, hb3⟩ := step3 (dc := dc) hl2 (by omega) (by omega) hb2
  rw [h3]
  simp only
  have hnone : none ∉ b3 := by
    intro hmem
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
    rw [hb3] at hj
    unfold spliceAt at hj
    split at hj
    · split at hj
      · obtain ⟨w, hw', _⟩ := src_some hw hp (j := j) (by omega)
        rw [hw'] at hj
        cases hj
      · split at hj
        · cases hj
        · obtain ⟨w, hw', _⟩ := src_some hw hp (j := st + dc + (j - (st + ins))) (by omega)
          rw [hw'] at hj
          cases hj
    · cases hj
  rw [ite_eq_right hnone]
  exact ⟨b3, rfl, hl3, hb3⟩

theorem none_not_mem_buf {a : JSArr} (hw : a.WF) (hp : isFastPacked a.kind = true)
    {b : List (Option Val)} {nl st ins dc len : Nat} (hlen : len ≤ a.length) (hst : st + dc ≤ len)
    (hnl : nl = len + ins - dc) (hb : ∀ j, b[j]? = spliceAt a.store nl st ins dc j)
    {x : Option Val} (hx : x ∈ b) :
    (∃ j, j < len ∧ a.elems[j]? = some x) ∨ x = some (.smi 0) := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
  rw [hb] at hj
  unfold spliceAt at hj
  split at hj
  · split at hj
    · obtain ⟨w, hw1, hw2⟩ := src_some hw hp (j := j) (by omega)
      rw [hw1] at hj
      cases hj
      exact Or.inl ⟨j, by omega, hw2⟩
    · split at hj
      · cases hj
        exact Or.inr rfl
      · obtain ⟨w, hw1, hw2⟩ := src_some hw hp (j := st + dc + (j - (st + ins))) (by omega)
        rw [hw1] at hj
        cases hj
        exact Or.inl ⟨_, by omega, hw2⟩
  · cases hj

theorem blit_set {buf l : List (Option Val)} {k : Nat} {x : Option Val} (hk : k < buf.length) :
    blit (buf.set k x) (k + 1) l = blit buf k (x :: l) := by
  unfold blit
  have h1 : (buf.set k x).take (k + 1) = buf.take k ++ [x] := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take, List.getElem?_set, List.getElem?_append]
    simp only [List.length_take]
    rw [Nat.min_eq_left (by omega)]
    by_cases h : j < k
    · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left h, List.getElem?_take,
        ite_eq_left h]
    · by_cases h' : j = k
      · subst h'
        rw [ite_eq_left (by omega), ite_eq_left rfl, ite_eq_left hk, ite_eq_right h]
        simp
      · rw [ite_eq_right (by omega), ite_eq_right h, List.getElem?_eq_none (by simp; omega)]
  have h2 : (buf.set k x).drop (k + 1 + l.length) = buf.drop (k + (x :: l).length) := by
    simp only [List.length_cons]
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_drop, List.getElem?_drop, List.getElem?_set_ne (by omega)]
    congr 1
    omega
  rw [h1, h2]
  simp

theorem insertLoop_ok {dbl : Bool} :
    ∀ (es : List Val) (buf : List (Option Val)) (k : Nat), k + es.length ≤ buf.length →
      (dbl = true → ∀ e ∈ es, e.isNumber = true) →
      insertLoop dbl buf k es = .ok (blit buf k (es.map some))
  | [], buf, k, _, _ => by
    rw [insertLoop]
    simp [blit]
  | e :: es, buf, k, hk, hn => by
    rw [insertLoop]
    have hnum : ¬(dbl = true ∧ e.isNumber = false) := by
      intro ⟨hd, he⟩
      rw [hn hd e (by simp)] at he
      cases he
    simp only [List.length_cons] at hk
    rw [ite_eq_right hnum, storeChecked_eq (by omega)]
    simp only
    rw [insertLoop_ok es (buf.set k (some e)) (k + 1) (by simp; omega)
      (fun hd e' he' => hn hd e' (by simp [he'])), blit_set (by omega)]
    rfl

theorem insertLoop_ne_abort {dbl : Bool} :
    ∀ (es : List Val) (buf : List (Option Val)) (k : Nat), k + es.length ≤ buf.length →
      insertLoop dbl buf k es ≠ .abort
  | [], buf, k, _ => by
    rw [insertLoop]
    nofun
  | e :: es, buf, k, hk => by
    rw [insertLoop]
    simp only [List.length_cons] at hk
    split
    · nofun
    · rw [storeChecked_eq (by omega)]
      exact insertLoop_ne_abort es _ (k + 1) (by simp; omega)

def stepKind (k : Kind) (e : Val) : Kind :=
  if isSmiKind k then
    (if e.isSmi then k else if isHeapNumber e then allowDouble k else allowNonNumber k)
  else if k.isDouble then (if e.isNumber then k else allowNonNumber k) else k

theorem insertKind_const {k : Kind} (h1 : isSmiKind k = false) (h2 : k.isDouble = false) :
    ∀ es, insertKind k es = k
  | [] => rfl
  | _ :: _ => by
    rw [insertKind, ite_eq_right (by simp [h1]), ite_eq_right (by simp [h2])]

theorem insertKind_cons (k : Kind) (e : Val) (es : List Val) :
    insertKind k (e :: es) = insertKind (stepKind k e) es := by
  rw [insertKind]
  unfold stepKind
  by_cases h1 : isSmiKind k = true
  · rw [ite_eq_left h1, ite_eq_left h1]
    by_cases h2 : e.isSmi = true
    · rw [ite_eq_left h2, ite_eq_left h2]
    · rw [ite_eq_right h2, ite_eq_right h2]
      split <;> rfl
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : k.isDouble = true
    · rw [ite_eq_left h2, ite_eq_left h2]
      split <;> rfl
    · rw [ite_eq_right h2, ite_eq_right h2,
        insertKind_const (by simpa using h1) (by simpa using h2)]

theorem stepKind_packed {k : Kind} (hk : isFastPacked k = true) (e : Val) :
    isFastPacked (stepKind k e) = true := by
  cases k <;> simp [isFastPacked] at hk <;> cases e <;> rfl

theorem stepKind_value {k : Kind} (hk : isFastPacked k = true) (e : Val) :
    kindOk (stepKind k e) (some e) = true := by
  cases k <;> simp [isFastPacked] at hk <;> cases e <;> rfl

theorem stepKind_mono {k : Kind} (hk : isFastPacked k = true) (e : Val) {x : Option Val}
    (hx : kindOk k x = true) : kindOk (stepKind k e) x = true := by
  cases k <;> simp [isFastPacked] at hk <;> cases e <;> rcases x with _ | w <;>
    (try cases w) <;>
    simp_all [stepKind, isSmiKind, isHeapNumber, allowDouble, allowNonNumber, Kind.isDouble,
      Val.isSmi, Val.isNumber, kindOk]

theorem insertKind_packed : ∀ {k : Kind} (es : List Val), isFastPacked k = true →
    isFastPacked (insertKind k es) = true
  | _, [], hk => hk
  | k, e :: es, hk => by
    rw [insertKind_cons]
    exact insertKind_packed es (stepKind_packed hk e)

theorem insertKind_mono : ∀ {k : Kind} (es : List Val), isFastPacked k = true →
    ∀ {x : Option Val}, kindOk k x = true → kindOk (insertKind k es) x = true
  | _, [], _, _, hx => hx
  | k, e :: es, hk, x, hx => by
    rw [insertKind_cons]
    exact insertKind_mono es (stepKind_packed hk e) (stepKind_mono hk e hx)

theorem insertKind_items : ∀ {k : Kind} (es : List Val), isFastPacked k = true →
    ∀ e ∈ es, kindOk (insertKind k es) (some e) = true
  | _, [], _, _, he => by cases he
  | k, e :: es, hk, e', he' => by
    rw [insertKind_cons]
    rcases List.mem_cons.mp he' with rfl | hm
    · exact insertKind_mono es (stepKind_packed hk _) (stepKind_value hk _)
    · exact insertKind_items es (stepKind_packed hk e) e' hm

theorem insertKind_double {k : Kind} (es : List Val) (hk : isFastPacked k = true)
    (hd : (insertKind k es).isDouble = true) : ∀ e ∈ es, e.isNumber = true := by
  intro e he
  have h1 := insertKind_items es hk e he
  have h2 := insertKind_packed es hk
  generalize insertKind k es = k' at h1 h2 hd
  cases k' <;> simp_all [isFastPacked, Kind.isDouble, kindOk]

theorem getElem?_specSpliced (xs : List (Option Val)) (len st dc : Nat) (its : List Val)
    (j : Nat) :
    (specSpliced xs len st dc its)[j]? =
      if j < st then some (some (getOrUndef xs j))
      else if j < st + its.length then (its[j - st]?).map some
      else if j < st + its.length + (len - st - dc) then
        some (some (getOrUndef xs (st + dc + (j - (st + its.length)))))
      else none := by
  unfold specSpliced
  rw [List.append_assoc, List.getElem?_append, List.getElem?_append]
  simp only [List.length_map, List.length_range, List.getElem?_map]
  by_cases h1 : j < st
  · rw [ite_eq_left h1, ite_eq_left h1, List.getElem?_range h1]
    rfl
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : j - st < its.length
    · rw [ite_eq_left h2, ite_eq_left (by omega)]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]
      by_cases h3 : j - st - its.length < len - st - dc
      · rw [List.getElem?_range h3, ite_eq_left (by omega), Nat.sub_sub]
        rfl
      · rw [List.getElem?_eq_none (by simp; omega), ite_eq_right (by omega)]
        rfl

theorem length_specSpliced (xs : List (Option Val)) (len st dc : Nat) (its : List Val) :
    (specSpliced xs len st dc its).length = st + its.length + (len - st - dc) := by
  simp [specSpliced]
  omega

theorem final_getElem? {src b3 : List (Option Val)} {nl st dc : Nat} {its : List Val}
    (hl : b3.length = nl) (hn : st + its.length ≤ nl)
    (hb : ∀ j, b3[j]? = spliceAt src nl st its.length dc j) (j : Nat) :
    (blit b3 st (its.map some))[j]? =
      if j < st then src[j]? else if j < st + its.length then (its[j - st]?).map some
      else if j < nl then src[st + dc + (j - (st + its.length))]? else none := by
  rw [getElem?_blit (by simp; omega), List.length_map, List.getElem?_map]
  simp only [hb]
  unfold spliceAt
  repeat' split
  all_goals first | rfl | omega

theorem final_eq_spec {a : JSArr} (hw : a.WF) (hp : isFastPacked a.kind = true)
    {b3 : List (Option Val)} {len nl st dc : Nat} {its : List Val} (hlen : len ≤ a.length)
    (hst : st + dc ≤ len) (hnl : nl = len + its.length - dc) (hl : b3.length = nl)
    (hb : ∀ j, b3[j]? = spliceAt a.store nl st its.length dc j) :
    blit b3 st (its.map some) = specSpliced a.elems len st dc its := by
  apply List.ext_getElem?
  intro j
  rw [final_getElem? hl (by omega) hb, getElem?_specSpliced]
  by_cases h1 : j < st
  · rw [ite_eq_left h1, ite_eq_left h1]
    obtain ⟨w, h1', h2'⟩ := src_some hw hp (j := j) (by omega)
    rw [h1', getOrUndef_of_some h2']
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : j < st + its.length
    · rw [ite_eq_left h2, ite_eq_left h2]
    · rw [ite_eq_right h2, ite_eq_right h2]
      by_cases h3 : j < nl
      · rw [ite_eq_left h3, ite_eq_left (by omega)]
        obtain ⟨w, h1', h2'⟩ := src_some hw hp (j := st + dc + (j - (st + its.length))) (by omega)
        rw [h1', getOrUndef_of_some h2']
      · rw [ite_eq_right h3, ite_eq_right (by omega)]

theorem mem_final {a : JSArr} (hw : a.WF) (hp : isFastPacked a.kind = true)
    {b3 : List (Option Val)} {len nl st dc : Nat} {its : List Val} (hlen : len ≤ a.length)
    (hst : st + dc ≤ len) (hnl : nl = len + its.length - dc) (hl : b3.length = nl)
    (hb : ∀ j, b3[j]? = spliceAt a.store nl st its.length dc j) {x : Option Val}
    (hx : x ∈ blit b3 st (its.map some)) : kindOk a.kind x = true ∨ ∃ e ∈ its, x = some e := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
  rw [final_getElem? hl (by omega) hb] at hj
  have hel : ∀ i, i < len → a.store[i]? = some x → kindOk a.kind x = true := by
    intro i hi hs
    obtain ⟨w, h1', h2'⟩ := src_some hw hp (j := i) (by omega)
    rw [h1'] at hs
    cases hs
    exact hw.kind_ok _ (List.mem_iff_getElem?.mpr ⟨i, h2'⟩)
  split at hj
  · exact Or.inl (hel j (by omega) hj)
  · split at hj
    · obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hj
      exact Or.inr ⟨e, List.mem_iff_getElem?.mpr ⟨_, he⟩, rfl⟩
    · split at hj
      · exact Or.inl (hel _ (by omega) hj)
      · cases hj

theorem transitionCopy_eq {lim : Limits} {c : JSArr} (hm : c.store.length ≤ lim.maxLen) (k : Kind) :
    transitionCopy lim c k = some { c with kind := k } := by
  unfold transitionCopy
  by_cases h : k = c.kind
  · rw [ite_eq_left h, h]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

structure Spliced (a res : JSArr) (len nl st dc : Nat) (its : List Val) : Prop where
  kind_eq : res.kind = insertKind a.kind its
  flags : res.forRead = true ∧ res.fast = true ∧ res.forCopy = true
  cow : res.cow = false
  length_eq : res.length = nl
  store_len : res.store.length = nl
  elems_eq : res.elems = specSpliced a.elems len st dc its
  kind_ok : ∀ x ∈ res.store, kindOk a.kind x = true ∨ ∃ e ∈ its, x = some e

theorem tryFast_cases {r : SmiRepr} {lim : Limits} {len nl st dc : Nat} {its : List Val}
    {a : JSArr} (hw : a.WF) (hst : st + dc ≤ len) (hnl : nl = len + its.length - dc)
    (hm : nl ≤ lim.maxLen) :
    tryFast r lim len nl st dc its a = .slow ∨
      (isFastPacked a.kind = true ∧ ∃ res, tryFast r lim len nl st dc its a = .done a res ∧
        Spliced a res len nl st dc its) := by
  unfold tryFast
  by_cases h1 : r.max < nl ∨ r.max < st ∨ r.max < dc
  · rw [ite_eq_left h1]; exact Or.inl rfl
  rw [ite_eq_right h1]
  by_cases h2 : a.fast = false
  · rw [ite_eq_left h2]; exact Or.inl rfl
  rw [ite_eq_right h2]
  by_cases h3 : r.max < len
  · rw [ite_eq_left h3]; exact Or.inl rfl
  rw [ite_eq_right h3]
  by_cases h4 : a.length < len
  · rw [ite_eq_left h4]; exact Or.inl rfl
  rw [ite_eq_right h4]
  by_cases h5 : isFastPacked a.kind = false
  · rw [ite_eq_left h5]; exact Or.inl rfl
  rw [ite_eq_right h5]
  have hp : isFastPacked a.kind = true := by simpa using h5
  obtain ⟨b3, hc, hl3, hb3⟩ := copy_ok (lim := lim) (ins := its.length) hw hp (len := len)
    (by omega) hst hnl hm
  rw [hc]
  simp only
  rw [transitionCopy_eq (by simp [newArray, hl3]; omega)]
  simp only
  have hins := insertLoop_ok (dbl := (insertKind a.kind its).isDouble) its b3 st
    (by simp [hl3]; omega) (fun hd => insertKind_double its hp hd)
  simp only [newArray] at hins ⊢
  rw [hins]
  simp only
  refine Or.inr ⟨hp, _, rfl, ?_⟩
  have hfl : (blit b3 st (its.map some)).length = nl := by
    rw [length_blit (by simp; omega), hl3]
  exact {
    kind_eq := rfl
    flags := ⟨rfl, rfl, rfl⟩
    cow := rfl
    length_eq := hl3
    store_len := hfl
    elems_eq := by
      simp only [JSArr.elems, hl3]
      rw [List.take_of_length_le (by omega)]
      exact final_eq_spec hw hp (by omega) hst hnl hl3 hb3
    kind_ok := fun x hx => mem_final hw hp (by omega) hst hnl hl3 hb3 hx }

theorem spliced_wf {a res : JSArr} (hp : isFastPacked a.kind = true)
    {len nl st dc : Nat} {its : List Val} (hs : Spliced a res len nl st dc its) :
    res.WF ∧ res.SlackHoles ∧ isFastPacked res.kind = true := by
  have hk := hs.kind_eq
  have hpk : isFastPacked res.kind = true := by rw [hk]; exact insertKind_packed its hp
  have hl := hs.length_eq
  have hsl := hs.store_len
  refine ⟨⟨by omega, ?_, fun _ => isFast_of_isFastPacked hpk, fun _ => hs.flags.1,
    fun _ => hs.flags.2.1, by rw [hs.cow]; nofun⟩, ?_, hpk⟩
  · intro x hx
    have hx' : x ∈ res.store := List.mem_of_mem_take hx
    rw [hk]
    rcases hs.kind_ok x hx' with h | ⟨e, he, rfl⟩
    · exact insertKind_mono its hp h
    · exact insertKind_items its hp e he
  · intro x hx
    rw [List.drop_of_length_le (by omega)] at hx
    cases hx

theorem fastPath_cases {r : SmiRepr} {lim : Limits} {len : Nat} {args : Args} {a : JSArr}
    (hw : a.WF) (hfm : lim.maxFast ≤ lim.maxLen) :
    fastPath r lim len args a = .throws ∨ fastPath r lim len args a = .slow ∨
      (newLen len args = 0 ∧ fastPath r lim len args a = .done a (newArray .packedSmi [])) ∨
      (isFastPacked a.kind = true ∧ ∃ res, fastPath r lim len args a = .done a res ∧
        Spliced a res len (newLen len args) (actualStart len args) (actualDeleteCount len args)
          (items args)) := by
  have hs := actualStart_le len args
  have hd := actualDeleteCount_le len args
  unfold fastPath
  by_cases h1 : 2 ^ 53 - 1 < newLen len args
  · rw [ite_eq_left h1]; exact Or.inl rfl
  rw [ite_eq_right h1]
  by_cases h2 : newLen len args = 0
  · rw [ite_eq_left h2]; exact Or.inr (Or.inr (Or.inl ⟨h2, rfl⟩))
  rw [ite_eq_right h2]
  by_cases h3 : lim.maxFast < newLen len args
  · rw [ite_eq_left h3]; exact Or.inr (Or.inl rfl)
  rw [ite_eq_right h3]
  rcases tryFast_cases (r := r) (lim := lim) (len := len) (nl := newLen len args)
    (st := actualStart len args) (dc := actualDeleteCount len args) (its := items args) hw
    (by omega) rfl (by omega) with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

theorem fastPath_ne_ub {r : SmiRepr} {lim : Limits} {len : Nat} {args : Args} {a : JSArr}
    (hw : a.WF) (hfm : lim.maxFast ≤ lim.maxLen) : fastPath r lim len args a ≠ .ub := by
  rcases fastPath_cases (r := r) (args := args) hw hfm with h | h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;>
    rw [h] <;> nofun

theorem fastPath_ne_abort {r : SmiRepr} {lim : Limits} {len : Nat} {args : Args} {a : JSArr}
    (hw : a.WF) (hfm : lim.maxFast ≤ lim.maxLen) : fastPath r lim len args a ≠ .abort := by
  rcases fastPath_cases (r := r) (args := args) hw hfm with h | h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;>
    rw [h] <;> nofun

theorem fastPath_done {r : SmiRepr} {lim : Limits} {len : Nat} {args : Args} {a src res : JSArr}
    (hw : a.WF) (hfm : lim.maxFast ≤ lim.maxLen) (h : fastPath r lim len args a = .done src res) :
    src = a ∧ res.WF ∧ res.SlackHoles ∧ res.cow = false ∧ isFastPacked res.kind = true ∧
      res.length = newLen len args ∧
      res.elems = specSpliced a.elems len (actualStart len args) (actualDeleteCount len args)
        (items args) := by
  have hs := actualStart_le len args
  have hd := actualDeleteCount_le len args
  rcases fastPath_cases (r := r) (args := args) hw hfm with h' | h' | ⟨h0, h'⟩ | ⟨hp, res', h', hsp⟩ <;>
    rw [h'] at h
  · cases h
  · cases h
  · cases h
    unfold newLen at h0
    have hst : actualStart len args = 0 := by omega
    have hit : (items args).length = 0 := by omega
    refine ⟨rfl, newArray_wf rfl (by simp), newArray_slack _ _, rfl, rfl, by simp [newArray, newLen]; omega, ?_⟩
    rw [newArray_elems]
    exact (List.eq_nil_of_length_eq_zero (by rw [length_specSpliced]; omega)).symm
  · cases h
    obtain ⟨hwf, hsl, hpk⟩ := spliced_wf hp hsp
    exact ⟨rfl, hwf, hsl, hsp.cow, hpk, hsp.length_eq, hsp.elems_eq⟩

end ArrayToSpliced
