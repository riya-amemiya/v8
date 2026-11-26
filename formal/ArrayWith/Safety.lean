import ArrayWith.Model

namespace ArrayWith

open Torque ArrayCopyCommon

theorem kindOk_runtimeKind_value (ud : Bool) {k : Kind} (hk : k.isFast = true) (v : Val) :
    kindOk (runtimeKind ud k v) (some v) = true := by
  cases k <;> simp [Kind.isFast] at hk <;> cases v <;> cases ud <;> rfl

theorem kindOk_runtimeKind_mono (ud : Bool) {k : Kind} (hk : k.isFast = true) (v : Val)
    {x : Option Val} (h : kindOk k x = true) : kindOk (runtimeKind ud k v) x = true := by
  cases k <;> simp [Kind.isFast] at hk <;> cases v <;> cases ud <;> rcases x with _ | w <;>
    simp_all [runtimeKind, Kind.moreGeneral, Kind.isMoreGeneral, Kind.isHoley, Kind.toHoley,
      optimalKind, kindOk, isNumber_of_isSmi]

theorem isFast_runtimeKind (ud : Bool) {k : Kind} (hk : k.isFast = true) (v : Val) :
    (runtimeKind ud k v).isFast = true := by
  cases k <;> simp [Kind.isFast] at hk <;> cases v <;> cases ud <;> rfl

theorem convertRelativeIndex_lt {index : Int} {len idx : Nat}
    (h : convertRelativeIndex index len = some idx) : idx < len := by
  unfold convertRelativeIndex at h
  dsimp only at h
  by_cases h0 : 0 ≤ index
  · rw [ite_eq_left h0] at h
    by_cases h1 : index < 0 ∨ (len : Int) ≤ index
    · rw [ite_eq_left h1] at h
      cases h
    · rw [ite_eq_right h1] at h
      cases h
      omega
  · rw [ite_eq_right h0] at h
    by_cases h1 : (len : Int) + index < 0 ∨ (len : Int) ≤ (len : Int) + index
    · rw [ite_eq_left h1] at h
      cases h
    · rw [ite_eq_right h1] at h
      cases h
      omega

structure Copied (a c : JSArr) (len : Nat) : Prop where
  kind_eq : c.kind = a.kind
  fast : c.fast = true
  cow : c.cow = false
  length_eq : c.length = len
  store_eq : c.store = specSlice a.elems 0 len
  flags : c.forRead = true ∧ c.forCopy = true

theorem extract_copied {lim : Limits} {a : JSArr} (hw : a.WF) (hf : a.fast = true) {len : Nat}
    (hl : len ≤ a.length) (hm : len ≤ lim.maxLen) :
    ∃ c, extractFast lim a 0 len = .done a c ∧ Copied a c len := by
  rw [extractFast_eq hf hw.length_le (by omega) hm]
  exact ⟨_, rfl, rfl, rfl, rfl, by simp [newArray, length_specSlice], rfl, rfl, rfl⟩

theorem specSlice_packed {a : JSArr} (hw : a.WF) (hp : isFastPacked a.kind = true) {len : Nat}
    (hl : len ≤ a.length) :
    specSlice a.elems 0 len = (List.range len).map fun k => some (getOrUndef a.elems k) := by
  have hel := JSArr.elems_length hw
  apply List.ext_getElem?
  intro i
  rw [getElem?_specSlice, List.getElem?_map]
  by_cases hi : i < len
  · rw [ite_eq_left hi, List.getElem?_range hi]
    have hmem : a.elems[i]'(by omega) ∈ a.elems := List.getElem_mem _
    have hne := kindOk_packed_some hp (hw.kind_ok _ hmem)
    obtain ⟨w, hw'⟩ := Option.ne_none_iff_exists'.mp hne
    have hget : a.elems[i]? = some (some w) := by
      rw [List.getElem?_eq_getElem (by omega), hw']
    simp only [Nat.zero_add, Option.map_some, List.getD_eq_getElem?_getD, hget,
      Option.getD_some, getOrUndef_of_some hget]
  · rw [ite_eq_right hi, List.getElem?_eq_none (by simp; omega)]
    rfl

theorem set_spec {a : JSArr} (hw : a.WF) (hp : isFastPacked a.kind = true) {len idx : Nat}
    (hl : len ≤ a.length) (v : Val) :
    (specSlice a.elems 0 len).set idx (some v) = specWith a.elems len idx v := by
  rw [specSlice_packed hw hp hl]
  apply List.ext_getElem?
  intro i
  unfold specWith
  rw [List.getElem?_set, List.getElem?_map, List.getElem?_map]
  simp only [List.length_map, List.length_range]
  by_cases hi : i < len
  · rw [List.getElem?_range hi]
    by_cases he : idx = i
    · subst he
      rw [ite_eq_left rfl, ite_eq_left hi]
      simp
    · rw [ite_eq_right he]
      simp [Ne.symm he]
  · rw [List.getElem?_eq_none (by simp; omega)]
    by_cases he : idx = i
    · rw [ite_eq_left he, ite_eq_right (by omega)]
      rfl
    · rw [ite_eq_right he]
      rfl

theorem mem_set_spec {a : JSArr} (hw : a.WF) {len idx : Nat} (hl : len ≤ a.length) (v : Val)
    {x : Option Val} (hx : x ∈ (specSlice a.elems 0 len).set idx (some v)) :
    x = some v ∨ kindOk a.kind x = true := by
  rcases List.mem_or_eq_of_mem_set hx with hm | rfl
  · exact Or.inr (kindOk_specSlice hw (by omega) x hm)
  · exact Or.inl rfl

theorem ensureWritable_of_cow_false {c : JSArr} (h : c.cow = false) : ensureWritable c = c := by
  unfold ensureWritable
  rw [ite_eq_right (by simp [h])]

structure Created (a res : JSArr) (len idx : Nat) (v : Val) : Prop where
  store_eq : res.store = (specSlice a.elems 0 len).set idx (some v)
  length_eq : res.length = len
  cow : res.cow = false
  flags : res.forRead = true ∧ res.fast = true ∧ res.forCopy = true
  kind_ok : res.kind.isFast = true ∧ kindOk res.kind (some v) = true ∧
    ∀ x, kindOk a.kind x = true → kindOk res.kind x = true

theorem fastCreate_ok {ud : Bool} {a c : JSArr} (hp : isFastPacked a.kind = true)
    {len idx : Nat} (hc : Copied a c len) (hi : idx < len) (v : Val) :
    ∃ res, fastCreate ud c idx v = .done () res ∧ Created a res len idx v := by
  have hfa := isFast_of_isFastPacked hp
  have hslen : c.store.length = len := by rw [hc.store_eq, length_specSlice]
  have hne : c.store ≠ [] := by
    intro h
    rw [h] at hslen
    simp at hslen
    omega
  have hrt : Created a (runtimeCreate ud c idx v) len idx v := {
    store_eq := by simp [runtimeCreate, hc.store_eq]
    length_eq := by simp [runtimeCreate, hc.length_eq]
    cow := rfl
    flags := ⟨hc.flags.1, hc.fast, hc.flags.2⟩
    kind_ok := by
      refine ⟨?_, ?_, ?_⟩
      · simp only [runtimeCreate, hc.kind_eq]
        exact isFast_runtimeKind ud hfa v
      · simp only [runtimeCreate, hc.kind_eq]
        exact kindOk_runtimeKind_value ud hfa v
      · intro x hx
        simp only [runtimeCreate, hc.kind_eq]
        exact kindOk_runtimeKind_mono ud hfa v hx }
  have hst : ∀ (hv : kindOk a.kind (some v) = true), ∃ res, storeInto c idx v = .done () res ∧
      Created a res len idx v := by
    intro hv
    refine ⟨{ c with store := c.store.set idx (some v) }, ?_, ?_⟩
    · unfold storeInto
      rw [storeChecked_eq (by omega)]
    · exact {
        store_eq := by simp [hc.store_eq]
        length_eq := hc.length_eq
        cow := hc.cow
        flags := ⟨hc.flags.1, hc.fast, hc.flags.2⟩
        kind_ok := ⟨by rw [hc.kind_eq]; exact hfa, by rw [hc.kind_eq]; exact hv,
          fun x hx => by rw [hc.kind_eq]; exact hx⟩ }
  unfold fastCreate
  rw [ite_eq_right (by simp [hc.fast, hc.length_eq]; omega)]
  simp only [ensureWritable_of_cow_false hc.cow]
  cases hk : a.kind with
  | packedSmi =>
    rw [hc.kind_eq, hk]
    simp only
    by_cases hv : v.isSmi = true
    · rw [ite_eq_left hv]
      exact hst (by rw [hk]; simp [kindOk, hv])
    · rw [ite_eq_right hv]
      exact ⟨_, rfl, hrt⟩
  | packedDouble =>
    rw [hc.kind_eq, hk]
    simp only
    rw [ite_eq_right (fun h => hne h.2)]
    by_cases hv : v.isNumber = true
    · rw [ite_eq_left hv, ite_eq_right hne]
      exact hst (by rw [hk]; simp [kindOk, hv])
    · rw [ite_eq_right hv]
      exact ⟨_, rfl, hrt⟩
  | packedElem =>
    rw [hc.kind_eq, hk]
    exact hst (by rw [hk]; rfl)
  | holeySmi => rw [hk] at hp; cases hp
  | holeyDouble => rw [hk] at hp; cases hp
  | holeyElem => rw [hk] at hp; cases hp
  | slow => rw [hk] at hp; cases hp

theorem tryFast_cases {r : SmiRepr} {lim : Limits} {ud : Bool} {len idx : Nat} {v : Val} {a : JSArr}
    (hw : a.WF) (hcap : a.store.length ≤ lim.maxLen) (hi : idx < len) :
    tryFast r lim ud len idx v a = .slow ∨
      (isFastPacked a.kind = true ∧ len ≤ a.length ∧
        ∃ res, tryFast r lim ud len idx v a = .done a res ∧ Created a res len idx v) := by
  unfold tryFast
  by_cases h1 : a.fast = false
  · rw [ite_eq_left h1]; exact Or.inl rfl
  rw [ite_eq_right h1]
  by_cases h2 : isFastPacked a.kind = false
  · rw [ite_eq_left h2]; exact Or.inl rfl
  rw [ite_eq_right h2]
  by_cases h3 : r.max < len
  · rw [ite_eq_left h3]; exact Or.inl rfl
  rw [ite_eq_right h3]
  by_cases h4 : a.length < len
  · rw [ite_eq_left h4]; exact Or.inl rfl
  rw [ite_eq_right h4]
  have hf : a.fast = true := by simpa using h1
  have hp : isFastPacked a.kind = true := by simpa using h2
  obtain ⟨c, hex, hc⟩ := extract_copied (lim := lim) hw hf (len := len) (by omega)
    (by have := hw.length_le; omega)
  rw [hex]
  simp only
  obtain ⟨res, hres, hcr⟩ := fastCreate_ok (ud := ud) hp hc hi v
  rw [hres]
  exact Or.inr ⟨hp, by omega, res, rfl, hcr⟩

theorem created_elems {a res : JSArr} {len idx : Nat} {v : Val} (hc : Created a res len idx v) :
    res.store.length = len ∧ res.elems = (specSlice a.elems 0 len).set idx (some v) := by
  have hslen : res.store.length = len := by
    rw [hc.store_eq, List.length_set, length_specSlice]
  refine ⟨hslen, ?_⟩
  have : res.elems = res.store := by
    unfold JSArr.elems
    rw [hc.length_eq]
    exact List.take_of_length_le (by omega)
  rw [this, hc.store_eq]

theorem created_wf {a res : JSArr} (hw : a.WF) {len idx : Nat} {v : Val} (hl : len ≤ a.length)
    (hc : Created a res len idx v) : res.WF ∧ res.SlackHoles := by
  obtain ⟨hslen, helems⟩ := created_elems hc
  have hlen := hc.length_eq
  refine ⟨⟨by omega, ?_, fun _ => hc.kind_ok.1, fun _ => hc.flags.1, fun _ => hc.flags.2.1,
    by rw [hc.cow]; nofun⟩, ?_⟩
  · intro x hx
    rw [helems] at hx
    rcases mem_set_spec hw hl v hx with rfl | hk
    · exact hc.kind_ok.2.1
    · exact hc.kind_ok.2.2 x hk
  · intro x hx
    rw [List.drop_of_length_le (by omega)] at hx
    cases hx

theorem tryFast_ne_ub {r : SmiRepr} {lim : Limits} {ud : Bool} {len idx : Nat} {v : Val} {a : JSArr}
    (hw : a.WF) (hcap : a.store.length ≤ lim.maxLen) (hi : idx < len) :
    tryFast r lim ud len idx v a ≠ .ub := by
  rcases tryFast_cases (r := r) (ud := ud) (v := v) hw hcap hi with h | ⟨_, _, res, h, _⟩ <;>
    rw [h] <;> nofun

theorem tryFast_ne_abort {r : SmiRepr} {lim : Limits} {ud : Bool} {len idx : Nat} {v : Val}
    {a : JSArr} (hw : a.WF) (hcap : a.store.length ≤ lim.maxLen) (hi : idx < len) :
    tryFast r lim ud len idx v a ≠ .abort := by
  rcases tryFast_cases (r := r) (ud := ud) (v := v) hw hcap hi with h | ⟨_, _, res, h, _⟩ <;>
    rw [h] <;> nofun

theorem tryFast_done {r : SmiRepr} {lim : Limits} {ud : Bool} {len idx : Nat} {v : Val}
    {a src res : JSArr} (hw : a.WF) (hcap : a.store.length ≤ lim.maxLen) (hi : idx < len)
    (h : tryFast r lim ud len idx v a = .done src res) :
    src = a ∧ res.WF ∧ res.SlackHoles ∧ res.cow = false ∧ res.length = len ∧
      res.elems = specWith a.elems len idx v := by
  rcases tryFast_cases (r := r) (ud := ud) (v := v) hw hcap hi with h' | ⟨hp, hl, res', h', hc⟩ <;>
    rw [h'] at h
  · cases h
  · cases h
    obtain ⟨hwf, hsl⟩ := created_wf hw hl hc
    refine ⟨rfl, hwf, hsl, hc.cow, hc.length_eq, ?_⟩
    rw [(created_elems hc).2, set_spec hw hp hl]

theorem fastPath_ne_ub {r : SmiRepr} {lim : Limits} {ud : Bool} {len : Nat} {index : Int} {v : Val}
    {a : JSArr} (hw : a.WF) (hcap : a.store.length ≤ lim.maxLen) :
    fastPath r lim ud len index v a ≠ .ub := by
  unfold fastPath
  split
  · nofun
  · rename_i idx h
    exact tryFast_ne_ub hw hcap (convertRelativeIndex_lt h)

theorem fastPath_ne_abort {r : SmiRepr} {lim : Limits} {ud : Bool} {len : Nat} {index : Int}
    {v : Val} {a : JSArr} (hw : a.WF) (hcap : a.store.length ≤ lim.maxLen) :
    fastPath r lim ud len index v a ≠ .abort := by
  unfold fastPath
  split
  · nofun
  · rename_i idx h
    exact tryFast_ne_abort hw hcap (convertRelativeIndex_lt h)

theorem fastPath_done {r : SmiRepr} {lim : Limits} {ud : Bool} {len : Nat} {index : Int} {v : Val}
    {a src res : JSArr} (hw : a.WF) (hcap : a.store.length ≤ lim.maxLen)
    (h : fastPath r lim ud len index v a = .done src res) :
    ∃ idx, convertRelativeIndex index len = some idx ∧ idx < len ∧ src = a ∧ res.WF ∧
      res.SlackHoles ∧ res.cow = false ∧ res.length = len ∧
      res.elems = specWith a.elems len idx v := by
  unfold fastPath at h
  split at h
  · cases h
  · rename_i idx hidx
    have hi := convertRelativeIndex_lt hidx
    exact ⟨idx, hidx, hi, tryFast_done hw hcap hi h⟩

end ArrayWith
