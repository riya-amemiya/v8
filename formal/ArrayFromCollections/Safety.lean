import ArrayFromCollections.Model

namespace ArrayFromCollections

open Torque

def wr (g : Val × Val → Val) (e : Entry) : Option Val := e.spec.map g

def remaining (g : Val × Val → Val) (t : Table) (i : Nat) : List Val :=
  ((t.data.take t.used).drop i).filterMap (wr g)

def MapKind.written : MapKind → Val × Val → Val
  | .keys => Prod.fst
  | _ => Prod.snd

theorem wr_hole (g : Val × Val → Val) {e : Entry} (h : e.key = .hole) : wr g e = none := by
  simp [wr, Entry.spec, h]

theorem wr_key (g : Val × Val → Val) {e : Entry} {k : Val} (h : e.key = .key k) :
    wr g e = some (g (k, e.value)) := by
  simp [wr, Entry.spec, h]

theorem length_filterMap_wr (g : Val × Val → Val) :
    ∀ l : List Entry, (l.filterMap (wr g)).length = liveCount l
  | [] => rfl
  | e :: l => by
    have ih := length_filterMap_wr g l
    cases hk : e.key with
    | hole =>
      rw [List.filterMap_cons, wr_hole g hk]
      simp [liveCount, Entry.live, hk] at ih ⊢
      exact ih
    | key k =>
      rw [List.filterMap_cons, wr_key g hk]
      simp [liveCount, Entry.live, hk] at ih ⊢
      exact ih

theorem remaining_cons (g : Val × Val → Val) {t : Table} {i : Nat} (hi : i < t.used)
    (hl : i < t.data.length) :
    remaining g t i = (wr g t.data[i]).toList ++ remaining g t (i + 1) := by
  have hlt : i < (t.data.take t.used).length := by
    simp [List.length_take]
    omega
  unfold remaining
  rw [List.drop_eq_getElem_cons hlt, List.filterMap_cons, List.getElem_take]
  cases wr g t.data[i] <;> rfl

theorem remaining_end (g : Val × Val → Val) {t : Table} {i : Nat} (hi : t.used ≤ i) :
    remaining g t i = [] := by
  unfold remaining
  rw [List.drop_eq_nil_of_le (by simp [List.length_take]; omega)]
  rfl

theorem nextSkip_cases (g : Val × Val → Val) {t : Table} (hu : t.used ≤ t.data.length)
    (i : Nat) :
    (nextSkip t i = .done ∧ remaining g t i = []) ∨
    (∃ k e en, nextSkip t i = .found k e (e + 1) ∧ t.data[e]? = some en ∧ en.key = .key k ∧
      remaining g t i = g (k, en.value) :: remaining g t (e + 1)) := by
  by_cases hi : i < t.used
  · have hl : i < t.data.length := by omega
    cases hk : t.data[i].key with
    | hole =>
      have hn : nextSkip t i = nextSkip t (i + 1) := by
        rw [nextSkip]
        simp [hi, List.getElem?_eq_getElem hl, hk]
      have hr : remaining g t i = remaining g t (i + 1) := by
        rw [remaining_cons g hi hl, wr_hole g hk]
        rfl
      rw [hn, hr]
      exact nextSkip_cases g hu (i + 1)
    | key k =>
      refine Or.inr ⟨k, i, t.data[i], ?_, List.getElem?_eq_getElem hl, hk, ?_⟩
      · rw [nextSkip]
        simp [hi, List.getElem?_eq_getElem hl, hk]
      · rw [remaining_cons g hi hl, wr_key g hk]
        rfl
  · refine Or.inl ⟨?_, remaining_end g (by omega)⟩
    rw [nextSkip]
    simp [hi]
termination_by t.used - i

theorem nextSkip_ne_oob {t : Table} (hu : t.used ≤ t.data.length) (i : Nat) :
    nextSkip t i ≠ .oob := by
  rcases nextSkip_cases Prod.fst hu i with ⟨h, _⟩ | ⟨k, e, en, h, _⟩ <;> rw [h] <;> simp

theorem remaining_length_le (g : Val × Val → Val) {t : Table} (ht : t.Inv) (i : Nat) :
    (remaining g t i).length ≤ t.nof := by
  unfold remaining
  rw [length_filterMap_wr, ← ht.count]
  exact (List.drop_sublist i _).countP_le

theorem remaining_zero_length (g : Val × Val → Val) {t : Table} (ht : t.Inv) :
    (remaining g t 0).length = t.nof := by
  unfold remaining
  rw [List.drop_zero, length_filterMap_wr, ht.count]

theorem set_prefix (out : List Val) (v : Val) (k : Nat) :
    (out.map some ++ List.replicate (k + 1) none).set out.length (some v) =
      (out ++ [v]).map some ++ List.replicate k none := by
  rw [List.set_append_right _ _ (by simp)]
  simp [List.replicate_succ]

def CopyInv (g : Val × Val → Val) (t : Table) (L : List Val) (s : Copy) : Prop :=
  ∃ out, out ++ remaining g t s.index = L ∧ s.offset = out.length ∧
    s.store = out.map some ++ List.replicate (t.nof - out.length) none

theorem CopyInv.store_length {g : Val × Val → Val} {t : Table} {L : List Val} {s : Copy}
    (hL : L.length ≤ t.nof) (hi : CopyInv g t L s) : s.store.length = t.nof := by
  obtain ⟨out, hsplit, _, hstore⟩ := hi
  have : out.length ≤ L.length := by
    rw [← hsplit]
    simp
  rw [hstore]
  simp
  omega

theorem copyInv_init (g : Val × Val → Val) (t : Table) (start : Nat) :
    CopyInv g t (remaining g t start) ⟨start, 0, allocate t.nof⟩ :=
  ⟨[], rfl, rfl, by simp [allocate]⟩

theorem storeAt_inv {g : Val × Val → Val} {t : Table} {L : List Val} {s : Copy} {v : Val}
    {n : Nat} (hL : L.length ≤ t.nof) (hi : CopyInv g t L s)
    (hrem : remaining g t s.index = v :: remaining g t n) :
    storeAt s v n = .cont ⟨n, s.offset + 1, s.store.set s.offset (some v)⟩ ∧
      CopyInv g t L ⟨n, s.offset + 1, s.store.set s.offset (some v)⟩ := by
  have hlen := hi.store_length hL
  obtain ⟨out, hsplit, hoff, hstore⟩ := hi
  have hle : out.length + 1 ≤ L.length := by
    rw [← hsplit, hrem]
    simp
  refine ⟨?_, out ++ [v], ?_, ?_, ?_⟩
  · unfold storeAt
    rw [ite_eq_left (by omega)]
  · rw [← hsplit, hrem]
    simp
  · simp [hoff]
  · show s.store.set s.offset (some v) = _
    obtain ⟨k, hk⟩ : ∃ k, t.nof - out.length = k + 1 := ⟨t.nof - out.length - 1, by omega⟩
    rw [hstore, hoff, hk, set_prefix]
    simp
    omega

theorem copyInv_done {g : Val × Val → Val} {t : Table} {L : List Val} {s : Copy}
    (hi : CopyInv g t L s) (hrem : remaining g t s.index = []) :
    s.store = L.map some ++ List.replicate (t.nof - L.length) none := by
  obtain ⟨out, hsplit, _, hstore⟩ := hi
  rw [hrem, List.append_nil] at hsplit
  subst hsplit
  exact hstore

theorem loadValue_eq {t : Table} {e : Nat} {en : Entry} (h : t.data[e]? = some en) :
    loadValue t e = some en.value := by
  simp [loadValue, h]

theorem mapStep_cases (kind : MapKind) {t : Table} (hu : t.used ≤ t.data.length)
    {L : List Val} (hL : L.length ≤ t.nof) {s : Copy} (hi : CopyInv kind.written t L s) :
    (mapStep kind t s = .done s ∧ remaining kind.written t s.index = []) ∨
      ∃ s', mapStep kind t s = .cont s' ∧ CopyInv kind.written t L s' := by
  rcases nextSkip_cases kind.written hu s.index with ⟨h, hr⟩ | ⟨k, e, en, h, he, _, hr⟩
  · left
    unfold mapStep
    rw [h]
    exact ⟨rfl, hr⟩
  · right
    unfold mapStep
    rw [h]
    cases kind with
    | keys =>
      obtain ⟨h1, h2⟩ := storeAt_inv hL hi hr
      exact ⟨_, h1, h2⟩
    | values =>
      simp only [loadValue_eq he]
      obtain ⟨h1, h2⟩ := storeAt_inv hL hi hr
      exact ⟨_, h1, h2⟩
    | entries =>
      simp only [loadValue_eq he]
      obtain ⟨h1, h2⟩ := storeAt_inv hL hi hr
      exact ⟨_, h1, h2⟩

theorem setStep_eq (t : Table) (s : Copy) : setStep t s = mapStep .keys t s := by
  unfold setStep mapStep
  split <;> rfl

theorem copy_run {step : Copy → Step Copy Copy} {μ : Copy → Nat}
    {hdec : ∀ s s', step s = .cont s' → μ s' < μ s} {P : Copy → Prop} {Q : Copy → Prop}
    (hcases : ∀ s, P s → (step s = .done s ∧ Q s) ∨ ∃ s', step s = .cont s' ∧ P s')
    {s0 : Copy} (h0 : P s0) : ∃ r, run step μ hdec s0 = .ok r ∧ P r ∧ Q r := by
  obtain ⟨u, hr, hres⟩ := run_spec step μ hdec s0
  have hu : P u := hr.invariant (fun s t hs h => by
    rcases hcases s hs with ⟨h1, _⟩ | ⟨s', h1, h2⟩
    · rw [h1] at h
      cases h
    · rw [h1] at h
      cases h
      exact h2) h0
  rcases hcases u hu with ⟨h1, hq⟩ | ⟨s', h1, _⟩
  · rw [h1] at hres
    simp only [Step.result] at hres
    exact ⟨u, by injection hres with hres; exact hres.symm, hu, hq⟩
  · rw [h1] at hres
    simp [Step.result] at hres

theorem runMap_from (kind : MapKind) {t : Table} (ht : t.Inv) (start : Nat) :
    ∃ r, runMap kind t ⟨start, 0, allocate t.nof⟩ = .ok r ∧
      r.store = (remaining kind.written t start).map some ++
        List.replicate (t.nof - (remaining kind.written t start).length) none := by
  obtain ⟨r, hr, hi, hq⟩ := copy_run (step := mapStep kind t)
    (hdec := mapStep_decreases kind t)
    (P := CopyInv kind.written t (remaining kind.written t start))
    (Q := fun s => remaining kind.written t s.index = [])
    (fun s hs => mapStep_cases kind ht.used_le (remaining_length_le _ ht start) hs)
    (copyInv_init kind.written t start)
  exact ⟨r, hr, copyInv_done hi hq⟩

theorem runSet_from {t : Table} (ht : t.Inv) (start : Nat) :
    ∃ r, runSet t ⟨start, 0, allocate t.nof⟩ = .ok r ∧
      r.store = (remaining Prod.fst t start).map some ++
        List.replicate (t.nof - (remaining Prod.fst t start).length) none := by
  obtain ⟨r, hr, hi, hq⟩ := copy_run (step := setStep t) (hdec := setStep_decreases t)
    (P := CopyInv MapKind.keys.written t (remaining MapKind.keys.written t start))
    (Q := fun s => remaining MapKind.keys.written t s.index = [])
    (fun s hs => by
      rw [setStep_eq]
      exact mapStep_cases .keys ht.used_le (remaining_length_le _ ht start) hs)
    (copyInv_init MapKind.keys.written t start)
  exact ⟨r, hr, copyInv_done hi hq⟩

theorem healIndex_zero (l : Link) : healIndex l 0 = 0 := by
  simp [healIndex]

theorem transition_zero : ∀ chain : List Link, transition chain 0 = 0
  | [] => rfl
  | l :: ls => by
    rw [transition, healIndex_zero, transition_zero ls]

theorem full_store {g : Val × Val → Val} {t : Table} (ht : t.Inv) :
    (remaining g t 0).map some ++ List.replicate (t.nof - (remaining g t 0).length) none =
      (remaining g t 0).map some := by
  rw [remaining_zero_length g ht, Nat.sub_self, List.replicate_zero, List.append_nil]

theorem resultArray_ok {g : Val × Val → Val} {t : Table} (ht : t.Inv) :
    (resultArray t.nof ((remaining g t 0).map some)).WF ∧
      (resultArray t.nof ((remaining g t 0).map some)).SlackHoles ∧
      (resultArray t.nof ((remaining g t 0).map some)).elems = (remaining g t 0).map some ∧
      (resultArray t.nof ((remaining g t 0).map some)).length = t.nof := by
  have hl : ((remaining g t 0).map some).length = t.nof := by
    rw [List.length_map, remaining_zero_length g ht]
  have he : (resultArray t.nof ((remaining g t 0).map some)).elems = (remaining g t 0).map some := by
    simp only [resultArray, JSArr.elems]
    rw [← hl, List.take_length]
  refine ⟨⟨Nat.le_of_eq hl.symm, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    nofun⟩, ?_, he, rfl⟩
  · intro x hx
    rw [he] at hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    rfl
  · intro x hx
    simp only [resultArray] at hx
    rw [List.drop_eq_nil_of_le (Nat.le_of_eq hl)] at hx
    simp at hx

theorem specIter_eq {α : Type} : ∀ (xs : List (Option α)) (i : Nat),
    specIter xs i = (xs.drop i).filterMap id := by
  intro xs i
  induction h : xs.length - i generalizing i with
  | zero =>
    rw [specIter, dite_eq_right (show ¬(i < xs.length) by omega), List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ d ih =>
    have hi : i < xs.length := by omega
    rw [specIter, dite_eq_left hi, List.drop_eq_getElem_cons hi, List.filterMap_cons]
    cases hx : xs[i] with
    | none =>
      dsimp only
      rw [ih (i + 1) (by omega)]
      rfl
    | some e =>
      dsimp only
      rw [ih (i + 1) (by omega)]
      rfl

theorem remaining_spec (g : Val × Val → Val) (t : Table) :
    remaining g t 0 = specIter ((t.data.take t.used).map fun e => e.spec.map g) 0 := by
  rw [specIter_eq, List.drop_zero, List.filterMap_map]
  unfold remaining wr
  rw [List.drop_zero]
  rfl

theorem fastIterableToList_spec {env : Env} {x : Iterable} {arr : JSArr} {x' : Iterable}
    (ht : x.table.Inv) (h : fastIterableToList env x = .ok (arr, x')) :
    arr.WF ∧ arr.SlackHoles ∧ arr.elems = x.spec.map some ∧ arr.length = x.table.nof ∧
      x'.Exhausted := by
  unfold fastIterableToList at h
  split at h
  · cases h
  split at h
  · rename_i kind it
    split at h
    · rename_i hb
      have hidx : it.index = 0 := by
        simp only [mapBranch, Bool.and_eq_true, beq_iff_eq] at hb
        exact hb.1.1.1.2
      have hkv : kind.keyOrValue = true := by
        simp only [mapBranch, Bool.and_eq_true] at hb
        exact hb.1.1.1.1
      have ht' : it.table.Inv := ht
      obtain ⟨r, hr, hs⟩ := runMap_from kind (t := it.table) ht 0
      unfold mapIteratorToList at h
      rw [hidx, transition_zero, hr] at h
      simp only [mapOk] at h
      cases h
      obtain ⟨hw, hsl, he, hl⟩ := resultArray_ok (g := kind.written) ht'
      rw [hs, full_store ht']
      refine ⟨hw, hsl, ?_, hl, rfl, rfl⟩
      rw [he]
      congr 1
      cases kind with
      | keys =>
        simp only [Iterable.spec, Table.mapData]
        rw [remaining_spec, List.map_map]
        rfl
      | values =>
        simp only [Iterable.spec, Table.mapData]
        rw [remaining_spec, List.map_map]
        rfl
      | entries => cases hkv
    · cases h
  · rename_i kind it
    split at h
    · have ht' : it.table.Inv := ht
      obtain ⟨r, hr, hs⟩ := runSet_from (t := it.table) ht 0
      unfold setOrSetIteratorToList at h
      simp only [Iterable.table] at h
      rw [hr] at h
      simp only [mapOk] at h
      cases h
      obtain ⟨hw, hsl, he, hl⟩ := resultArray_ok (g := Prod.fst) ht'
      rw [hs, full_store ht']
      refine ⟨hw, hsl, ?_, hl, rfl, rfl⟩
      rw [he]
      congr 1
      simp only [Iterable.spec, Table.setData, Table.mapData]
      rw [remaining_spec, List.map_map]
      rfl
    · cases h
  · rename_i s
    split at h
    · have ht' : s.table.Inv := ht
      obtain ⟨r, hr, hs⟩ := runSet_from (t := s.table) ht 0
      unfold setOrSetIteratorToList at h
      simp only [Iterable.table] at h
      rw [hr] at h
      simp only [mapOk] at h
      cases h
      obtain ⟨hw, hsl, he, hl⟩ := resultArray_ok (g := Prod.fst) ht'
      rw [hs, full_store ht']
      refine ⟨hw, hsl, ?_, hl, trivial⟩
      rw [he]
      congr 1
      simp only [Iterable.spec, Table.setData, Table.mapData]
      rw [remaining_spec, List.map_map]
      rfl
    · cases h
  · cases h

theorem fastIterableToList_ne_ub {env : Env} {x : Iterable} (ht : x.table.Inv) :
    fastIterableToList env x ≠ .ub ∧ fastIterableToList env x ≠ .fatal := by
  unfold fastIterableToList
  split
  · exact ⟨nofun, nofun⟩
  split
  · rename_i kind it
    split
    · rename_i hb
      have hidx : it.index = 0 := by
        simp only [mapBranch, Bool.and_eq_true, beq_iff_eq] at hb
        exact hb.1.1.1.2
      obtain ⟨r, hr, _⟩ := runMap_from kind (t := it.table) ht 0
      unfold mapIteratorToList
      rw [hidx, transition_zero, hr]
      exact ⟨nofun, nofun⟩
    · exact ⟨nofun, nofun⟩
  · rename_i kind it
    split
    · obtain ⟨r, hr, _⟩ := runSet_from (t := it.table) ht 0
      unfold setOrSetIteratorToList
      simp only [Iterable.table]
      rw [hr]
      exact ⟨nofun, nofun⟩
    · exact ⟨nofun, nofun⟩
  · rename_i s
    split
    · obtain ⟨r, hr, _⟩ := runSet_from (t := s.table) ht 0
      unfold setOrSetIteratorToList
      simp only [Iterable.table]
      rw [hr]
      exact ⟨nofun, nofun⟩
    · exact ⟨nofun, nofun⟩
  · exact ⟨nofun, nofun⟩

end ArrayFromCollections
