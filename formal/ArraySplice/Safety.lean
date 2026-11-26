import ArraySplice.Model

namespace ArraySplice

open Torque InPlace

theorem insertLoop_spec {k : Kind} :
    ∀ (xs : List Val) (s : List (Option Val)) (pos : Nat), pos + xs.length ≤ s.length →
      (k.isDouble = true → ∀ e ∈ xs, e.isNumber = true) →
      ∃ t, insertLoop false k s pos xs = .ok t ∧ t.length = s.length ∧
        ∀ j, t[j]? = if pos ≤ j ∧ j < pos + xs.length then (xs[j - pos]?).map some else s[j]?
  | [], s, p, _, _ => by
    refine ⟨s, rfl, rfl, fun j => ?_⟩
    rw [ite_eq_right (by simp only [List.length_nil]; omega)]
  | e :: rest, s, p, hl, hd => by
    simp only [List.length_cons] at hl
    have he : ¬(k.isDouble = true ∧ e.isNumber = false) := by
      intro ⟨h1, h2⟩
      rw [hd h1 e (by simp)] at h2
      cases h2
    obtain ⟨t, ht, htl, htj⟩ := insertLoop_spec rest (s.set p (some e)) (p + 1)
      (by simp; omega) (fun h x hx => hd h x (by simp [hx]))
    refine ⟨t, ?_, by rw [htl]; simp, ?_⟩
    · rw [insertLoop, ite_eq_right he, storeSlot_nat (by omega)]
      simpa using ht
    · intro j
      rw [htj j, List.getElem?_set]
      simp only [List.length_cons]
      by_cases h1 : p + 1 ≤ j ∧ j < p + 1 + rest.length
      · rw [ite_eq_left h1, ite_eq_left ⟨by omega, by omega⟩,
          show j - p = (j - (p + 1)) + 1 by omega]
        rfl
      · rw [ite_eq_right h1]
        by_cases h2 : j = p
        · subst h2
          rw [ite_eq_left rfl, ite_eq_left (show j < s.length by omega),
            ite_eq_left ⟨Nat.le_refl _, by omega⟩, Nat.sub_self]
          rfl
        · rw [ite_eq_right (Ne.symm h2), ite_eq_right (by omega)]

theorem storeHoles_spec (s : List (Option Val)) (i j : Nat) (hj : j ≤ s.length) :
    ∃ t, storeHoles false s i j = .ok t ∧ t.length = s.length ∧
      ∀ m, t[m]? = if i ≤ m ∧ m < j then some none else s[m]? := by
  induction h : j - i generalizing s i with
  | zero =>
    refine ⟨s, ?_, rfl, fun m => by rw [ite_eq_right (by omega)]⟩
    rw [storeHoles, dite_eq_right_iff.mpr (by intro h'; omega)]
  | succ d ih =>
    obtain ⟨t, ht, htl, htm⟩ := ih (s.set i none) (i + 1) (by simp; omega) (by omega)
    refine ⟨t, ?_, by rw [htl]; simp, ?_⟩
    · rw [storeHoles, dite_eq_left (show i < j by omega), storeSlot_nat (by omega)]
      simpa using ht
    · intro m
      rw [htm m, List.getElem?_set]
      by_cases h1 : i + 1 ≤ m ∧ m < j
      · rw [ite_eq_left h1, ite_eq_left ⟨by omega, by omega⟩]
      · rw [ite_eq_right h1]
        by_cases h2 : m = i
        · subst h2
          rw [ite_eq_left rfl, ite_eq_left (show m < s.length by omega),
            ite_eq_left ⟨Nat.le_refl _, by omega⟩]
        · rw [ite_eq_right (Ne.symm h2), ite_eq_right (by omega)]

structure Shuffled (e : JSArr) (n start ic adc : Nat) (s1 : List (Option Val)) : Prop where
  room : n ≤ s1.length
  head : ∀ j, j < start → s1[j]? = e.store[j]?
  tail : ∀ j, start + ic ≤ j → j < n → s1[j]? = e.store[j + adc - ic]?
  slack : ∀ j, n ≤ j → j < s1.length → s1[j]? = some none

structure ShufflePre (c : Config) (e : JSArr) (len n start ic adc : Nat) : Prop where
  cow : e.cow = false
  slack : e.SlackHoles
  length : e.length = len
  room : len ≤ e.store.length
  range : start + adc ≤ len
  newLen : n + adc = len + ic
  cap : newCapacity n ≤ c.smiMax

theorem slack_at {e : JSArr} (hsl : e.SlackHoles) {j : Nat} (hj : e.length ≤ j)
    (hs : j < e.store.length) : e.store[j]? = some none := by
  rw [List.getElem?_eq_getElem hs]
  congr 1
  apply hsl
  rw [List.mem_iff_getElem?]
  exact ⟨j - e.length, by rw [List.getElem?_drop, show e.length + (j - e.length) = j by omega,
    List.getElem?_eq_getElem hs]⟩

theorem shuffle_spec {c : Config} {e : JSArr} {len n start ic adc : Nat}
    (hp : ShufflePre c e len n start ic adc) :
    shuffle c e len n start ic adc ≠ .ub ∧
      ∀ r, shuffle c e len n start ic adc = .ok r → r.2 = false ∧ Shuffled e n start ic adc r.1 := by
  have hc := hp.cow
  have hl := hp.length
  have hr := hp.room
  have hg := hp.range
  have hn := hp.newLen
  unfold shuffle
  by_cases h1 : ic = adc
  · rw [ite_eq_left h1]
    refine ⟨nofun, fun r hr' => ?_⟩
    cases hr'
    refine ⟨hc, ⟨show n ≤ e.store.length by omega, fun _ _ => rfl,
      fun j _ _ => by rw [h1, Nat.add_sub_cancel], ?_⟩⟩
    intro j hj hjs
    exact slack_at hp.slack (by omega) hjs
  rw [ite_eq_right h1]
  have hmv : start + ic + (len - adc - start) ≤ e.store.length →
      memmove e.cow e.store (start + ic) (start + adc) (len - adc - start) =
        .ok (moveElements e.store (start + ic) (start + adc) (len - adc - start)) := by
    intro hd
    rw [hc]
    exact memmove_ok hd (by omega)
  by_cases h2 : ic < adc
  · rw [ite_eq_left h2]
    have hmove := getElem?_moveElements (store := e.store) (dst := start + ic) (src := start + adc)
      (count := len - adc - start) (by omega) (by omega)
    have hml := length_moveElements (store := e.store) (dst := start + ic) (src := start + adc)
      (count := len - adc - start) (by omega)
    obtain ⟨t, ht, htl, htm⟩ := storeHoles_spec (moveElements e.store (start + ic) (start + adc)
      (len - adc - start)) n len (by rw [hml]; exact hr)
    rw [hmv (by omega)]
    simp only [Res.ok_bind]
    rw [hc, ht]
    simp only [Res.ok_bind, Res.pure_eq]
    refine ⟨nofun, fun r hr' => ?_⟩
    cases hr'
    refine ⟨rfl, ⟨by rw [htl, hml]; omega, ?_, ?_, ?_⟩⟩
    · intro j hj
      rw [htm j, ite_eq_right (by omega), hmove j, ite_eq_right (by omega)]
    · intro j hj1 hj2
      rw [htm j, ite_eq_right (by omega), hmove j, ite_eq_left ⟨by omega, by omega⟩]
      congr 1
      omega
    · intro j hj hjs
      rw [htm j]
      by_cases h3 : j < len
      · rw [ite_eq_left ⟨hj, h3⟩]
      · rw [ite_eq_right (by omega), hmove j, ite_eq_right (by omega)]
        rw [htl, hml] at hjs
        exact slack_at hp.slack (by omega) hjs
  rw [ite_eq_right h2]
  by_cases h3 : n ≤ e.store.length
  · rw [ite_eq_left h3, hmv (by omega)]
    simp only [Res.ok_bind, Res.pure_eq]
    have hmove := getElem?_moveElements (store := e.store) (dst := start + ic) (src := start + adc)
      (count := len - adc - start) (by omega) (by omega)
    have hml := length_moveElements (store := e.store) (dst := start + ic) (src := start + adc)
      (count := len - adc - start) (by omega)
    refine ⟨nofun, fun r hr' => ?_⟩
    cases hr'
    refine ⟨hc, ⟨by rw [hml]; omega, ?_, ?_, ?_⟩⟩
    · intro j hj
      rw [hmove j, ite_eq_right (by omega)]
    · intro j hj1 hj2
      rw [hmove j, ite_eq_left ⟨by omega, by omega⟩]
      congr 1
      omega
    · intro j hj hjs
      rw [hmove j, ite_eq_right (by omega)]
      rw [hml] at hjs
      exact slack_at hp.slack (by omega) hjs
  rw [ite_eq_right h3, ite_eq_right (by have := hp.cap; omega)]
  have hcap : n < newCapacity n := by unfold newCapacity; omega
  unfold extractGrow
  by_cases h4 : e.kind.isDouble = true ∧ e.store = []
  · rw [ite_eq_left h4]
    have hz : len = 0 := by have := h4.2; rw [this] at hr; simp at hr; omega
    split
    · exact ⟨nofun, fun r hr' => by cases hr'⟩
    simp only [Res.ok_bind]
    rw [ite_eq_right (by rw [h4.2]; simp)]
    simp only [Res.pure_eq]
    refine ⟨nofun, fun r hr' => ?_⟩
    cases hr'
    refine ⟨rfl, ⟨by simp; omega, fun j hj => by omega, fun j _ _ => by omega, ?_⟩⟩
    intro j _ hjs
    rw [List.getElem?_replicate, ite_eq_left (by simpa using hjs)]
  rw [ite_eq_right h4, ite_eq_right (by omega)]
  split
  · exact ⟨nofun, fun r hr' => by cases hr'⟩
  simp only [Res.ok_bind]
  have hfl : (e.store.take start ++ List.replicate (newCapacity n - start) none).length =
      newCapacity n := by
    simp only [List.length_append, List.length_take, List.length_replicate]
    omega
  have hfresh : ∀ j, (e.store.take start ++ List.replicate (newCapacity n - start) none)[j]? =
      if j < start then e.store[j]? else if j < newCapacity n then some none else none := by
    intro j
    rw [List.getElem?_append]
    simp only [List.length_take, Nat.min_eq_left (show start ≤ e.store.length by omega)]
    by_cases hj : j < start
    · rw [ite_eq_left hj, ite_eq_left hj, List.getElem?_take, ite_eq_left hj]
    · rw [ite_eq_right hj, ite_eq_right hj, List.getElem?_replicate]
      by_cases hk : j < newCapacity n
      · rw [ite_eq_left (by omega), ite_eq_left hk]
      · rw [ite_eq_right (by omega), ite_eq_right hk]
  by_cases h5 : 0 < e.store.length
  · rw [ite_eq_left h5, memcpy_ok (by rw [hfl]; omega) (by omega)]
    simp only [Res.ok_bind, Res.pure_eq]
    refine ⟨nofun, fun r hr' => ?_⟩
    cases hr'
    have hlen : ((e.store.drop (start + adc)).take (len - adc - start)).length =
        len - adc - start := by
      simp only [List.length_take, List.length_drop]
      omega
    have hbl := getElem?_blit (buf := e.store.take start ++ List.replicate (newCapacity n - start)
      none) (pos := start + ic) (src := (e.store.drop (start + adc)).take (len - adc - start))
      (by rw [hlen, hfl]; omega)
    refine ⟨rfl, ⟨by rw [length_blit (by rw [hlen, hfl]; omega), hfl]; omega, ?_, ?_, ?_⟩⟩
    · intro j hj
      rw [hbl j, ite_eq_left (by omega), hfresh j, ite_eq_left hj]
    · intro j hj1 hj2
      rw [hbl j, ite_eq_right (by omega), ite_eq_left (by rw [hlen]; omega), List.getElem?_take,
        ite_eq_left (by omega), List.getElem?_drop]
      congr 1
      omega
    · intro j hj hjs
      rw [length_blit (by rw [hlen, hfl]; omega), hfl] at hjs
      rw [hbl j, ite_eq_right (by omega), ite_eq_right (by rw [hlen]; omega), hfresh j,
        ite_eq_right (by omega), ite_eq_left hjs]
  · rw [ite_eq_right h5]
    simp only [Res.pure_eq]
    refine ⟨nofun, fun r hr' => ?_⟩
    cases hr'
    have hz : len = 0 := by omega
    refine ⟨rfl, ⟨by rw [hfl]; omega, fun j hj => by omega, fun j _ _ => by omega, ?_⟩⟩
    intro j hj hjs
    rw [hfl] at hjs
    rw [hfresh j, ite_eq_right (by omega), ite_eq_left hjs]

structure Fits (k K : Kind) (xs : List Val) : Prop where
  items : ∀ e ∈ xs, kindOk K (some e) = true
  general : ∀ x, kindOk k x = true → kindOk K x = true
  double : K.isDouble = true → ∀ e ∈ xs, e.isNumber = true
  fast : K.isFast = true

theorem insertionKind_fits : ∀ (xs : List Val) (k : Kind), k.isFast = true →
    Fits k (insertionKind k xs) xs
  | [], k, hf => ⟨fun _ he => by simp at he, fun _ h => h, fun _ _ he => by simp at he, hf⟩
  | e :: rest, k, hf => by
    unfold insertionKind
    by_cases hs : isSmiKind k = true
    · rw [ite_eq_left hs]
      have hk : k = .packedSmi ∨ k = .holeySmi := by
        cases k <;> simp_all [isSmiKind]
      by_cases he : e.isSmi = true
      · rw [ite_eq_left he]
        have ih := insertionKind_fits rest k hf
        refine ⟨?_, ih.general, ?_, ih.fast⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ih.general _ (by rcases hk with rfl | rfl <;> simpa [kindOk] using he)
          · exact ih.items x hx
        · intro hd x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact isNumber_of_isSmi he
          · exact ih.double hd x hx
      rw [ite_eq_right he]
      by_cases hn : isHeapNumber e = true
      · rw [ite_eq_left hn]
        have hd' : (allowDouble k).isFast = true := by rcases hk with rfl | rfl <;> rfl
        have ih := insertionKind_fits rest (allowDouble k) hd'
        have hen : e.isNumber = true := by cases e <;> simp_all [isHeapNumber, Val.isNumber]
        refine ⟨?_, fun x hx => ih.general x ?_, ?_, ih.fast⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ih.general _ (by rcases hk with rfl | rfl <;> simp [allowDouble, kindOk, hen])
          · exact ih.items x hx
        · rcases hk with rfl | rfl <;> cases x <;> simp_all [allowDouble, kindOk, isNumber_of_isSmi]
        · intro hd x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hen
          · exact ih.double hd x hx
      rw [ite_eq_right hn]
      have hd' : (allowNonNumber k).isFast = true := by rcases hk with rfl | rfl <;> rfl
      have ih := insertionKind_fits rest (allowNonNumber k) hd'
      have hobj : insertionKind (allowNonNumber k) rest = allowNonNumber k := by
        rcases hk with rfl | rfl <;> cases rest <;> rfl
      refine ⟨?_, fun x hx => ih.general x ?_, ?_, ih.fast⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ih.general _ (by rcases hk with rfl | rfl <;> rfl)
        · exact ih.items x hx
      · rcases hk with rfl | rfl <;> cases x <;> simp_all [allowNonNumber, kindOk]
      · intro hd
        rw [hobj] at hd
        rcases hk with rfl | rfl <;> cases hd
    rw [ite_eq_right hs]
    by_cases hdk : k.isDouble = true
    · rw [ite_eq_left hdk]
      have hk : k = .packedDouble ∨ k = .holeyDouble := by
        cases k <;> simp_all [Kind.isDouble]
      by_cases hen : e.isNumber = true
      · rw [ite_eq_left hen]
        have ih := insertionKind_fits rest k hf
        refine ⟨?_, ih.general, ?_, ih.fast⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ih.general _ (by rcases hk with rfl | rfl <;> simp [kindOk, hen])
          · exact ih.items x hx
        · intro hd x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hen
          · exact ih.double hd x hx
      rw [ite_eq_right hen]
      have hd' : (allowNonNumber k).isFast = true := by rcases hk with rfl | rfl <;> rfl
      have ih := insertionKind_fits rest (allowNonNumber k) hd'
      have hobj : insertionKind (allowNonNumber k) rest = allowNonNumber k := by
        rcases hk with rfl | rfl <;> cases rest <;> rfl
      refine ⟨?_, fun x hx => ih.general x ?_, ?_, ih.fast⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ih.general _ (by rcases hk with rfl | rfl <;> rfl)
        · exact ih.items x hx
      · rcases hk with rfl | rfl <;> cases x <;> simp_all [allowNonNumber, kindOk]
      · intro hd
        rw [hobj] at hd
        rcases hk with rfl | rfl <;> cases hd
    rw [ite_eq_right hdk]
    have hk : k = .packedElem ∨ k = .holeyElem := by
      cases k <;> simp_all [isSmiKind, Kind.isDouble, Kind.isFast]
    refine ⟨?_, fun _ h => h, ?_, hf⟩
    · intro x _
      rcases hk with rfl | rfl <;> rfl
    · intro hd
      rcases hk with rfl | rfl <;> cases hd

theorem kindOk_transitionTarget {k K : Kind} {x : Option Val} (h : kindOk K x = true) :
    kindOk (k.transitionTarget K) x = true := by
  unfold Kind.transitionTarget
  split
  · cases K <;> cases x <;> simp_all [Kind.toHoley, kindOk]
  · exact h

theorem transitionTarget_isDouble (k K : Kind) :
    (k.transitionTarget K).isDouble = K.isDouble := by
  unfold Kind.transitionTarget
  split
  · cases K <;> rfl
  · rfl

theorem transitionTarget_isFast {k K : Kind} (h : K.isFast = true) :
    (k.transitionTarget K).isFast = true := by
  unfold Kind.transitionTarget
  split
  · cases K <;> simp_all [Kind.toHoley, Kind.isFast]
  · exact h

def specList (b : JSArr) (start adc : Nat) (xs : List Val) : List (Option Val) :=
  (specSplice b.elems start adc xs).1

theorem fastSplice_spec {c : Config} {b : JSArr} {len n start adc : Nat} {xs : List Val}
    (hw : b.WF) (hsl : b.SlackHoles) (hl : b.length = len) (hr : start + adc ≤ len)
    (hn : n + adc = len + xs.length) (hcap : newCapacity n ≤ c.smiMax)
    (hst : b.store.length ≤ c.maxLen) (hms : c.maxLen ≤ c.smiMax)
    (hitems : ∀ e ∈ xs, kindOk b.kind (some e) = true)
    (hdbl : b.kind.isDouble = true → ∀ e ∈ xs, e.isNumber = true) :
    fastSplice c b len n start adc xs ≠ .ub ∧
      ∀ b', fastSplice c b len n start adc xs = .ok b' →
        b'.WF ∧ b'.SlackHoles ∧ b'.elems = specList b start adc xs ∧ b'.length = n ∧
          b'.kind = b.kind ∧ b'.cow = false := by
  have hew := ensureWritable_wf hw
  have hesl := ensureWritable_slack hsl
  have hek := ensureWritable_kind b
  have hel := ensureWritable_length b
  have hee := ensureWritable_elems b
  have hec := ensureWritable_cow b
  have hpre : ShufflePre c (ensureWritable b) len n start xs.length adc :=
    ⟨hec, hesl, by rw [hel, hl], by rw [← hl, ← hel]; exact hew.length_le, hr, hn, hcap⟩
  obtain ⟨hsu, hsr⟩ := shuffle_spec hpre
  unfold fastSplice
  rw [ensureWritableChecked_ok hw hst hms]
  simp only [Res.ok_bind]
  have helen : b.elems.length = len := by rw [JSArr.elems_length hw, hl]
  cases hsh : shuffle c (ensureWritable b) len n start xs.length adc with
  | ub => exact absurd hsh hsu
  | abort =>
    simp only [Res.abort_bind]
    exact ⟨nofun, fun b' h => by cases h⟩
  | ok r =>
    obtain ⟨r1, r2⟩ := r
    obtain ⟨hr2, hshuf0⟩ := hsr _ hsh
    have hshuf : Shuffled (ensureWritable b) n start xs.length adc r1 := hshuf0
    simp only at hr2
    subst hr2
    simp only [Res.ok_bind]
    have hroom := hshuf.room
    have hesl' := hew.length_le
    rw [hel] at hesl'
    obtain ⟨t, ht, htl, htj⟩ := insertLoop_spec (k := (ensureWritable b).kind) xs r1 start
      (by omega) (by rw [hek]; exact hdbl)
    rw [ht]
    simp only [Res.ok_bind, Res.pure_eq]
    refine ⟨nofun, fun b' hb' => ?_⟩
    cases hb'
    have hS : (specList b start adc xs).length = n := by
      simp only [specList, specSplice, List.length_append, List.length_take, List.length_map,
        List.length_drop, helen]
      omega
    have hpt : ∀ j, j < t.length → t[j]? = some ((specList b start adc xs).getD j none) := by
      intro j hj
      rw [htj j, List.getD_eq_getElem?_getD]
      simp only [specList, specSplice]
      rw [List.getElem?_append, List.getElem?_append]
      simp only [List.length_append, List.length_take, List.length_map, helen,
        Nat.min_eq_left (show start ≤ len by omega)]
      by_cases h1 : start ≤ j ∧ j < start + xs.length
      · rw [ite_eq_left h1, ite_eq_left (by omega), ite_eq_right (by omega), List.getElem?_map,
          List.getElem?_eq_getElem (show j - start < xs.length by omega)]
        rfl
      · rw [ite_eq_right h1]
        by_cases h2 : j < start
        · rw [hshuf.head j h2, getElem?_store hesl hew.length_le (by omega), hee,
            ite_eq_left (by omega), ite_eq_left h2, List.getElem?_take, ite_eq_left h2,
            List.getD_eq_getElem?_getD]
        · by_cases h3 : j < n
          · rw [hshuf.tail j (by omega) h3,
              getElem?_store hesl hew.length_le (by omega), hee, ite_eq_right (by omega),
              List.getElem?_drop, List.getD_eq_getElem?_getD,
              show start + adc + (j - (start + xs.length)) = j + adc - xs.length by omega]
          · have hnj : n ≤ j := by omega
            have hjl : j < r1.length := by rw [htl] at hj; exact hj
            rw [hshuf.slack j hnj hjl, ite_eq_right (show ¬(j < start + xs.length) by omega),
              List.getElem?_drop, List.getElem?_eq_none (by rw [helen]; omega)]
            rfl
    have hform := eq_append_replicate (by rw [hS, htl]; exact hshuf.room) hpt
    have hfin := elems_slack_of_store
      (b := { ensureWritable b with store := t, length := n, cow := false }) hform (by rw [hS])
    refine ⟨?_, hfin.2.1, hfin.1, rfl, hek, rfl⟩
    exact {
      length_le := hfin.2.2
      kind_ok := by
        intro x hx
        rw [hfin.1] at hx
        show kindOk (ensureWritable b).kind x = true
        rw [hek]
        simp only [specList, specSplice, List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact hw.kind_ok x (List.mem_of_mem_take hx)
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
          exact hitems e he
        · exact hw.kind_ok x (List.mem_of_mem_drop hx)
      forRead_fast := hew.forRead_fast
      fast_forRead := hew.fast_forRead
      forCopy_fast := hew.forCopy_fast
      cow_not_double := nofun }

structure Bounds (c : Config) (a : JSArr) (len start adc : Nat) (xs : List Val) : Prop where
  store : a.store.length ≤ c.maxLen
  maxLen : c.maxLen ≤ c.smiMax
  range : start + adc ≤ len
  grow : newCapacity (len + xs.length) ≤ c.smiMax

theorem transition_props {c : Config} {a b : JSArr} {xs : List Val} (hw : a.WF)
    (hsl : a.SlackHoles) (hf : a.kind.isFast = true)
    (h : transitionForInsertion c a xs = .ok b) :
    b.WF ∧ b.SlackHoles ∧ b.elems = a.elems ∧ b.length = a.length ∧
      b.store.length = a.store.length ∧ (∀ e ∈ xs, kindOk b.kind (some e) = true) ∧
      (b.kind.isDouble = true → ∀ e ∈ xs, e.isNumber = true) := by
  have hfit := insertionKind_fits xs a.kind hf
  unfold transitionForInsertion at h
  split at h
  · rename_i heq
    cases h
    rw [heq] at hfit
    exact ⟨hw, hsl, rfl, rfl, rfl, hfit.items, hfit.double⟩
  · obtain ⟨_, ht⟩ := transitionTo_spec (c := c) (insertionKind a.kind xs) hw
    have htr := ht b h
    have hel : b.elems = a.elems := by simp [JSArr.elems, htr.store_eq, htr.length_eq]
    refine ⟨?_, ?_, hel, htr.length_eq, by rw [htr.store_eq], ?_, ?_⟩
    · exact {
        length_le := by rw [htr.store_eq, htr.length_eq]; exact hw.length_le
        kind_ok := by
          intro x hx
          rw [hel] at hx
          rw [htr.kind_eq]
          exact kindOk_transitionTarget (hfit.general x (hw.kind_ok x hx))
        forRead_fast := fun _ => by rw [htr.kind_eq]; exact transitionTarget_isFast hfit.fast
        fast_forRead := fun hfa => by
          rw [htr.forRead_eq]
          exact hw.fast_forRead (by rw [← htr.fast_eq]; exact hfa)
        forCopy_fast := fun hfc => by
          rw [htr.fast_eq]
          exact hw.forCopy_fast (by rw [← htr.forCopy_eq]; exact hfc)
        cow_not_double := fun hc => by
          cases hd : b.kind.isDouble
          · rfl
          · rw [htr.cow_double hd] at hc
            cases hc }
    · show ∀ x ∈ b.store.drop b.length, x = none
      rw [htr.store_eq, htr.length_eq]
      exact hsl
    · intro e he
      rw [htr.kind_eq]
      exact kindOk_transitionTarget (hfit.items e he)
    · intro hd
      rw [htr.kind_eq, transitionTarget_isDouble] at hd
      exact hfit.double hd

theorem take_drop_store {b : JSArr} {start adc : Nat} (h : start + adc ≤ b.length) :
    (b.store.drop start).take adc = (b.elems.drop start).take adc := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take, List.getElem?_take, List.getElem?_drop, List.getElem?_drop]
  by_cases hj : j < adc
  · rw [ite_eq_left hj, ite_eq_left hj]
    simp only [JSArr.elems, List.getElem?_take]
    rw [ite_eq_left (by omega)]
  · rw [ite_eq_right hj, ite_eq_right hj]

theorem extract_spec {c : Config} {b : JSArr} {start adc : Nat} (hw : b.WF)
    (hf : b.kind.isFast = true) (h : start + adc ≤ b.length) :
    extract c b start adc ≠ .ub ∧ ∀ d, extract c b start adc = .ok d →
      d.WF ∧ d.SlackHoles ∧ d.elems = (b.elems.drop start).take adc ∧ d.length = adc := by
  have hl := hw.length_le
  have hk : ∀ x ∈ (b.elems.drop start).take adc, kindOk b.kind x = true :=
    fun x hx => hw.kind_ok x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have hlen : ((b.elems.drop start).take adc).length = adc := by
    simp only [List.length_take, List.length_drop, JSArr.elems_length hw]
    omega
  unfold extract
  split
  · rename_i h0
    subst h0
    refine ⟨nofun, fun d hd => ?_⟩
    cases hd
    exact ⟨newArray_wf hf (by simp), newArray_slack _ _, by simp [newArray_elems], rfl⟩
  · split
    · exact ⟨nofun, fun d hd => by cases hd⟩
    · rw [memcpy_ok (by simp) (by omega)]
      simp only [Res.ok_bind, Res.pure_eq]
      have hbl : blit (List.replicate adc none) 0 ((b.store.drop start).take adc) =
          (b.elems.drop start).take adc := by
        rw [take_drop_store h]
        simp [blit, hlen]
      refine ⟨nofun, fun d hd => ?_⟩
      cases hd
      rw [hbl]
      exact ⟨newArray_wf hf hk, newArray_slack _ _, newArray_elems _ _, by simp [newArray, hlen]⟩

theorem newCapacity_mono {m n : Nat} (h : m ≤ n) : newCapacity m ≤ newCapacity n := by
  unfold newCapacity
  omega

theorem tryFast_spec {c : Config} {m : MapInfo} {a : JSArr} {len start adc : Nat} {xs : List Val}
    (hw : a.WF) (hsl : a.SlackHoles) (hb : Bounds c a len start adc xs) :
    tryFast c m a len start adc xs ≠ .ub ∧
      ∀ a' d, tryFast c m a len start adc xs = .done a' d →
        a'.WF ∧ a'.SlackHoles ∧ a'.elems = (specSplice a.elems start adc xs).1 ∧
          a'.length = len + xs.length - adc ∧ d.WF ∧
          d.elems = (specSplice a.elems start adc xs).2 ∧ d.length = adc := by
  have hrange := hb.range
  unfold tryFast
  split
  · exact ⟨nofun, fun _ _ h => by cases h⟩
  split
  · exact ⟨nofun, fun _ _ h => by cases h⟩
  rename_i _ hfc
  have hfc' : a.forCopy = true := by
    cases h : a.forCopy
    · exact absurd (Or.inl h) hfc
    · rfl
  have hfast : a.kind.isFast = true := hw.forRead_fast (hw.fast_forRead (hw.forCopy_fast hfc'))
  cases ht : transitionForInsertion c a xs with
  | ub =>
    unfold transitionForInsertion at ht
    split at ht
    · cases ht
    · exact absurd ht (transitionTo_spec _ hw).1
  | abort => exact ⟨nofun, fun _ _ h => by cases h⟩
  | ok b =>
    obtain ⟨hbw, hbsl, hbe, hbl, hbs, hbi, hbd⟩ := transition_props hw hsl hfast ht
    have hbf : b.kind.isFast = true := hbw.forRead_fast (by
      have := hw.fast_forRead (hw.forCopy_fast hfc')
      unfold transitionForInsertion at ht
      split at ht
      · cases ht
        exact this
      · exact ((transitionTo_spec _ hw).2 b ht).forRead_eq ▸ this)
    simp only [Res.ok_then]
    split
    · exact ⟨nofun, fun _ _ h => by cases h⟩
    split
    · exact ⟨nofun, fun _ _ h => by cases h⟩
    rename_i _ hlen
    have hlen' : len = b.length := by
      cases Nat.decEq len b.length with
      | isTrue h => exact h
      | isFalse h => exact absurd h hlen
    have hgrow := hb.grow
    have hn1 : len + xs.length - adc ≤ newCapacity (len + xs.length) := by
      unfold newCapacity
      omega
    rw [ite_eq_right (by omega)]
    obtain ⟨hex, hexs⟩ := extract_spec (c := c) hbw hbf (start := start) (adc := adc)
      (by omega)
    cases he : extract c b start adc with
    | ub => exact absurd he hex
    | abort => exact ⟨nofun, fun _ _ h => by cases h⟩
    | ok d =>
      obtain ⟨hdw, _, hde, hdl⟩ := hexs d he
      simp only [Res.ok_then]
      have hspec2 : d.elems = (specSplice a.elems start adc xs).2 := by
        rw [hde, hbe]
        rfl
      have helen : a.elems.length = len := by rw [JSArr.elems_length hw, ← hbl, ← hlen']
      split
      · rename_i h0
        refine ⟨nofun, fun a' d' h => ?_⟩
        cases h
        refine ⟨⟨by simp, by simp [JSArr.elems], ?_, ?_, ?_, ?_⟩, ?_, ?_, h0.symm ▸ rfl, hdw,
          hspec2, hdl⟩
        · intro _
          exact hbf
        · exact hbw.fast_forRead
        · exact hbw.forCopy_fast
        · nofun
        · intro x hx
          simp at hx
        · have : (List.take start a.elems ++ List.map some xs ++ List.drop (start + adc) a.elems)
              = [] := by
            rw [← List.length_eq_zero_iff]
            simp only [List.length_append, List.length_take, List.length_map, List.length_drop,
              helen]
            omega
          show List.take 0 [] = (specSplice a.elems start adc xs).1
          simp only [List.take_nil, specSplice]
          exact this.symm
      · rename_i h0
        obtain ⟨hfu, hfs⟩ := fastSplice_spec (c := c) (n := len + xs.length - adc) hbw hbsl
          hlen'.symm (by omega) (by omega)
          (Nat.le_trans (newCapacity_mono (by omega)) hgrow) (by rw [hbs]; exact hb.store) hb.maxLen
          hbi hbd
        cases hfsp : fastSplice c b len (len + xs.length - adc) start adc xs with
        | ub => exact absurd hfsp hfu
        | abort => exact ⟨nofun, fun _ _ h => by cases h⟩
        | ok b' =>
          obtain ⟨hw', hsl', he', hl', _, _⟩ := hfs b' hfsp
          simp only [Res.ok_then]
          refine ⟨nofun, fun a' d' h => ?_⟩
          cases h
          refine ⟨hw', hsl', ?_, hl', hdw, hspec2, hdl⟩
          rw [he']
          simp only [specList, hbe]

theorem actual_range (len : Nat) (args : Args) :
    actualStart len args.startArg + actualDeleteCount len args ≤ len := by
  have hs : actualStart len args.startArg ≤ len := by
    unfold actualStart
    split
    · split <;> omega
    · omega
  cases args with
  | none => simp only [actualDeleteCount]; omega
  | start s => simp only [actualDeleteCount, Args.startArg] at hs ⊢; omega
  | full s dc xs => simp only [actualDeleteCount, Args.startArg] at hs ⊢; omega

end ArraySplice
