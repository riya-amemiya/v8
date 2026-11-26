import ArrayUnshift.Model

namespace ArrayUnshift

open Torque InPlace

theorem argsKind_spec : ∀ (t : Kind) (xs : List Val),
    (argsKind t xs = t ∧ ∀ e ∈ xs, e.isSmi = true) ∨
      (argsKind t xs = .packedDouble ∧ ∀ e ∈ xs, e.isNumber = true) ∨
      argsKind t xs = .packedElem
  | t, [] => Or.inl ⟨rfl, fun _ h => absurd h (List.not_mem_nil)⟩
  | t, .smi n :: rest => by
    have he : argsKind t (.smi n :: rest) = argsKind t rest := rfl
    rw [he]
    rcases argsKind_spec t rest with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
    · refine Or.inl ⟨h1, ?_⟩
      intro e hm
      rcases List.mem_cons.mp hm with rfl | hm
      · rfl
      · exact h2 e hm
    · refine Or.inr (Or.inl ⟨h1, ?_⟩)
      intro e hm
      rcases List.mem_cons.mp hm with rfl | hm
      · rfl
      · exact h2 e hm
    · exact Or.inr (Or.inr h1)
  | t, .num n :: rest => by
    have he : argsKind t (.num n :: rest) = argsKind .packedDouble rest := rfl
    rw [he]
    rcases argsKind_spec .packedDouble rest with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
    · refine Or.inr (Or.inl ⟨h1, ?_⟩)
      intro e hm
      rcases List.mem_cons.mp hm with rfl | hm
      · rfl
      · exact isNumber_of_isSmi (h2 e hm)
    · refine Or.inr (Or.inl ⟨h1, ?_⟩)
      intro e hm
      rcases List.mem_cons.mp hm with rfl | hm
      · rfl
      · exact h2 e hm
    · exact Or.inr (Or.inr h1)
  | _, .arr _ :: _ => Or.inr (Or.inr rfl)
  | _, .proxy :: _ => Or.inr (Or.inr rfl)
  | _, .undef :: _ => Or.inr (Or.inr rfl)
  | _, .other :: _ => Or.inr (Or.inr rfl)

theorem fits_same_smi {k : Kind} {xs : List Val} (hf : k.isFast = true)
    (h : ∀ e ∈ xs, e.isSmi = true) : KindFits k k xs where
  fast := hf
  general := fun _ hx => hx
  items := by
    intro e he
    have := h e he
    cases k <;> cases e <;> simp_all [kindOk, Val.isSmi, Val.isNumber, Kind.isFast]
  double := fun _ e he => isNumber_of_isSmi (h e he)

theorem fits_object {k : Kind} {xs : List Val} (hk : isObjectKind k = true) : KindFits k k xs where
  fast := by cases k <;> simp_all [isObjectKind, Kind.isFast]
  general := fun _ hx => hx
  items := by
    intro e _
    cases k <;> simp_all [isObjectKind, kindOk]
  double := by
    intro hd
    cases k <;> simp_all [isObjectKind, Kind.isDouble]

theorem fits_double {k : Kind} {xs : List Val} (hf : k.isFast = true) (ho : isObjectKind k = false)
    (h : ∀ e ∈ xs, e.isNumber = true) : KindFits k (k.transitionTarget .packedDouble) xs where
  fast := by cases k <;> simp_all [isObjectKind, Kind.isFast, Kind.transitionTarget, Kind.isHoley,
    Kind.toHoley]
  general := by
    intro x hx
    cases k <;> rcases x with _ | v <;> (try cases v) <;>
      simp_all [isObjectKind, Kind.isFast, Kind.transitionTarget, Kind.isHoley, Kind.toHoley,
        kindOk, Val.isSmi, Val.isNumber]
  items := by
    intro e he
    have := h e he
    cases k <;> cases e <;>
      simp_all [isObjectKind, Kind.isFast, Kind.transitionTarget, Kind.isHoley, Kind.toHoley,
        kindOk, Val.isNumber]
  double := fun _ => h

theorem fits_elem {k : Kind} {xs : List Val} (hf : k.isFast = true) :
    KindFits k (k.transitionTarget .packedElem) xs where
  fast := by cases k <;> simp_all [Kind.isFast, Kind.transitionTarget, Kind.isHoley, Kind.toHoley]
  general := by
    intro x hx
    cases k <;> rcases x with _ | v <;>
      simp_all [Kind.isFast, Kind.transitionTarget, Kind.isHoley, Kind.toHoley, kindOk]
  items := by
    intro e _
    cases k <;> simp_all [Kind.isFast, Kind.transitionTarget, Kind.isHoley, Kind.toHoley, kindOk]
  double := by
    intro hd
    cases k <;> simp_all [Kind.isFast, Kind.transitionTarget, Kind.isHoley, Kind.toHoley,
      Kind.isDouble]

structure Matched (a d : JSArr) (xs : List Val) : Prop where
  store_eq : d.store = a.store
  length_eq : d.length = a.length
  forRead_eq : d.forRead = a.forRead
  fast_eq : d.fast = a.fast
  forCopy_eq : d.forCopy = a.forCopy
  cow_false : a.cow = false → d.cow = false
  fits : KindFits a.kind d.kind xs

theorem matchKind_spec {c : Config} {a : JSArr} {xs : List Val} (hw : a.WF)
    (hf : a.kind.isFast = true) :
    matchKind c a xs ≠ .ub ∧ ∀ d, matchKind c a xs = .ok d → Matched a d xs := by
  have same : ∀ d, d = a → KindFits a.kind a.kind xs → Matched a d xs := by
    intro d hd hk
    subst hd
    exact ⟨rfl, rfl, rfl, rfl, rfl, id, hk⟩
  unfold matchKind
  split
  · rename_i h0
    subst h0
    exact ⟨nofun, fun d hd => same d (by cases hd; rfl) (fits_same_smi hf nofun)⟩
  split
  · rename_i ho
    exact ⟨nofun, fun d hd => same d (by cases hd; rfl) (fits_object ho)⟩
  rename_i _ ho
  have ho' : isObjectKind a.kind = false := by simpa using ho
  split
  · rename_i heq
    refine ⟨nofun, fun d hd => same d (by cases hd; rfl) ?_⟩
    rcases argsKind_spec a.kind xs with ⟨_, h2⟩ | ⟨h1, h2⟩ | h1
    · exact fits_same_smi hf h2
    · have hk : a.kind = .packedDouble := heq.symm.trans h1
      have : a.kind.transitionTarget .packedDouble = a.kind := by
        rw [hk]
        rfl
      have := fits_double hf ho' h2
      rwa [‹a.kind.transitionTarget .packedDouble = a.kind›] at this
    · have hk : a.kind = .packedElem := heq.symm.trans h1
      rw [hk] at ho'
      cases ho'
  rename_i hne
  obtain ⟨hnu, hprops⟩ := transitionTo_spec (c := c) (argsKind a.kind xs) hw
  refine ⟨hnu, fun d hd => ?_⟩
  have ht := hprops d hd
  refine ⟨ht.store_eq, ht.length_eq, ht.forRead_eq, ht.fast_eq, ht.forCopy_eq, ht.cow_false, ?_⟩
  rw [ht.kind_eq]
  rcases argsKind_spec a.kind xs with ⟨h1, _⟩ | ⟨h1, h2⟩ | h1
  · exact absurd h1 hne
  · rw [h1]
    exact fits_double hf ho' h2
  · rw [h1]
    exact fits_elem hf

theorem matchKind_ok {c : Config} {a : JSArr} {xs : List Val} (hcap : a.store.length ≤ c.maxLen) :
    ∃ d, matchKind c a xs = .ok d := by
  unfold matchKind
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  exact transitionTo_ok _ hcap

theorem newElementsCapacity_ge (maxLen n : Nat) : n ≤ newElementsCapacity maxLen n := by
  unfold newElementsCapacity
  split
  · omega
  · omega

theorem copyArguments_ok {k : Kind} {s : List (Option Val)} {xs : List Val}
    (hl : xs.length ≤ s.length) (hd : k.isDouble = true → ∀ e ∈ xs, e.isNumber = true) :
    copyArguments false k s xs = .ok (blit s 0 (xs.map some)) := by
  unfold copyArguments
  rw [ite_eq_right]
  intro h
  rcases h with h | h | ⟨h1, h2⟩
  · cases h
  · omega
  · obtain ⟨e, he, hn⟩ := List.any_eq_true.mp h2
    rw [hd h1 e he] at hn
    cases hn

theorem length_grownStore (b : JSArr) {n cap : Nat} (h : n ≤ cap) :
    (grownStore b n cap).length = cap := by
  unfold grownStore growTo
  simp [List.length_take]
  omega

theorem getD_spec (xs : List (Option Val)) (items : List Val) (j : Nat) :
    (specUnshift xs items).getD j none =
      if j < items.length then some (items.getD j .undef) else xs.getD (j - items.length) none := by
  unfold specUnshift
  rw [List.getD_eq_getElem?_getD, List.getElem?_append]
  simp only [List.length_map, List.getElem?_map]
  by_cases h : j < items.length
  · rw [ite_eq_left h, ite_eq_left h, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h]
    rfl
  · rw [ite_eq_right h, ite_eq_right h, List.getD_eq_getElem?_getD]

theorem getElem?_items {s : List (Option Val)} {items : List Val} (hl : items.length ≤ s.length)
    {j : Nat} (hj : j < items.length) :
    (blit s 0 (items.map some))[j]? = some (some (items.getD j .undef)) := by
  rw [getElem?_blit (by simp; omega), ite_eq_right (by omega), ite_eq_left (by simp; omega)]
  simp only [List.getElem?_map, Nat.sub_zero, List.getElem?_eq_getElem hj, Option.map_some,
    List.getD_eq_getElem?_getD]
  rfl

structure Added (d d' : JSArr) (xs : List Val) : Prop where
  kind_eq : d'.kind = d.kind
  length_eq : d'.length = d.length + xs.length
  cow_eq : d'.cow = false
  flags : d'.forRead = d.forRead ∧ d'.fast = d.fast ∧ d'.forCopy = d.forCopy
  len_le : d'.length ≤ d'.store.length
  store_eq : d'.store = specUnshift d.elems xs ++
    List.replicate (d'.store.length - (specUnshift d.elems xs).length) none

theorem addArguments_spec {c : Config} {d : JSArr} {xs : List Val} (hl : d.length ≤ d.store.length)
    (hcow : d.cow = false) (hd : d.kind.isDouble = true → ∀ e ∈ xs, e.isNumber = true) :
    (addArguments c d xs = .throws ∧ d.store.length < d.length + xs.length ∧
        c.maxLen < newElementsCapacity c.maxLen (d.length + xs.length)) ∨
      ∃ d', addArguments c d xs = .done d' (d.length + xs.length) ∧
        (d.SlackHoles → Added d d' xs) := by
  have hel : d.elems.length = d.length := by
    simp [JSArr.elems, List.length_take]
    omega
  unfold addArguments
  split
  · rename_i hgrow
    split
    · exact Or.inl ⟨rfl, hgrow, by assumption⟩
    have hge := newElementsCapacity_ge c.maxLen (d.length + xs.length)
    dsimp only
    generalize newElementsCapacity c.maxLen (d.length + xs.length) = cap at hge
    have hgl := length_grownStore d (n := xs.length) (show xs.length ≤ cap by omega)
    rw [copyArguments_ok (by omega) hd, Res.ok_then]
    refine Or.inr ⟨_, rfl, fun hsl => ?_⟩
    have htl : (blit (grownStore d xs.length cap) 0 (xs.map some)).length = cap := by
      rw [length_blit (by simp; omega), hgl]
    refine ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩,
      by show d.length + xs.length ≤ (blit _ _ _).length; omega, ?_⟩
    have hspl : (specUnshift d.elems xs).length = d.length + xs.length := by
      simp [specUnshift, hel]
      omega
    apply eq_append_replicate (by dsimp only; omega)
    intro j hj
    dsimp only at hj
    rw [htl] at hj
    rw [getD_spec]
    by_cases h1 : j < xs.length
    · rw [ite_eq_left h1, getElem?_items (by omega) h1]
    · rw [ite_eq_right h1, getElem?_blit (by simp; omega), ite_eq_right (by omega),
        ite_eq_right (by simp; omega)]
      unfold grownStore growTo
      rw [List.getElem?_append]
      simp only [List.length_append, List.length_replicate, List.length_take]
      by_cases h2 : j < xs.length + min (cap - xs.length) d.store.length
      · rw [ite_eq_left h2, List.getElem?_append_right (by simp; omega), List.getElem?_take,
          List.length_replicate, ite_eq_left (by omega), getElem?_store hsl hl (by omega)]
      · rw [ite_eq_right h2, List.getElem?_replicate, ite_eq_left (by omega),
          List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
  · rename_i hfit
    rw [hcow, memmove_ok (by omega) (by omega), Res.ok_bind,
      copyArguments_ok (by rw [length_moveElements (by omega)]; omega) hd, Res.ok_then]
    refine Or.inr ⟨_, rfl, fun hsl => ?_⟩
    have hml : (moveElements d.store xs.length 0 d.length).length = d.store.length :=
      length_moveElements (by omega)
    have htl : (blit (moveElements d.store xs.length 0 d.length) 0 (xs.map some)).length =
        d.store.length := by
      rw [length_blit (by simp; omega), hml]
    refine ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩,
      by show d.length + xs.length ≤ (blit _ _ _).length; omega, ?_⟩
    have hspl : (specUnshift d.elems xs).length = d.length + xs.length := by
      simp [specUnshift, hel]
      omega
    apply eq_append_replicate (by dsimp only; omega)
    intro j hj
    dsimp only at hj
    rw [htl] at hj
    rw [getD_spec]
    by_cases h1 : j < xs.length
    · rw [ite_eq_left h1, getElem?_items (by omega) h1]
    · rw [ite_eq_right h1, getElem?_blit (by simp; omega), ite_eq_right (by omega),
        ite_eq_right (by simp; omega), getElem?_moveElements (by omega) (by omega)]
      by_cases h2 : xs.length ≤ j ∧ j < xs.length + d.length
      · rw [ite_eq_left h2, getElem?_store hsl hl (by omega)]
        congr 3
        omega
      · rw [ite_eq_right h2, getElem?_store hsl hl (by omega), List.getD_eq_getElem?_getD,
          List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
          List.getElem?_eq_none (by omega)]

theorem unshift_cases {c : Config} {m : MapInfo} {a : JSArr} {xs : List Val} (hw : a.WF) :
    unshift c m a xs = .slow ∨ unshift c m a xs = .abort ∨
      ∃ d, a.fast = true ∧ ensureWritableChecked c a = .ok (ensureWritable a) ∧
        matchKind c (ensureWritable a) xs = .ok d ∧ Matched (ensureWritable a) d xs ∧
        unshift c m a xs = (if xs = [] then .done d d.length else addArguments c d xs) := by
  have hew := ensureWritable_wf hw
  unfold unshift
  cases hf : a.fast
  · left
    rfl
  have hk : (ensureWritable a).kind.isFast = true := by
    rw [ensureWritable_kind]
    exact hw.forRead_fast (hw.fast_forRead hf)
  rcases ensureWritableChecked_cases c a with h | h
  · right
    left
    rw [h]
    rfl
  rw [ite_eq_right (by decide), h, Res.ok_then]
  split
  · left
    rfl
  obtain ⟨hnu, hprops⟩ := matchKind_spec (c := c) (xs := xs) hew hk
  cases hm : matchKind c (ensureWritable a) xs with
  | ok d => exact Or.inr (Or.inr ⟨d, rfl, rfl, rfl, hprops d hm, rfl⟩)
  | ub => exact absurd hm hnu
  | abort =>
    right
    left
    rfl

theorem unshift_ne_ub {c : Config} {m : MapInfo} {a : JSArr} {xs : List Val} (hw : a.WF) :
    unshift c m a xs ≠ .ub := by
  have hew := ensureWritable_wf hw
  rcases unshift_cases (c := c) (m := m) (xs := xs) hw with h | h | ⟨d, _, _, _, hmd, h⟩ <;> rw [h]
  · nofun
  · nofun
  split
  · nofun
  have hl : d.length ≤ d.store.length := by
    rw [hmd.length_eq, hmd.store_eq]
    exact hew.length_le
  rcases addArguments_spec (c := c) hl (hmd.cow_false (ensureWritable_cow a)) hmd.fits.double with
    ⟨h', _⟩ | ⟨d', h', _⟩ <;> rw [h'] <;> nofun

theorem unshift_ne_abort {c : Config} {m : MapInfo} {a : JSArr} {xs : List Val} (hw : a.WF)
    (hcap : a.store.length ≤ c.maxLen) (hc : c.maxLen ≤ c.smiMax) : unshift c m a xs ≠ .abort := by
  have hew := ensureWritable_wf hw
  have hecap : (ensureWritable a).store.length ≤ c.maxLen :=
    Nat.le_trans (ensureWritable_store_length a) hcap
  unfold unshift
  split
  · nofun
  rw [ensureWritableChecked_ok hw hcap hc, Res.ok_then]
  split
  · nofun
  rename_i hf _
  have hk : (ensureWritable a).kind.isFast = true := by
    rw [ensureWritable_kind]
    exact hw.forRead_fast (hw.fast_forRead (by simpa using hf))
  obtain ⟨d, hd⟩ := matchKind_ok (xs := xs) hecap
  have hmd := (matchKind_spec (c := c) (xs := xs) hew hk).2 d hd
  rw [hd, Res.ok_then]
  split
  · nofun
  have hl : d.length ≤ d.store.length := by
    rw [hmd.length_eq, hmd.store_eq]
    exact hew.length_le
  rcases addArguments_spec (c := c) hl (hmd.cow_false (ensureWritable_cow a)) hmd.fits.double with
    ⟨h', _⟩ | ⟨d', h', _⟩ <;> rw [h'] <;> nofun

theorem unshift_done {c : Config} {m : MapInfo} {a a' : JSArr} {xs : List Val} {r : Nat}
    (hw : a.WF) (hsl : a.SlackHoles) (h : unshift c m a xs = .done a' r) :
    a'.WF ∧ a'.SlackHoles ∧ a'.cow = false ∧ a'.length = a.length + xs.length ∧
      a'.elems = specUnshift a.elems xs ∧ r = a.length + xs.length := by
  have hew := ensureWritable_wf hw
  have hesl := ensureWritable_slack hsl
  rcases unshift_cases (c := c) (m := m) (xs := xs) hw with h' | h' | ⟨d, hf, _, _, hmd, h'⟩ <;>
    rw [h'] at h
  · cases h
  · cases h
  have hdl : d.length = a.length := by rw [hmd.length_eq, ensureWritable_length]
  have hdel : d.elems = a.elems := by
    rw [← ensureWritable_elems a]
    simp only [JSArr.elems, hmd.store_eq, hmd.length_eq]
  have hdsl : d.SlackHoles := by
    intro x hx
    rw [hmd.store_eq, hmd.length_eq] at hx
    exact hesl x hx
  have hl : d.length ≤ d.store.length := by
    rw [hmd.length_eq, hmd.store_eq]
    exact hew.length_le
  have hcw : d.cow = false := hmd.cow_false (ensureWritable_cow a)
  have hkf := hmd.fits
  rw [ensureWritable_kind] at hkf
  have hflags := ensureWritable_flags a
  split at h
  · rename_i h0
    subst h0
    cases h
    refine ⟨⟨hl, ?_, ?_, ?_, ?_, fun hc => by rw [hcw] at hc; cases hc⟩, hdsl, hcw, by simp [hdl],
      by rw [hdel]; rfl, by simp [hdl]⟩
    · intro x hx
      rw [hdel] at hx
      exact hkf.general x (hw.kind_ok x hx)
    · intro _
      exact hkf.fast
    · intro hfd
      rw [hmd.forRead_eq, hflags.1]
      exact hw.fast_forRead (by rw [← hflags.2.1, ← hmd.fast_eq]; exact hfd)
    · intro hfc
      rw [hmd.fast_eq, hflags.2.1]
      exact hw.forCopy_fast (by rw [← hflags.2.2, ← hmd.forCopy_eq]; exact hfc)
  rcases addArguments_spec (c := c) hl hcw hkf.double with ⟨h', _⟩ | ⟨d', h', hadd⟩ <;>
    rw [h'] at h
  · cases h
  cases h
  have had := hadd hdsl
  have hl' : a'.length = (specUnshift d.elems xs).length := by
    rw [had.length_eq]
    simp [specUnshift, JSArr.elems_length (show d.WF from ⟨hl, fun x hx => by
      rw [hdel] at hx
      exact hkf.general x (hw.kind_ok x hx), fun _ => hkf.fast, fun hfd => by
      rw [hmd.forRead_eq, hflags.1]
      exact hw.fast_forRead (by rw [← hflags.2.1, ← hmd.fast_eq]; exact hfd), fun hfc => by
      rw [hmd.fast_eq, hflags.2.1]
      exact hw.forCopy_fast (by rw [← hflags.2.2, ← hmd.forCopy_eq]; exact hfc),
      fun hc => by rw [hcw] at hc; cases hc⟩)]
    omega
  obtain ⟨he', hs', _⟩ := elems_slack_of_store had.store_eq hl'
  refine ⟨⟨had.len_le, ?_, ?_, ?_, ?_, fun hc => by rw [had.cow_eq] at hc; cases hc⟩, hs',
    had.cow_eq, by rw [had.length_eq, hdl], by rw [he', hdel], by rw [hdl]⟩
  · intro x hx
    rw [he'] at hx
    rw [had.kind_eq]
    unfold specUnshift at hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact hkf.items e he
    · rw [hdel] at hx
      exact hkf.general x (hw.kind_ok x hx)
  · intro _
    rw [had.kind_eq]
    exact hkf.fast
  · intro hfd
    rw [had.flags.1, hmd.forRead_eq, hflags.1]
    exact hw.fast_forRead (by rw [← hflags.2.1, ← hmd.fast_eq, ← had.flags.2.1]; exact hfd)
  · intro hfc
    rw [had.flags.2.1, hmd.fast_eq, hflags.2.1]
    exact hw.forCopy_fast (by rw [← hflags.2.2, ← hmd.forCopy_eq, ← had.flags.2.2]; exact hfc)

theorem unshift_throws {c : Config} {m : MapInfo} {a : JSArr} {xs : List Val} (hw : a.WF)
    (h : unshift c m a xs = .throws) :
    (ensureWritable a).store.length < a.length + xs.length ∧
      c.maxLen < a.length + xs.length + 16 := by
  have hew := ensureWritable_wf hw
  rcases unshift_cases (c := c) (m := m) (xs := xs) hw with h' | h' | ⟨d, _, _, _, hmd, h'⟩ <;>
    rw [h'] at h
  · cases h
  · cases h
  split at h
  · cases h
  have hl : d.length ≤ d.store.length := by
    rw [hmd.length_eq, hmd.store_eq]
    exact hew.length_le
  rcases addArguments_spec (c := c) hl (hmd.cow_false (ensureWritable_cow a)) hmd.fits.double with
    ⟨_, hg, hcap⟩ | ⟨d', h', _⟩
  · have hst := ensureWritable_store_length a
    have hel := ensureWritable_length a
    rw [hmd.store_eq, hmd.length_eq, hel] at hg
    rw [hmd.length_eq, hel] at hcap
    unfold newElementsCapacity at hcap
    split at hcap <;> omega
  · rw [h'] at h
    cases h

theorem unshift_handles {c : Config} {m : MapInfo} {a : JSArr} {xs : List Val} (hw : a.WF)
    (hcap : a.store.length ≤ c.maxLen) (hc : c.maxLen ≤ c.smiMax) (hf : a.fast = true)
    (hm : m.extensible = true ∧ m.lengthWritable = true)
    (hsize : a.length + xs.length + 16 ≤ c.maxLen) : ∃ a' r, unshift c m a xs = .done a' r := by
  have hew := ensureWritable_wf hw
  have hecap : (ensureWritable a).store.length ≤ c.maxLen :=
    Nat.le_trans (ensureWritable_store_length a) hcap
  have hk : (ensureWritable a).kind.isFast = true := by
    rw [ensureWritable_kind]
    exact hw.forRead_fast (hw.fast_forRead hf)
  unfold unshift
  rw [ite_eq_right (by simp [hf]), ensureWritableChecked_ok hw hcap hc, Res.ok_then,
    ite_eq_right (by simp [hm.1, hm.2])]
  obtain ⟨d, hd⟩ := matchKind_ok (xs := xs) hecap
  have hmd := (matchKind_spec (c := c) (xs := xs) hew hk).2 d hd
  rw [hd, Res.ok_then]
  split
  · exact ⟨_, _, rfl⟩
  have hl : d.length ≤ d.store.length := by
    rw [hmd.length_eq, hmd.store_eq]
    exact hew.length_le
  rcases addArguments_spec (c := c) hl (hmd.cow_false (ensureWritable_cow a)) hmd.fits.double with
    ⟨_, _, hcap'⟩ | ⟨d', h', _⟩
  · rw [hmd.length_eq, ensureWritable_length] at hcap'
    unfold newElementsCapacity at hcap'
    split at hcap' <;> omega
  · exact ⟨_, _, h'⟩

end ArrayUnshift
