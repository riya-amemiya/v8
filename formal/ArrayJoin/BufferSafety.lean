import ArrayJoin.Cycle

namespace ArrayJoin

def ChunkOK (b : Buf) : Prop :=
  1 ≤ b.cap ∧ b.cur.length + 1 ≤ b.cap ∧ (∀ p ∈ b.full, p.2.length + 1 = p.1) ∧
    (b.cur = [] → b.full = [])

def fold (sl : Nat) (sep : List Nat) (xs : List Item) : Option WS := xs.foldlM (wItem sl sep) WS.init

def LastOK (sep : List Nat) (b : Buf) (C : List Nat) (s : Str) : Prop :=
  s.chars ≠ [] ∧ ∃ pre X n, C = X ++ s.chars ++ reps sep s.chars n ∧
    (∀ sl, C.length ≤ sl → fold sl sep (pre ++ [.str s]) = some ⟨X ++ s.chars, 1, some s⟩) ∧
    ((n = 0 ∧ b.flat = pre ++ [.str s] ∧ b.cur.getLast? = some (.str s)) ∨
      (0 < n ∧ b.flat = pre ++ [.str s, .rep n] ∧ b.cur.getLast? = some (.rep n)))

structure Inv (l : Limits) (sep : List Nat) (b : Buf) (C : List Nat) : Prop where
  chunk : ChunkOK b
  total : b.total = C.length
  bound : b.total ≤ l.strMax
  empty : b.cur = [] → C = [] ∧ b.last = none
  write : ∀ sl, C.length ≤ sl → ∃ w, fold sl sep b.flat = some w ∧ w.out = C ∧
    w.numSep = (if b.cur = [] then 0 else 1)
  last : ∀ s, b.last = some s → LastOK sep b C s

theorem fold_snoc (sl : Nat) (sep : List Nat) (xs : List Item) (x : Item) :
    fold sl sep (xs ++ [x]) = (fold sl sep xs).bind fun w => wItem sl sep w x := by
  simp only [fold, List.foldlM_append, List.foldlM_cons, List.foldlM_nil]
  cases fold sl sep xs <;> simp <;> rfl

theorem sepRun_one (sep : List Nat) : sepRun sep 1 = sep := by simp [sepRun]

theorem sepRun_succ (sep : List Nat) (n : Nat) : sepRun sep (n + 1) = sepRun sep n ++ sep := by
  simp [sepRun, List.replicate_succ']

theorem sepRun_nil {sep : List Nat} {n : Nat} (h : n = 0 ∨ sep.length = 0) : sepRun sep n = [] := by
  rcases h with h | h
  · subst h
    rfl
  · rw [List.eq_nil_of_length_eq_zero h]
    simp [sepRun]

theorem sepRun_length (sep : List Nat) (n : Nat) : (sepRun sep n).length = n * sep.length := by
  induction n with
  | zero => simp [sepRun]
  | succ n ih => rw [sepRun_succ, List.length_append, ih, Nat.succ_mul]

theorem reps_succ' (sep s : List Nat) (n : Nat) :
    reps sep s (n + 1) = reps sep s n ++ (sep ++ s) := by
  simp [reps, List.replicate_succ']

theorem wItem_str_zero {sl : Nat} {sep o : List Nat} {last : Option Str} {s : Str}
    (h : o.length + s.len ≤ sl) :
    wItem sl sep ⟨o, 0, last⟩ (.str s) = some ⟨o ++ s.chars, 1, some s⟩ := by
  simp only [wItem, writeSeps]
  rw [ite_eq_right (by omega)]
  simp [h]

theorem wItem_str_one {sl : Nat} {sep o : List Nat} {last : Option Str} {s : Str}
    (h : o.length + sep.length + s.len ≤ sl) :
    wItem sl sep ⟨o, 1, last⟩ (.str s) = some ⟨o ++ sep ++ s.chars, 1, some s⟩ := by
  obtain ⟨ns, hw⟩ := writeSeps_one (sl := sl) (sep := sep) (o := o) (last := last) (by omega)
  simp only [wItem, hw, Option.bind]
  rw [ite_eq_left (by simp; omega)]

theorem wItem_seps {sl : Nat} {sep o : List Nat} {ns : Nat} {last : Option Str} {n : Nat}
    (hn : 0 < n) (hs : 0 < sep.length) (h : o.length + n * sep.length ≤ sl) :
    wItem sl sep ⟨o, ns, last⟩ (.seps n) = some ⟨o ++ sepRun sep n, 0, none⟩ := by
  simp only [wItem, writeSeps]
  rw [ite_eq_left hn]
  dsimp only
  rw [ite_eq_left ⟨hn, hs⟩, ite_eq_left h]
  rfl

theorem appendToChunk_spec {l : Limits} (hl : l.OK) {b : Buf} (hc : ChunkOK b) (x : Item) :
    ∃ b', appendToChunk l b x = .ok b' ∧ ChunkOK b' ∧ b'.flat = b.flat ++ [x] ∧
      b'.cur.getLast? = some x ∧ b'.total = b.total ∧ b'.last = b.last ∧ b'.cur ≠ [] := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  unfold appendToChunk
  by_cases h : b.cur.length + 1 < b.cap
  · rw [ite_eq_left h]
    refine ⟨_, rfl, ⟨h1, by simp; omega, h3, by simp⟩, ?_, by simp, rfl, rfl, by simp⟩
    simp [Buf.flat]
  · rw [ite_eq_right h, ite_eq_right (by omega), ite_eq_right (by have := hl.chunk; simp [grow]; omega)]
    refine ⟨_, rfl, ⟨by have := hl.chunk; simp [grow]; omega, by have := hl.chunk; simp [grow]; omega,
      ?_, by simp⟩, ?_, by simp, rfl, rfl, by simp⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact h3 p hp
      · simp at hp
        subst hp
        dsimp only
        omega
    · simp [Buf.flat]

theorem flat_replace_last {b : Buf} (h : b.cur ≠ []) (y : Item) :
    ({ b with cur := b.cur.dropLast ++ [y] } : Buf).flat = b.flat.dropLast ++ [y] := by
  simp only [Buf.flat]
  rw [List.dropLast_append_of_ne_nil h, List.append_assoc]

theorem readChunk_eq {sl : Nat} {sep : List Nat} {cap : Nat} {items : List Item} (w : WS)
    (h : items.length + 1 ≤ cap) :
    readChunk sl sep cap (items.length + 1) items w = items.foldlM (wItem sl sep) w := by
  unfold readChunk
  rw [ite_eq_left ⟨by omega, h⟩, Nat.add_sub_cancel, slots, List.take_left]

theorem writeChunks_eq_aux {sl : Nat} {sep : List Nat} {cap : Nat} {cur : List Item}
    (hcur : cur.length + 1 ≤ cap) :
    ∀ (full : List (Nat × List Item)) (w : WS), (∀ p ∈ full, p.2.length + 1 = p.1) →
      writeChunks sl sep (cur.length + 1) (full ++ [(cap, cur)]) w =
        ((full.map Prod.snd).flatten ++ cur).foldlM (wItem sl sep) w
  | [], w, _ => by
    simp only [List.nil_append, writeChunks, List.map_nil, List.flatten_nil]
    exact readChunk_eq w hcur
  | p :: full, w, hp => by
    have hp0 := hp p (by simp)
    match hrest : full ++ [(cap, cur)] with
    | [] => simp at hrest
    | c :: cs =>
      rw [List.cons_append, hrest, writeChunks]
      have ih := writeChunks_eq_aux (sl := sl) (sep := sep) hcur full
      rw [List.map_cons, List.flatten_cons, List.append_assoc, List.foldlM_append]
      obtain ⟨c0, items⟩ := p
      dsimp only at hp0 ⊢
      rw [← hp0, readChunk_eq w (by omega)]
      cases items.foldlM (wItem sl sep) w with
      | none => rfl
      | some w' =>
        simp only [Option.bind, bind, Option.bind]
        rw [← hrest]
        exact ih w' (fun q hq => hp q (by simp [hq]))

theorem writeChunks_eq {sl : Nat} {sep : List Nat} {b : Buf} (hc : ChunkOK b) (w : WS) :
    writeChunks sl sep (b.cur.length + 1) b.chunks w = b.flat.foldlM (wItem sl sep) w :=
  writeChunks_eq_aux hc.2.1 b.full w hc.2.2.1

theorem inv_new {l : Limits} (hl : l.OK) (sep : List Nat) (len : Nat) :
    Inv l sep (newBuffer l len) [] where
  chunk := by
    refine ⟨?_, ?_, by simp [newBuffer], by simp [newBuffer]⟩ <;>
    · simp only [newBuffer]
      have := hl.chunk
      split <;> simp <;> omega
  total := rfl
  bound := Nat.zero_le _
  empty := fun _ => ⟨rfl, rfl⟩
  write := fun _ _ => ⟨WS.init, rfl, rfl, by simp [newBuffer, WS.init]⟩
  last := fun s h => by simp [newBuffer] at h

theorem append_case {l : Limits} (hl : l.OK) {sep : List Nat} {b0 : Buf} (hc : ChunkOK b0)
    {X : List Nat} {s : Str} (hs : s.chars ≠ []) (hb : (X ++ s.chars).length ≤ l.strMax)
    (hf : ∀ sl, (X ++ s.chars).length ≤ sl →
      fold sl sep (b0.flat ++ [.str s]) = some ⟨X ++ s.chars, 1, some s⟩) :
    ∃ b', ((appendToChunk l { b0 with total := (X ++ s.chars).length } (.str s)).bind
        fun b2 => .ok { b2 with last := some s }) = .ok b' ∧
      Inv l sep b' (X ++ s.chars) ∧ b'.last = some s ∧ b'.cur ≠ [] := by
  obtain ⟨b2, he, hc2, hflat, hlast, htot, _, hne⟩ :=
    appendToChunk_spec hl (b := { b0 with total := (X ++ s.chars).length }) hc (.str s)
  rw [he]
  have hf2 : ({ b2 with last := some s } : Buf).flat = b0.flat ++ [.str s] := hflat
  refine ⟨_, rfl, ⟨hc2, htot, by rw [htot]; exact hb, fun h => absurd h hne,
    fun sl hsl => ⟨_, by rw [hf2]; exact hf sl hsl, rfl, by simp [hne]⟩, ?_⟩, rfl, hne⟩
  intro s' hs'
  simp only [Option.some.injEq] at hs'
  subst hs'
  exact ⟨hs, b0.flat, X, 0, by simp [reps], fun sl hsl => hf sl hsl, Or.inl ⟨rfl, hf2, hlast⟩⟩

theorem repeat_case {l : Limits} (hl : l.OK) {sep : List Nat} {b : Buf} {C : List Nat} {s : Str}
    (hi : Inv l sep b C) (hlast : b.last = some s) (hb : (C ++ sep ++ s.chars).length ≤ l.strMax) :
    ∃ b', repeatLast l { b with total := (C ++ sep ++ s.chars).length } = .ok b' ∧
      Inv l sep b' (C ++ sep ++ s.chars) ∧ b'.last = some s ∧ b'.cur ≠ [] := by
  obtain ⟨hs, pre, X, n0, hC, hpre, hcase⟩ := hi.last s hlast
  have hC' : C ++ sep ++ s.chars = X ++ s.chars ++ reps sep s.chars (n0 + 1) := by
    rw [hC, reps_succ']
    simp
  have hlenC : C.length ≤ (C ++ sep ++ s.chars).length := by simp
  have hslen : 0 < s.chars.length := Nat.pos_of_ne_zero (fun h => hs (List.eq_nil_of_length_eq_zero h))
  have hwrite : ∀ sl, (C ++ sep ++ s.chars).length ≤ sl →
      fold sl sep (pre ++ [.str s, .rep (n0 + 1)]) =
        some ⟨C ++ sep ++ s.chars, 1, none⟩ := by
    intro sl hsl
    have : pre ++ [.str s, .rep (n0 + 1)] = (pre ++ [.str s]) ++ [.rep (n0 + 1)] := by simp
    rw [this, fold_snoc, hpre sl (by omega), Option.bind, hC']
    exact rep_closed hs (by omega) (by rw [← hC']; exact hsl)
  have hlast' : ∀ b' : Buf, b'.last = some s → b'.flat = pre ++ [.str s, .rep (n0 + 1)] →
      b'.cur.getLast? = some (.rep (n0 + 1)) → LastOK sep b' (C ++ sep ++ s.chars) s := by
    intro b' _ hf hg
    exact ⟨hs, pre, X, n0 + 1, hC', fun sl hsl => hpre sl (by omega), Or.inr ⟨by omega, hf, hg⟩⟩
  rcases hcase with ⟨rfl, hflat, hget⟩ | ⟨hn0, hflat, hget⟩
  · unfold repeatLast
    simp only [hget]
    obtain ⟨b2, he, hc2, hflat2, hlast2, htot, hl2, hne⟩ :=
      appendToChunk_spec hl (b := { b with total := (C ++ sep ++ s.chars).length }) hi.chunk (.rep 1)
    rw [he]
    have hf2 : b2.flat = pre ++ [.str s, .rep (0 + 1)] := by
      rw [hflat2]
      show b.flat ++ [Item.rep 1] = _
      rw [hflat]
      simp
    refine ⟨b2, rfl, ⟨hc2, by simpa using htot, by simpa [htot] using hb,
      fun h => absurd h hne, fun sl hsl => ⟨_, by rw [hf2]; exact hwrite sl hsl, rfl, by simp [hne]⟩,
      ?_⟩, by simpa [hl2] using hlast, hne⟩
    intro s' hs'
    rw [hl2] at hs'
    simp only [hlast, Option.some.injEq] at hs'
    subst hs'
    exact hlast' b2 (by simpa [hl2] using hlast) hf2 hlast2
  · unfold repeatLast
    simp only [hget]
    have hcur : b.cur ≠ [] := by
      intro h
      rw [h] at hget
      simp at hget
    have hsmi : n0 + 1 + 1 ≤ l.smiMax := by
      have h1 := hl.smi
      have h2 : (C ++ sep ++ s.chars).length = X.length + s.chars.length +
          (n0 + 1) * (sep.length + s.chars.length) := by
        rw [hC']
        simp [reps_length]
        omega
      have h3 := Nat.le_mul_of_pos_right (n0 + 1) (show 0 < sep.length + s.chars.length by omega)
      omega
    rw [ite_eq_left (by omega)]
    have hf2 : ({ { b with total := (C ++ sep ++ s.chars).length } with
        cur := b.cur.dropLast ++ [.rep (n0 + 1)] } : Buf).flat = pre ++ [.str s, .rep (n0 + 1)] := by
      rw [flat_replace_last (b := { b with total := (C ++ sep ++ s.chars).length }) hcur]
      show b.flat.dropLast ++ [Item.rep (n0 + 1)] = _
      rw [hflat]
      simp
    have hcne : b.cur.dropLast ++ [Item.rep (n0 + 1)] ≠ [] := by simp
    obtain ⟨c1, c2, c3, c4⟩ := hi.chunk
    have hlen : 0 < b.cur.length := Nat.pos_of_ne_zero (fun h => hcur (List.eq_nil_of_length_eq_zero h))
    refine ⟨_, rfl, ⟨⟨c1, by show (b.cur.dropLast ++ [Item.rep (n0 + 1)]).length + 1 ≤ b.cap; rw [List.length_append, List.length_dropLast, List.length_singleton]; omega, c3,
      fun h => absurd h hcne⟩, rfl, hb, fun h => absurd h hcne,
      fun sl hsl => ⟨_, by rw [hf2]; exact hwrite sl hsl, rfl, by simp⟩, ?_⟩, hlast, hcne⟩
    intro s' hs'
    simp only [hlast, Option.some.injEq] at hs'
    subst hs'
    exact hlast' _ hlast hf2 (by simp)

end ArrayJoin
