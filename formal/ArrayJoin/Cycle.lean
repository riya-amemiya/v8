import ArrayJoin.Buffer

namespace ArrayJoin

def cyc (p : List Nat) (m : Nat) : List Nat := (List.range m).map fun i => p.getD (i % p.length) 0

theorem cyc_length (p : List Nat) (m : Nat) : (cyc p m).length = m := by simp [cyc]

theorem cyc_get (p : List Nat) (m i : Nat) (h : i < (cyc p m).length) :
    (cyc p m)[i] = p.getD (i % p.length) 0 := by
  simp [cyc]

theorem cyc_self {p : List Nat} : cyc p p.length = p := by
  apply List.ext_getElem (cyc_length p p.length)
  intro i h1 h2
  rw [cyc_get, Nat.mod_eq_of_lt h2]
  simp [List.getD_eq_getElem?_getD, h2]

theorem cyc_add {p : List Nat} {a : Nat} (h : p.length ∣ a) (b : Nat) :
    cyc p (a + b) = cyc p a ++ cyc p b := by
  apply List.ext_getElem (by simp [cyc_length])
  intro i h1 h2
  rw [cyc_get]
  rw [cyc_length] at h1
  by_cases hi : i < a
  · rw [List.getElem_append_left (by rw [cyc_length]; exact hi), cyc_get]
  · rw [List.getElem_append_right (by rw [cyc_length]; omega), cyc_get]
    congr 1
    rw [cyc_length]
    obtain ⟨q, rfl⟩ := h
    have : i = p.length * q + (i - p.length * q) := by omega
    conv => lhs; rw [this]
    rw [Nat.mul_add_mod]

theorem cyc_drop_take {p : List Nat} {j t m : Nat} (h : p.length ∣ j) (hjt : j + t ≤ m) :
    ((cyc p m).drop j).take t = cyc p t := by
  apply List.ext_getElem (by simp [cyc_length]; omega)
  intro i h1 h2
  rw [List.getElem_take, List.getElem_drop, cyc_get, cyc_get]
  congr 1
  obtain ⟨q, rfl⟩ := h
  rw [Nat.mul_add_mod]

theorem cyc_take {p : List Nat} {t m : Nat} (h : t ≤ m) : (cyc p m).take t = cyc p t := by
  have := cyc_drop_take (p := p) (j := 0) (t := t) (m := m) (Nat.dvd_zero _) (by omega)
  simpa using this

theorem cyc_mul (p : List Nat) : ∀ n, cyc p (p.length * n) = (List.replicate n p).flatten
  | 0 => by simp [cyc]
  | n + 1 => by
    rw [Nat.mul_succ, Nat.add_comm, cyc_add (Nat.dvd_refl _), cyc_self, cyc_mul p n]
    rfl

theorem reps_succ (sep s : List Nat) (n : Nat) :
    reps sep s (n + 1) = sep ++ s ++ reps sep s n := by
  simp [reps, List.replicate_succ]

theorem reps_length (sep s : List Nat) : ∀ n, (reps sep s n).length = n * (sep.length + s.length)
  | 0 => by simp [reps]
  | n + 1 => by
    rw [reps_succ, List.length_append, List.length_append, reps_length sep s n, Nat.succ_mul]
    omega

theorem replicate_pair (s sep : List Nat) : ∀ n,
    (List.replicate (n + 1) (s ++ sep)).flatten = s ++ reps sep s n ++ sep
  | 0 => by simp [reps]
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, replicate_pair s sep n, reps_succ]
    simp

theorem cyc_reps (s sep : List Nat) (n : Nat) :
    cyc (s ++ sep) (s.length + (s.length + sep.length) * n) = s ++ reps sep s n := by
  have hT : s.length + (s.length + sep.length) * n ≤ (s ++ sep).length * (n + 1) := by
    rw [List.length_append, Nat.mul_succ]
    omega
  rw [← cyc_take hT, cyc_mul, replicate_pair, List.append_assoc]
  have hl : (s ++ reps sep s n).length = s.length + (s.length + sep.length) * n := by
    rw [List.length_append, reps_length, Nat.mul_comm, Nat.add_comm sep.length]
  rw [← List.append_assoc, ← hl, List.take_left]

theorem dbl_spec {p X : List Nat} (hp : 0 < p.length) {T sl : Nat} (hT : X.length + T ≤ sl)
    (W : Nat) (hd : p.length ∣ W) (hW : 0 < W) (hle : W ≤ T) :
    ∃ W', p.length ∣ W' ∧ W' ≤ T ∧ T ≤ 2 * W' ∧
      dbl sl (X.length + T) (X ++ cyc p W) W = some (X ++ cyc p W') := by
  have hlen : (X ++ cyc p W).length = X.length + W := by simp [cyc_length]
  rw [dbl]
  by_cases h : (X ++ cyc p W).length + W < X.length + T
  · have hdrop : (X ++ cyc p W) ++ (X ++ cyc p W).drop ((X ++ cyc p W).length - W) =
        X ++ cyc p (W + W) := by
      rw [hlen, Nat.add_sub_cancel, List.drop_left, cyc_add hd, List.append_assoc]
    rw [dite_eq_left h, dite_eq_right (by omega), dite_eq_left ⟨by omega, by omega⟩, hdrop, Nat.two_mul]
    have : T - (W + W) < T - W := by omega
    exact dbl_spec hp hT (W + W) (Nat.dvd_add hd hd) (by omega) (by omega)
  · rw [dite_eq_right h]
    exact ⟨W, hd, hle, by omega, rfl⟩
termination_by T - W

theorem repTail_spec {p X : List Nat} {sepLen T sl W : Nat} (hsep : sepLen < p.length)
    (hmod : p.length ∣ T + sepLen) (hd : p.length ∣ W) (hle : W ≤ T) (h2 : T ≤ 2 * W)
    (hT : X.length + T ≤ sl) :
    repTail sl (X.length + T) sepLen (X ++ cyc p W) = some (X ++ cyc p T) := by
  have hlen : (X ++ cyc p W).length = X.length + W := by simp [cyc_length]
  obtain ⟨q, hq⟩ := hmod
  obtain ⟨w, hw⟩ := hd
  have hq2 : q ≤ 2 * w := by
    apply Nat.le_of_not_lt
    intro hlt
    have h3 : p.length * (2 * w + 1) ≤ p.length * q := Nat.mul_le_mul_left _ hlt
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm] at h3
    omega
  have h4 : p.length * q ≤ p.length * (2 * w) := Nat.mul_le_mul_left _ hq2
  rw [Nat.mul_left_comm] at h4
  unfold repTail
  rw [hlen, ite_eq_right (by omega)]
  by_cases h0 : X.length + T - (X.length + W) = 0
  · rw [ite_eq_left h0]
    have : W = T := by omega
    rw [this]
  · rw [ite_eq_right h0, ite_eq_left ⟨by omega, by omega⟩]
    have hdiv : p.length ∣ W - (T - W + sepLen) := by
      refine ⟨w - (q - w), ?_⟩
      rw [Nat.mul_sub, Nat.mul_sub, ← hw]
      omega
    have hidx : X.length + W - (X.length + T - (X.length + W)) - sepLen =
        X.length + (W - (T - W + sepLen)) := by omega
    have hrem : X.length + T - (X.length + W) = T - W := by omega
    rw [hidx, hrem, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      Nat.add_sub_cancel_left, cyc_drop_take (m := W) hdiv (by omega), List.append_assoc,
      ← cyc_add ⟨w, hw⟩, Nat.add_sub_cancel' hle]

theorem writeSeps_one {sl : Nat} {sep : List Nat} {o : List Nat} {last : Option Str}
    (h : o.length + sep.length ≤ sl) :
    ∃ ns, writeSeps sl sep ⟨o, 1, last⟩ = some ⟨o ++ sep, ns, last⟩ := by
  unfold writeSeps
  by_cases hs : 0 < sep.length
  · refine ⟨0, ?_⟩
    rw [ite_eq_left ⟨Nat.one_pos, hs⟩, ite_eq_left (by simpa using h)]
    simp [sepRun]
  · have : sep = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    refine ⟨1, ?_⟩
    rw [ite_eq_right (by simp)]
    simp

theorem rep_closed {sl : Nat} {sep X : List Nat} {s : Str} {n : Nat} (hs : s.chars ≠ [])
    (hn : 0 < n) (hsl : (X ++ s.chars ++ reps sep s.chars n).length ≤ sl) :
    wItem sl sep ⟨X ++ s.chars, 1, some s⟩ (.rep n) =
      some ⟨X ++ s.chars ++ reps sep s.chars n, 1, none⟩ := by
  have hsl' : X.length + (s.chars.length + (s.chars.length + sep.length) * n) ≤ sl := by
    rw [List.length_append, List.length_append, reps_length] at hsl
    rw [Nat.mul_comm, Nat.add_comm s.chars.length sep.length]
    omega
  have hslen : 0 < s.chars.length := Nat.pos_of_ne_zero (fun h => hs (List.eq_nil_of_length_eq_zero h))
  obtain ⟨ns, hw⟩ := writeSeps_one (sl := sl) (sep := sep) (o := X ++ s.chars) (last := some s)
    (by rw [List.length_append]; have := Nat.le_mul_of_pos_right (s.chars.length + sep.length) hn; omega)
  simp only [wItem, hw, Option.bind]
  unfold repStep
  rw [ite_eq_right (by omega)]
  dsimp only
  have hp : (s.chars ++ sep).length = s.len + sep.length := by simp [Str.len]
  have hend : (X ++ s.chars ++ sep).length + (s.len + sep.length) * n - sep.length =
      X.length + (s.chars.length + (s.chars.length + sep.length) * n) := by
    simp only [List.length_append, Str.len]
    omega
  rw [hend]
  have hX : X ++ s.chars ++ sep = X ++ cyc (s.chars ++ sep) (s.chars ++ sep).length := by
    rw [cyc_self, List.append_assoc]
  rw [hX, ← hp]
  obtain ⟨W', hd', hle', h2', hdbl⟩ := dbl_spec (p := s.chars ++ sep) (X := X)
    (by simp; omega) hsl' _ (Nat.dvd_refl _) (by simp; omega)
    (by simp only [List.length_append]; have := Nat.le_mul_of_pos_right (s.chars.length + sep.length) hn; omega)
  have hlenp : (s.chars ++ sep).length = s.chars.length + sep.length := by simp
  rw [hlenp] at hdbl ⊢
  rw [hdbl, Option.bind]
  rw [repTail_spec (by simp; omega) ?_ hd' hle' h2' hsl']
  · simp only [Option.map, cyc_reps, List.append_assoc]
  · refine ⟨n + 1, ?_⟩
    rw [hlenp, Nat.mul_succ]
    omega

end ArrayJoin
