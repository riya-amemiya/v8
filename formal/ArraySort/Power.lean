import ArraySort.Stack

namespace ArraySort

open Torque

def fsc (n x : Nat) : Nat := x * 2 ^ 30 / n

def lvl (n j x : Nat) : Nat := fsc n x / 2 ^ j

def pw (n a b : Nat) : Nat := clz32 ((fsc n a % 2 ^ 32) ^^^ (fsc n b % 2 ^ 32))

theorem nodePowerValue_eq (s1 n1 n2 n : Nat) :
    nodePowerValue (s1 : Int) (n1 : Int) (n2 : Int) (n : Int) =
      (pw n (2 * s1 + n1) (2 * s1 + n1 + n1 + n2) : Int) := by
  unfold nodePowerValue pw fsc
  have e1 : (2 * (s1 : Int) + n1) * 2 ^ 30 / n = (((2 * s1 + n1) * 2 ^ 30 / n : Nat) : Int) := by
    rw [Int.natCast_ediv]
    simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow]
    rfl
  have e2 : (2 * (s1 : Int) + n1 + n1 + n2) * 2 ^ 30 / n =
      (((2 * s1 + n1 + n1 + n2) * 2 ^ 30 / n : Nat) : Int) := by
    rw [Int.natCast_ediv]
    simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow]
    rfl
  simp only [e1, e2, Int.toNat_natCast]

theorem fsc_mono {n a b : Nat} (h : a ≤ b) : fsc n a ≤ fsc n b :=
  Nat.div_le_div_right (Nat.mul_le_mul_right _ h)

theorem fsc_lt {n a : Nat} (hn : 0 < n) (ha : a < 2 * n) : fsc n a < 2 ^ 31 := by
  unfold fsc
  rw [Nat.div_lt_iff_lt_mul hn]
  have : a * 2 ^ 30 < 2 * n * 2 ^ 30 := Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos 30)
  have h2 : 2 * n * 2 ^ 30 = 2 ^ 31 * n := by
    rw [show (2 : Nat) ^ 31 = 2 * 2 ^ 30 by rfl]
    rw [Nat.mul_comm 2 n, Nat.mul_assoc, Nat.mul_comm n (2 * 2 ^ 30)]
  omega

theorem fsc_gap {n a b : Nat} (hn : 0 < n) (hn2 : n ≤ 2 ^ 31) (h : a + 2 ≤ b) : fsc n a < fsc n b := by
  unfold fsc
  have h1 : a * 2 ^ 30 + n ≤ b * 2 ^ 30 := by
    have : (a + 2) * 2 ^ 30 ≤ b * 2 ^ 30 := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul] at this
    have : 2 * 2 ^ 30 = 2 ^ 31 := rfl
    omega
  have h2 : (a * 2 ^ 30 + n) / n = a * 2 ^ 30 / n + 1 := by
    rw [Nat.add_div_right _ hn]
  have h3 : (a * 2 ^ 30 + n) / n ≤ b * 2 ^ 30 / n := Nat.div_le_div_right h1
  omega

theorem lvl_succ (n j x : Nat) : lvl n (j + 1) x = lvl n j x / 2 := by
  unfold lvl
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem lvl_up {n j j' a b : Nat} (h : lvl n j a = lvl n j b) (hj : j ≤ j') : lvl n j' a = lvl n j' b := by
  obtain ⟨d, rfl⟩ : ∃ d, j' = j + d := ⟨j' - j, by omega⟩
  induction d with
  | zero => exact h
  | succ d ih => rw [← Nat.add_assoc, lvl_succ, lvl_succ, ih (by omega)]

theorem xor_split {x y : Nat} (hxy : x ≠ y) :
    x >>> ((x ^^^ y).log2 + 1) = y >>> ((x ^^^ y).log2 + 1) ∧
      x >>> (x ^^^ y).log2 ≠ y >>> (x ^^^ y).log2 := by
  have hz : x ^^^ y ≠ 0 := by
    intro h
    apply hxy
    apply Nat.eq_of_testBit_eq
    intro i
    have := congrArg (fun z => z.testBit i) h
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all
  constructor
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
    have h1 : (x ^^^ y).testBit ((x ^^^ y).log2 + 1 + i) = false := by
      apply Nat.testBit_lt_two_pow
      have := Nat.lt_log2_self (n := x ^^^ y)
      have h2 : 2 ^ ((x ^^^ y).log2 + 1) ≤ 2 ^ ((x ^^^ y).log2 + 1 + i) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rw [Nat.testBit_xor] at h1
    cases hx : x.testBit ((x ^^^ y).log2 + 1 + i) <;> cases hy : y.testBit ((x ^^^ y).log2 + 1 + i) <;>
      simp_all
  · intro h
    have h1 := Nat.testBit_log2 hz
    have h2 := congrArg (fun z => z.testBit 0) h
    simp only [Nat.testBit_shiftRight, Nat.add_zero] at h2
    rw [Nat.testBit_xor, h2] at h1
    simp at h1

theorem pw_spec {n a b : Nat} (hn : 0 < n) (hn2 : n < 2 ^ 31) (hab : a + 2 ≤ b) (hb : b < 2 * n) :
    1 ≤ pw n a b ∧ pw n a b ≤ 31 ∧ lvl n (32 - pw n a b) a = lvl n (32 - pw n a b) b ∧
      lvl n (31 - pw n a b) a < lvl n (31 - pw n a b) b := by
  have hxa := fsc_lt (a := a) hn (by omega)
  have hxb := fsc_lt (a := b) hn hb
  have hlt := fsc_gap (a := a) (b := b) hn (by omega) hab
  have hma : fsc n a % 2 ^ 32 = fsc n a := Nat.mod_eq_of_lt (by omega)
  have hmb : fsc n b % 2 ^ 32 = fsc n b := Nat.mod_eq_of_lt (by omega)
  unfold pw
  rw [hma, hmb]
  generalize hx : fsc n a = x at *
  generalize hy : fsc n b = y at *
  have hne : x ≠ y := by omega
  have hz : x ^^^ y ≠ 0 := by
    intro h
    apply hne
    apply Nat.eq_of_testBit_eq
    intro i
    have := congrArg (fun z => z.testBit i) h
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    cases hx' : x.testBit i <;> cases hy' : y.testBit i <;> simp_all
  have hzl : x ^^^ y < 2 ^ 31 := Nat.xor_lt_two_pow hxa hxb
  have hlog : (x ^^^ y).log2 < 31 := (Nat.log2_lt hz).2 hzl
  unfold clz32
  rw [ite_eq_right hz]
  obtain ⟨h1, h2⟩ := xor_split hne
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at h1 h2
  unfold lvl
  rw [← hx, ← hy] at *
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [show 32 - (31 - (fsc n a ^^^ fsc n b).log2) = (fsc n a ^^^ fsc n b).log2 + 1 by omega]
    exact h1
  · rw [show 31 - (31 - (fsc n a ^^^ fsc n b).log2) = (fsc n a ^^^ fsc n b).log2 by omega]
    have := Nat.div_le_div_right (c := 2 ^ (fsc n a ^^^ fsc n b).log2) (Nat.le_of_lt hlt)
    omega

def PI (n : Nat) : List (Nat × Nat) → List Nat → Prop
  | [], [] => True
  | [_], [] => True
  | g0 :: g1 :: gs, p0 :: ps => p0 = pw n g1.2 g0.1 ∧ g1.2 + 2 ≤ g0.1 ∧
      lvl n (31 - p0) g0.1 = lvl n (31 - p0) g0.2 ∧ 1 ≤ p0 ∧ p0 ≤ 31 ∧
      (∀ p1, ps.head? = some p1 → p1 < p0) ∧ PI n (g1 :: gs) ps
  | _, _ => False

def Bnd (n : Nat) (G : List (Nat × Nat)) : Prop := ∀ g ∈ G, g.1 ≤ g.2 ∧ g.2 < 2 * n

theorem pi_merge {n : Nat} (hn : 0 < n) (hn2 : n < 2 ^ 31) {g0 g1 : Nat × Nat} {gs : List (Nat × Nat)}
    {p0 : Nat} {ps : List Nat} (h : PI n (g0 :: g1 :: gs) (p0 :: ps)) (hB : Bnd n (g0 :: g1 :: gs)) :
    PI n ((g1.1, g0.2) :: gs) ps ∧ Bnd n ((g1.1, g0.2) :: gs) := by
  obtain ⟨hp0, hg, hl0, hr1, hr2, hhead, hrest⟩ := h
  have hb0 := hB g0 (by simp)
  have hb1 := hB g1 (by simp)
  refine ⟨?_, ?_⟩
  · match gs, ps, hrest with
    | [], [], _ => trivial
    | g2 :: gs', p1 :: ps', hrest =>
      obtain ⟨hp1, hg1, hl1, hs1, hs2, hhead1, hrest1⟩ := hrest
      have hlt : p1 < p0 := hhead p1 rfl
      refine ⟨hp1, hg1, ?_, hs1, hs2, hhead1, hrest1⟩
      have hspec := pw_spec (a := g1.2) (b := g0.1) hn hn2 hg (by omega)
      rw [← hp0] at hspec
      have a1 : lvl n (31 - p1) g1.2 = lvl n (31 - p1) g0.1 := lvl_up hspec.2.2.1 (by omega)
      have a2 : lvl n (31 - p1) g0.1 = lvl n (31 - p1) g0.2 := lvl_up hl0 (by omega)
      exact hl1.trans (a1.trans a2)
  · intro g hgm
    simp only [List.mem_cons] at hgm
    rcases hgm with rfl | hgm
    · simp only
      omega
    · exact hB g (by simp [hgm])

theorem pi_strict {n : Nat} (hn : 0 < n) (hn2 : n < 2 ^ 31) {g0 g1 : Nat × Nat} {gs : List (Nat × Nat)}
    {p0 : Nat} {ps : List Nat} {m : Nat} (h : PI n (g0 :: g1 :: gs) (p0 :: ps)) (hB : Bnd n (g0 :: g1 :: gs))
    (hm : g0.2 + 2 ≤ m) (hm2 : m < 2 * n) (hle : p0 ≤ pw n g0.2 m) : p0 < pw n g0.2 m := by
  obtain ⟨hp0, hg, hl0, hr1, hr2, _, _⟩ := h
  have hb0 := hB g0 (by simp)
  have s1 := pw_spec (a := g1.2) (b := g0.1) hn hn2 hg (by omega)
  have s2 := pw_spec (a := g0.2) (b := m) hn hn2 hm hm2
  rw [← hp0] at s1
  refine Nat.lt_of_le_of_ne hle fun heq => ?_
  rw [← heq] at s2
  have e1 := s1.2.2.1
  have e2 := s2.2.2.1
  rw [show 32 - p0 = (31 - p0) + 1 by omega, lvl_succ, lvl_succ] at e1 e2
  have o1 := s1.2.2.2
  have o2 := s2.2.2.2
  rw [hl0] at o1 e1
  omega

theorem pi_push {n : Nat} (hn : 0 < n) (hn2 : n < 2 ^ 31) {g0 : Nat × Nat} {G : List (Nat × Nat)}
    {P : List Nat} {m : Nat} (h : PI n (g0 :: G) P) (hB : Bnd n (g0 :: G)) (hm : g0.2 + 2 ≤ m)
    (hm2 : m < 2 * n) (hhead : ∀ p0, P.head? = some p0 → p0 < pw n g0.2 m) :
    PI n ((m, m) :: g0 :: G) (pw n g0.2 m :: P) ∧ Bnd n ((m, m) :: g0 :: G) := by
  have s := pw_spec (a := g0.2) (b := m) hn hn2 hm hm2
  refine ⟨⟨rfl, hm, rfl, s.1, s.2.1, hhead, h⟩, ?_⟩
  intro g hgm
  simp only [List.mem_cons] at hgm
  rcases hgm with rfl | hgm
  · simp only
    omega
  · exact hB g (by simp [hgm])

theorem pi_length {n : Nat} : ∀ (G : List (Nat × Nat)) (P : List Nat), G ≠ [] → PI n G P →
    G.length = P.length + 1 ∧ ∀ p0, P.head? = some p0 → P.length ≤ p0
  | [_], [], _, _ => ⟨rfl, fun _ h => by simp at h⟩
  | g0 :: g1 :: gs, p0 :: ps, _, h => by
    obtain ⟨_, _, _, h1, _, hhead, hrest⟩ := h
    have ih := pi_length (g1 :: gs) ps (by simp) hrest
    refine ⟨by simp only [List.length_cons] at ih ⊢; omega, ?_⟩
    intro p hp
    simp only [List.head?_cons, Option.some.injEq] at hp
    subst hp
    cases ps with
    | nil => simp; omega
    | cons p1 ps' =>
      have := ih.2 p1 rfl
      have := hhead p1 rfl
      simp only [List.length_cons] at *
      omega
  | [], _, h, _ => absurd rfl h
  | [_], _ :: _, _, h => absurd h (by simp [PI])
  | _ :: _ :: _, [], _, h => absurd h (by simp [PI])

theorem pi_size {n : Nat} {G : List (Nat × Nat)} {P : List Nat} (hG : G ≠ []) (h : PI n G P)
    (hP : ∀ p0, P.head? = some p0 → p0 ≤ 31) : G.length ≤ 32 := by
  have := pi_length G P hG h
  cases P with
  | nil => simp at this; omega
  | cons p0 ps =>
    have h1 := this.2 p0 rfl
    have h2 := hP p0 rfl
    simp only [List.length_cons] at *
    omega

theorem pi_head_le {n : Nat} {G : List (Nat × Nat)} {P : List Nat} (h : PI n G P) :
    ∀ p0, P.head? = some p0 → p0 ≤ 31 := by
  intro p0 hp
  match G, P, h with
  | g0 :: g1 :: gs, p :: ps, h =>
    simp only [List.head?_cons, Option.some.injEq] at hp
    subst hp
    exact h.2.2.2.2.1
  | [], [], _ => simp at hp
  | [_], [], _ => simp at hp
  | _ :: _ :: _, [], _ => simp at hp
  | [], _ :: _, h => exact absurd h (by simp [PI])
  | [_], _ :: _, h => exact absurd h (by simp [PI])

end ArraySort
