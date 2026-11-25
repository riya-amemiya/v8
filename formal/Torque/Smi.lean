namespace Torque

structure SmiRepr where
  shift : Nat
  width : Nat

def SmiRepr.compressed : SmiRepr := ⟨1, 32⟩

def SmiRepr.full : SmiRepr := ⟨32, 64⟩

def SmiRepr.max (r : SmiRepr) : Nat := 2 ^ (r.width - r.shift - 1) - 1

def SmiRepr.isSmi (r : SmiRepr) (n : Int) : Bool :=
  decide (-(r.max : Int) - 1 ≤ n ∧ n ≤ r.max)

def SmiRepr.word (r : SmiRepr) : Int → Nat
  | .ofNat m => m * 2 ^ r.shift % 2 ^ r.width
  | .negSucc m => (2 ^ r.width - (m + 1) * 2 ^ r.shift % 2 ^ r.width) % 2 ^ r.width

def SmiRepr.add (r : SmiRepr) (a b : Int) : Nat := (r.word a + r.word b) % 2 ^ r.width

def SmiRepr.above (x y : Nat) : Bool := decide (y < x)

def SmiRepr.signed (r : SmiRepr) (x : Nat) : Int :=
  if x < 2 ^ (r.width - 1) then x else (x : Int) - 2 ^ r.width

def SmiRepr.greaterThan (r : SmiRepr) (x y : Nat) : Bool := decide (r.signed y < r.signed x)

theorem SmiRepr.mul_lt {r : SmiRepr} (hr : r.shift < r.width) {n : Nat}
    (hn : n < 2 * 2 ^ (r.width - r.shift - 1)) : n * 2 ^ r.shift < 2 ^ r.width := by
  obtain ⟨k, hk⟩ : ∃ k, r.width = k + 1 + r.shift := ⟨r.width - r.shift - 1, by omega⟩
  have hk' : r.width - r.shift - 1 = k := by omega
  rw [hk', ← Nat.pow_succ'] at hn
  rw [hk, Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right hn (Nat.two_pow_pos _)

theorem SmiRepr.word_natCast {r : SmiRepr} (hr : r.shift < r.width) {n : Nat} (hn : n ≤ r.max) :
    r.word n = n * 2 ^ r.shift := by
  have hpos : 0 < 2 ^ (r.width - r.shift - 1) := Nat.two_pow_pos _
  have : n < 2 * 2 ^ (r.width - r.shift - 1) := by
    unfold SmiRepr.max at hn
    omega
  exact Nat.mod_eq_of_lt (SmiRepr.mul_lt hr this)

theorem SmiRepr.add_natCast {r : SmiRepr} (hr : r.shift < r.width) {a b : Nat}
    (ha : a ≤ r.max) (hb : b ≤ r.max) : r.add a b = (a + b) * 2 ^ r.shift := by
  have hpos : 0 < 2 ^ (r.width - r.shift - 1) := Nat.two_pow_pos _
  have : a + b < 2 * 2 ^ (r.width - r.shift - 1) := by
    unfold SmiRepr.max at ha hb
    omega
  unfold SmiRepr.add
  rw [SmiRepr.word_natCast hr ha, SmiRepr.word_natCast hr hb, ← Nat.add_mul]
  exact Nat.mod_eq_of_lt (SmiRepr.mul_lt hr this)

theorem SmiRepr.above_add_iff {r : SmiRepr} (hr : r.shift < r.width) {a b l : Nat}
    (ha : a ≤ r.max) (hb : b ≤ r.max) (hl : l ≤ r.max) :
    SmiRepr.above (r.add a b) (r.word l) = true ↔ l < a + b := by
  rw [SmiRepr.add_natCast hr ha hb, SmiRepr.word_natCast hr hl]
  simp only [SmiRepr.above, decide_eq_true_eq]
  exact Nat.mul_lt_mul_right (Nat.two_pow_pos _)

end Torque
