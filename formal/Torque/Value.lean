namespace Torque

inductive Val where
  | smi (n : Int)
  | num (n : Nat)
  | arr (p : Nat)
  | proxy
  | undef
  | other
  deriving DecidableEq, Repr

namespace Val

def isSmi : Val → Bool
  | smi _ => true
  | _ => false

def isNumber : Val → Bool
  | smi _ => true
  | num _ => true
  | _ => false

end Val

theorem not_arr_of_isNumber {v : Val} (h : v.isNumber = true) : ∀ p, v ≠ .arr p := by
  intro p hp
  subst hp
  simp [Val.isNumber] at h

theorem isNumber_of_isSmi {v : Val} (h : v.isSmi = true) : v.isNumber = true := by
  cases v <;> simp_all [Val.isSmi, Val.isNumber]

end Torque
