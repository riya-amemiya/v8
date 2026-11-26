import Torque

namespace ArrayAt

open Torque

inductive ExtInt where
  | fin (n : Int)
  | posInf
  | negInf
  deriving DecidableEq, Repr

structure FAdd (fadd : Int → Int → Int) : Prop where
  sign : ∀ x y, x + y < 0 → fadd x y < 0
  exact : ∀ x y, 0 ≤ x + y → x + y ≤ 2 ^ 53 → fadd x y = x + y

def convertRelativeIndex (fadd : Int → Int → Int) (index : ExtInt) (len : Nat) : Option Nat :=
  match index with
  | .posInf => none
  | .negInf => none
  | .fin n =>
    if 0 ≤ n then (if (len : Int) ≤ n then none else some n.toNat)
    else if fadd len n < 0 then none
    else if (len : Int) ≤ fadd len n then none
    else some (fadd len n).toNat

def specAt (len : Nat) (index : ExtInt) : Option Nat :=
  match index with
  | .posInf => none
  | .negInf => none
  | .fin n =>
    if (0 ≤ n → (len : Int) ≤ n) ∧ (n < 0 → (len : Int) + n < 0) then none
    else some (if 0 ≤ n then n else (len : Int) + n).toNat

end ArrayAt
