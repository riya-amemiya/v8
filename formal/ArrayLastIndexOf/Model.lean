import Torque

namespace ArrayLastIndexOf

open Torque

inductive ExtInt where
  | fin (n : Int)
  | posInf
  | negInf
  deriving DecidableEq, Repr

structure Cmp where
  seq : Val → Val → Bool
  isNaN : Val → Bool

structure Cmp.OK (c : Cmp) : Prop where
  nan_ne : ∀ s e, c.isNaN s = true → c.seq s e = false
  number : ∀ s e, c.seq s e = true → e.isNumber = true → s.isNumber = true
  undef : ∀ s e, c.seq s e = true → e = .undef → s = .undef
  undef_self : c.seq .undef .undef = true

def fromIndex (len : Nat) : Option ExtInt → ExtInt
  | none => .fin ((len : Int) - 1)
  | some .negInf => .negInf
  | some .posInf => .fin ((len : Int) - 1)
  | some (.fin n) => if 0 ≤ n then .fin (min n ((len : Int) - 1)) else .fin ((len : Int) + n)

def specFrom (len : Nat) (n : ExtInt) : Option Int :=
  match n with
  | .negInf => none
  | .posInf => some ((len : Int) - 1)
  | .fin n => if 0 ≤ n then some (min n ((len : Int) - 1)) else some ((len : Int) + n)

def scanDown (test : Option Val → Bool) (get : Nat → Option (Option Val)) : Nat → Option Int
  | 0 =>
    match get 0 with
    | none => none
    | some x => if test x then some 0 else some (-1)
  | k + 1 =>
    match get (k + 1) with
    | none => none
    | some x => if test x then some ((k : Int) + 1) else scanDown test get k

def present (c : Cmp) (s : Val) : Option Val → Bool
  | none => false
  | some e => c.seq s e

def specScan (c : Cmp) (s : Val) (elems : List (Option Val)) (k : Int) : Int :=
  if k < 0 then -1
  else (scanDown (present c s) (fun i => some (elems.getD i none)) k.toNat).getD (-1)

def specLastIndexOf (c : Cmp) (s : Val) (len : Nat) (arg : Option ExtInt)
    (elems : List (Option Val)) : Int :=
  if len = 0 then -1
  else
    match arg with
    | some n =>
      match specFrom len n with
      | none => -1
      | some k => specScan c s elems k
    | none => specScan c s elems ((len : Int) - 1)

inductive Result where
  | done (r : Int)
  | generic (k : ExtInt)
  | fatal
  deriving Repr

def clampFrom (fromK : Int) (elementsLen : Nat) : Int :=
  if (elementsLen : Int) ≤ fromK then (elementsLen : Int) - 1 else fromK

def scanStore (test : Option Val → Bool) (store : List (Option Val)) (k : Int) : Result :=
  if k < 0 then .done (-1)
  else
    match scanDown test (fun i => store[i]?) k.toNat with
    | none => .fatal
    | some r => .done r

def fastLastIndexOf (c : Cmp) (smiMax : Nat) (a : JSArr) (s : Val) (k : ExtInt) : Result :=
  match k with
  | .fin fromK =>
    if a.forRead = false then .generic k
    else if a.length = 0 then .done (-1)
    else if fromK < -((smiMax : Int) + 1) ∨ (smiMax : Int) < fromK then .generic k
    else if a.kind.isDouble then
      if s.isNumber ∧ c.isNaN s = true then .done (-1)
      else if s.isNumber ∨ s = .undef then
        scanStore (present c s) a.store (clampFrom fromK a.store.length)
      else .done (-1)
    else if s.isNumber ∧ c.isNaN s = true then .done (-1)
    else scanStore (present c s) a.store (clampFrom fromK a.store.length)
  | _ => .generic k

def lastIndexOf (c : Cmp) (smiMax : Nat) (len : Nat) (arg : Option ExtInt) (a : JSArr)
    (s : Val) : Result :=
  if len = 0 then .done (-1) else fastLastIndexOf c smiMax a s (fromIndex len arg)

end ArrayLastIndexOf
