import Torque

namespace ArrayFill

open Torque

structure FillConfig where
  maxLen : Nat
  maxFast : Nat
  undefinedDouble : Bool

structure Env where
  movingAllowed : Bool
  isArrayPrototype : Bool
  readOnlyLength : Bool
  replaced : Bool

structure Args where
  start : Option Int
  final : Option Int

def relIndex (len : Nat) (index : Option Int) (init : Nat) : Nat :=
  match index with
  | none => init
  | some i => if i < 0 then (if (len : Int) + i < 0 then 0 else ((len : Int) + i).toNat)
    else min i.toNat len

def startIndex (len : Nat) (args : Args) : Nat := relIndex len args.start 0

def endIndex (len : Nat) (args : Args) : Nat := relIndex len args.final len

inductive Result where
  | done (a : JSArr) (dcheckFailed : Bool)
  | slow
  | ub
  deriving Repr

def replaceAll (a : JSArr) (target : Kind) (fin : Nat) : JSArr :=
  if a.kind.isDouble ≠ target.isDouble ∨ a.cow = true then
    { a with
      kind := target
      cow := false
      store := if target.isDouble then List.replicate fin none
        else List.replicate fin (some (.smi 0)) }
  else { a with kind := target }

def transition (a : JSArr) (dst : Kind) : JSArr :=
  let d := a.kind.transitionTarget dst
  if a.kind = d then a
  else if d.isDouble then { a with kind := d, cow := false }
  else { a with kind := d }

def numberValueOk (c : FillConfig) (v : Val) : Bool :=
  v.isNumber || (c.undefinedDouble && v == .undef)

def accessorFill (c : FillConfig) (b : JSArr) (v : Val) (start fin : Nat) : Option JSArr :=
  let b1 := if b.kind.isDouble then b else ensureWritable b
  let b2 := if b1.store.length < fin then { b1 with store := growTo b1.store fin } else b1
  if b2.cow = true then none
  else if b2.kind.isDouble ∧ numberValueOk c v = false then none
  else if start ≤ fin ∧ fin ≤ b2.store.length then
    some { b2 with store := blit b2.store start (List.replicate (fin - start) (some v)) }
  else none

def setLength (c : FillConfig) (b : JSArr) (fin : Nat) : Result :=
  if b.length < fin then
    .done { b with kind := b.kind.toHoley, length := fin } (decide (c.maxFast < fin))
  else .done b false

def prepare (c : FillConfig) (env : Env) (a : JSArr) (v : Val) (start fin : Nat) : JSArr :=
  let target := optimalKind c.undefinedDouble v
  if target = a.kind then a
  else if start = 0 ∧ fin = a.length ∧ env.replaced = true then replaceAll a target fin
  else transition a (a.kind.moreGeneral target)

def tryFast (c : FillConfig) (env : Env) (a : JSArr) (v : Val) (start fin : Nat) : Result :=
  if 2 ^ 32 - 1 < fin then .slow
  else if a.kind.isFast = false ∨ env.movingAllowed = false ∨ env.isArrayPrototype = true then
    .slow
  else if c.maxLen < fin then .slow
  else if env.readOnlyLength = true ∧ a.length ≤ fin - 1 then .slow
  else
    match accessorFill c (prepare c env a v start fin) v start fin with
    | some b' => setLength c b' fin
    | none => .ub

def fastPath (c : FillConfig) (env : Env) (a : JSArr) (v : Val) (len : Nat) (args : Args) :
    Result :=
  if endIndex len args ≤ startIndex len args then .done a false
  else tryFast c env a v (startIndex len args) (endIndex len args)

def specFill (xs : List (Option Val)) (v : Val) (start fin : Nat) : List (Option Val) :=
  (List.range (max xs.length fin)).map fun i =>
    if start ≤ i ∧ i < fin then some v else xs.getD i none

end ArrayFill
