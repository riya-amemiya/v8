import ArrayCopyCommon

namespace ArrayToSpliced

open Torque ArrayCopyCommon

inductive Args where
  | none
  | start (s : Int)
  | full (s : Int) (dc : Int) (items : List Val)

def actualStart (len : Nat) : Args → Nat
  | .none => relIndex len 0
  | .start s => relIndex len s
  | .full s _ _ => relIndex len s

def items : Args → List Val
  | .full _ _ its => its
  | _ => []

def actualDeleteCount (len : Nat) (args : Args) : Nat :=
  match args with
  | .none => 0
  | .start _ => len - actualStart len args
  | .full _ dc _ => min (if dc < 0 then 0 else dc.toNat) (len - actualStart len args)

def newLen (len : Nat) (args : Args) : Nat :=
  len + (items args).length - actualDeleteCount len args

def fillZero (buf : List (Option Val)) (start n : Nat) : Option (List (Option Val)) :=
  if start + n ≤ buf.length then some (blit buf start (List.replicate n (some (.smi 0))))
  else none

def copyForToSpliced (lim : Limits) (src : List (Option Val)) (nl st ins dc : Nat) : Run :=
  if lim.maxLen < nl then .abort
  else
    match (if 0 < st then copyElements (List.replicate nl none) 0 src 0 st
      else some (List.replicate nl none)) with
    | none => .ub
    | some b1 =>
      match (if 0 < ins then fillZero b1 st ins else some b1) with
      | none => .ub
      | some b2 =>
        match (if 0 < nl - (st + ins) then copyElements b2 (st + ins) src (st + dc) (nl - (st + ins))
          else some b2) with
        | none => .ub
        | some b3 => if none ∈ b3 then .ub else .ok b3

def isSmiKind : Kind → Bool
  | .packedSmi => true
  | .holeySmi => true
  | _ => false

def isHeapNumber : Val → Bool
  | .num _ => true
  | _ => false

def allowDouble : Kind → Kind
  | .packedSmi => .packedDouble
  | .holeySmi => .holeyDouble
  | k => k

def allowNonNumber : Kind → Kind
  | .packedSmi => .packedElem
  | .holeySmi => .holeyElem
  | .packedDouble => .packedElem
  | .holeyDouble => .holeyElem
  | k => k

def insertKind : Kind → List Val → Kind
  | k, [] => k
  | k, e :: es =>
    if isSmiKind k then
      (if e.isSmi then insertKind k es
       else if isHeapNumber e then insertKind (allowDouble k) es
       else insertKind (allowNonNumber k) es)
    else if k.isDouble then
      (if e.isNumber then insertKind k es else insertKind (allowNonNumber k) es)
    else k

def transitionCopy (lim : Limits) (c : JSArr) (k : Kind) : Option JSArr :=
  if k = c.kind then some c
  else if c.kind.isDouble ≠ k.isDouble ∧ lim.maxLen < c.store.length then none
  else some { c with kind := k }

def insertLoop (dbl : Bool) : List (Option Val) → Nat → List Val → Run
  | buf, _, [] => .ok buf
  | buf, k, e :: es =>
    if dbl = true ∧ e.isNumber = false then .ub
    else match storeChecked buf k e with
      | some buf' => insertLoop dbl buf' (k + 1) es
      | none => .abort

def tryFast (r : SmiRepr) (lim : Limits) (len nl st dc : Nat) (its : List Val) (a : JSArr) :
    Result JSArr :=
  if r.max < nl ∨ r.max < st ∨ r.max < dc then .slow
  else if a.fast = false then .slow
  else if r.max < len then .slow
  else if a.length < len then .slow
  else if isFastPacked a.kind = false then .slow
  else match copyForToSpliced lim a.store nl st its.length dc with
    | .ub => .ub
    | .abort => .abort
    | .ok buf =>
      match transitionCopy lim (newArray a.kind buf) (insertKind a.kind its) with
      | none => .abort
      | some c =>
        match insertLoop c.kind.isDouble c.store st its with
        | .ok buf' => .done a { c with store := buf' }
        | .ub => .ub
        | .abort => .abort

def fastPath (r : SmiRepr) (lim : Limits) (len : Nat) (args : Args) (a : JSArr) : Result JSArr :=
  if 2 ^ 53 - 1 < newLen len args then .throws
  else if newLen len args = 0 then .done a (newArray .packedSmi [])
  else if lim.maxFast < newLen len args then .slow
  else tryFast r lim len (newLen len args) (actualStart len args) (actualDeleteCount len args)
    (items args) a

def specSpliced (xs : List (Option Val)) (len st dc : Nat) (its : List Val) : List (Option Val) :=
  (List.range st).map (fun i => some (getOrUndef xs i)) ++ its.map some ++
    (List.range (len - st - dc)).map (fun i => some (getOrUndef xs (st + dc + i)))

end ArrayToSpliced
