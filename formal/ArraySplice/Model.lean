import InPlace

namespace ArraySplice

open Torque InPlace

inductive Args where
  | none
  | start (s : Int)
  | full (s dc : Int) (items : List Val)

def Args.startArg : Args → Int
  | .none => 0
  | .start s => s
  | .full s _ _ => s

def Args.items : Args → List Val
  | .full _ _ xs => xs
  | _ => []

def actualStart (len : Nat) (relativeStart : Int) : Nat :=
  if relativeStart < 0 then
    (if (len : Int) + relativeStart < 0 then 0 else ((len : Int) + relativeStart).toNat)
  else min relativeStart.toNat len

def actualDeleteCount (len : Nat) : Args → Nat
  | .none => 0
  | .start s => len - actualStart len s
  | .full s dc _ => min (max dc 0).toNat (len - actualStart len s)

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

def insertionKind : Kind → List Val → Kind
  | k, [] => k
  | k, e :: rest =>
    if isSmiKind k then
      if e.isSmi then insertionKind k rest
      else if isHeapNumber e then insertionKind (allowDouble k) rest
      else insertionKind (allowNonNumber k) rest
    else if k.isDouble then
      if e.isNumber then insertionKind k rest else insertionKind (allowNonNumber k) rest
    else k

def transitionForInsertion (c : Config) (a : JSArr) (xs : List Val) : Res JSArr :=
  if insertionKind a.kind xs = a.kind then .ok a else transitionTo c a (insertionKind a.kind xs)

def newCapacity (n : Nat) : Nat := n + n / 2 + 16

def extract (c : Config) (b : JSArr) (start count : Nat) : Res JSArr :=
  if count = 0 then .ok (newArray b.kind [])
  else if c.maxLen < count then .abort
  else do
    let s ← memcpy (List.replicate count none) 0 b.store start count
    pure (newArray b.kind s)

def storeHoles (cow : Bool) (s : List (Option Val)) (i j : Nat) : Res (List (Option Val)) :=
  if h : i < j then do
    let s' ← storeSlot cow s i none
    storeHoles cow s' (i + 1) j
  else .ok s
termination_by j - i

def insertLoop (cow : Bool) (k : Kind) :
    List (Option Val) → Nat → List Val → Res (List (Option Val))
  | s, _, [] => .ok s
  | s, pos, e :: rest =>
    if k.isDouble = true ∧ e.isNumber = false then .ub
    else do
      let s' ← storeSlot cow s pos (some e)
      insertLoop cow k s' (pos + 1) rest

def extractGrow (c : Config) (k : Kind) (s : List (Option Val)) (start cap : Nat) :
    Res (List (Option Val)) :=
  if k.isDouble = true ∧ s = [] then
    if c.maxLen < cap then .abort else .ok (List.replicate cap none)
  else if s.length < start then .abort
  else if c.maxLen < cap then .abort
  else .ok (s.take start ++ List.replicate (cap - start) none)

def shuffle (c : Config) (e : JSArr) (len n start ic adc : Nat) :
    Res (List (Option Val) × Bool) :=
  if ic = adc then .ok (e.store, e.cow)
  else if ic < adc then do
    let s ← memmove e.cow e.store (start + ic) (start + adc) (len - adc - start)
    let s' ← storeHoles e.cow s n len
    pure (s', e.cow)
  else if n ≤ e.store.length then do
    let s ← memmove e.cow e.store (start + ic) (start + adc) (len - adc - start)
    pure (s, e.cow)
  else if c.smiMax < newCapacity n then .ub
  else do
    let fresh ← extractGrow c e.kind e.store start (newCapacity n)
    if 0 < e.store.length then do
      let s ← memcpy fresh (start + ic) e.store (start + adc) (len - adc - start)
      pure (s, false)
    else pure (fresh, false)

def fastSplice (c : Config) (b : JSArr) (len n start adc : Nat) (xs : List Val) : Res JSArr := do
  let e ← ensureWritableChecked c b
  let (s, cow) ← shuffle c e len n start xs.length adc
  let s' ← insertLoop cow e.kind s start xs
  pure { e with store := s', length := n, cow := cow }

def tryFast (c : Config) (m : MapInfo) (a : JSArr) (len start adc : Nat) (xs : List Val) :
    Result JSArr :=
  if c.smiMax < len ∨ c.smiMax < start ∨ c.smiMax < adc then .slow
  else if a.forCopy = false ∨ m.pushable = false then .slow
  else (transitionForInsertion c a xs).then fun b =>
    if c.smiMax < b.length then .slow
    else if len ≠ b.length then .slow
    else if c.smiMax < len + xs.length - adc then .ub
    else (extract c b start adc).then fun deleted =>
      if len + xs.length - adc = 0 then
        .done { b with store := [], length := 0, cow := false } deleted
      else (fastSplice c b len (len + xs.length - adc) start adc xs).then fun b' =>
        .done b' deleted

def fastPath (c : Config) (m : MapInfo) (a : JSArr) (len : Nat) (args : Args) : Result JSArr :=
  if 2 ^ 53 - 1 < len + args.items.length - actualDeleteCount len args then .throws
  else tryFast c m a len (actualStart len args.startArg) (actualDeleteCount len args) args.items

def specSplice (xs : List (Option Val)) (start count : Nat) (items : List Val) :
    List (Option Val) × List (Option Val) :=
  (xs.take start ++ items.map some ++ xs.drop (start + count), (xs.drop start).take count)

end ArraySplice
