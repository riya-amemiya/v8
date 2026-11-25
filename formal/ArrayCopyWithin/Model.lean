import Torque

namespace ArrayCopyWithin

open Torque

def clampIndex (index : Int) (len : Nat) : Nat :=
  let rel : Int := if 0 ≤ index then index else len + index
  if rel < 0 then 0 else if (len : Int) ≤ rel then len else rel.toNat

structure Args where
  target : Int
  start : Int
  final : Option Int

def targetIndex (len : Nat) (args : Args) : Nat := clampIndex args.target len

def startIndex (len : Nat) (args : Args) : Nat := clampIndex args.start len

def finalIndex (len : Nat) (args : Args) : Nat := clampIndex (args.final.getD len) len

def count (len : Nat) (args : Args) : Int :=
  min ((finalIndex len args : Int) - startIndex len args) ((len : Int) - targetIndex len args)

inductive Result where
  | done (a : JSArr)
  | slow
  | ub
  deriving Repr

def moveChecked (a : JSArr) (dst src count : Int) : Result :=
  if a.cow = true then .ub
  else if 0 ≤ dst ∧ 0 ≤ src ∧ 0 ≤ count ∧ dst + count ≤ a.store.length ∧
      src + count ≤ a.store.length then
    .done { a with store := moveElements a.store dst.toNat src.toNat count.toNat }
  else .ub

def tryFast (r : SmiRepr) (a : JSArr) (dst src count : Int) : Result :=
  if count ≤ 0 then .done a
  else if a.fast = false then .slow
  else if (r.isSmi dst && r.isSmi src && r.isSmi count) = false then .slow
  else if SmiRepr.above (r.add dst count) (r.word a.length) then .slow
  else if SmiRepr.above (r.add src count) (r.word a.length) then .slow
  else match a.kind with
    | .packedSmi => moveChecked (ensureWritable a) dst src count
    | .packedElem => moveChecked (ensureWritable a) dst src count
    | .packedDouble => moveChecked a dst src count
    | .holeyDouble => moveChecked a dst src count
    | .holeySmi => moveChecked (ensureWritable a) dst src count
    | .holeyElem => moveChecked (ensureWritable a) dst src count
    | .slow => .slow

def fastPath (r : SmiRepr) (a : JSArr) (len : Nat) (args : Args) : Result :=
  tryFast r a (targetIndex len args) (startIndex len args) (count len args)

def copyFwd : List (Option Val) → Nat → Nat → Nat → List (Option Val)
  | xs, _, _, 0 => xs
  | xs, dst, src, n + 1 => copyFwd (xs.set dst (xs.getD src none)) (dst + 1) (src + 1) n

def copyBwd : List (Option Val) → Nat → Nat → Nat → List (Option Val)
  | xs, _, _, 0 => xs
  | xs, dst, src, n + 1 => copyBwd (xs.set (dst + n) (xs.getD (src + n) none)) dst src n

def specCopy (xs : List (Option Val)) (dst src : Nat) (count : Int) : List (Option Val) :=
  if count ≤ 0 then xs
  else if src < dst ∧ dst < src + count.toNat then copyBwd xs dst src count.toNat
  else copyFwd xs dst src count.toNat

end ArrayCopyWithin
