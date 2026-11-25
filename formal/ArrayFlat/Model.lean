import Torque

namespace ArrayFlat

open Torque

def kMaxFlatFastStackEntries : Nat := 4096

def descend? : Nat → Val → Option (Nat × Nat)
  | d + 1, .arr q => some (d, q)
  | _, _ => none

def leaves (H : Heap) : Nat → List (Option Val) → List Val
  | 0, l => l.filterMap id
  | d + 1, l => l.flatMap fun
    | some (.arr q) => leaves H d (H q).elems
    | some v => [v]
    | none => []

def flatSpec (H : Heap) (root srcLen depth : Nat) : List Val :=
  leaves H depth ((H root).elems.take srcLen)

def Conforms : Kind → List Val → Prop
  | .packedSmi, L => ∀ v ∈ L, v.isSmi = true
  | .packedDouble, L => ∀ v ∈ L, v.isNumber = true
  | .packedElem, _ => True
  | _, _ => False

structure Frame where
  arr : Nat
  len : Nat
  idx : Nat
  depth : Nat
  deriving Repr

def Frame.next (f : Frame) : Frame := { f with idx := f.idx + 1 }

def Frame.rest (H : Heap) (f : Frame) : List (Option Val) :=
  ((H f.arr).elems.take f.len).drop f.idx

def Frame.pending (H : Heap) (f : Frame) : List Val :=
  leaves H f.depth (f.rest H)

def pendingAll (H : Heap) (cur : Frame) (stack : List Frame) : List Val :=
  cur.pending H ++ stack.flatMap (Frame.pending H)

inductive Fetch where
  | exhausted
  | bail
  | oob
  | elem (x : Option Val)

def fetch (H : Heap) (f : Frame) : Fetch :=
  if f.idx < f.len then
    if (H f.arr).length ≤ f.idx then .bail
    else match (H f.arr).store[f.idx]? with
      | some x => .elem x
      | none => .oob
  else .exhausted

def cost (H : Heap) : Nat → List (Option Val) → Nat
  | 0, l => l.length + 1
  | d + 1, l => (l.map fun
    | some (.arr q) => cost H d (H q).elems + 1
    | _ => 1).sum + 1

def Frame.cost (H : Heap) (f : Frame) : Nat := ArrayFlat.cost H f.depth (f.rest H)

def frameMeasure (H : Heap) (cur : Frame) (stack : List Frame) : Nat :=
  cur.cost H + (stack.map (Frame.cost H)).sum

end ArrayFlat
