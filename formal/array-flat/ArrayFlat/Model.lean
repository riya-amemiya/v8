namespace ArrayFlat

inductive Val where
  | smi (n : Int)
  | num (n : Nat)
  | arr (p : Nat)
  | proxy
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

inductive Kind where
  | packedSmi
  | holeySmi
  | packedDouble
  | holeyDouble
  | packedElem
  | holeyElem
  | slow
  deriving DecidableEq, Repr

def Kind.isFast : Kind → Bool
  | .slow => false
  | _ => true

def kindOk : Kind → Option Val → Bool
  | .packedSmi, some v => v.isSmi
  | .packedSmi, none => false
  | .packedDouble, some v => v.isNumber
  | .packedDouble, none => false
  | .packedElem, some _ => true
  | .packedElem, none => false
  | .holeySmi, some v => v.isSmi
  | .holeySmi, none => true
  | .holeyDouble, some v => v.isNumber || v == .other
  | .holeyDouble, none => true
  | .holeyElem, _ => true
  | .slow, _ => true

structure JSArr where
  kind : Kind
  forRead : Bool
  forCopy : Bool
  length : Nat
  store : List (Option Val)
  deriving Repr

def JSArr.elems (a : JSArr) : List (Option Val) := a.store.take a.length

structure JSArr.WF (a : JSArr) : Prop where
  length_le : a.length ≤ a.store.length
  kind_ok : ∀ x ∈ a.elems, kindOk a.kind x = true
  forRead_fast : a.forRead = true → a.kind.isFast = true
  forCopy_forRead : a.forCopy = true → a.forRead = true

abbrev Heap := Nat → JSArr

def HeapWF (H : Heap) : Prop := ∀ p, (H p).WF

structure Config where
  smiMax : Nat
  maxLen : Nat

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

def blit (buf : List (Option Val)) (pos : Nat) (src : List (Option Val)) :
    List (Option Val) :=
  buf.take pos ++ src ++ buf.drop (pos + src.length)

end ArrayFlat
