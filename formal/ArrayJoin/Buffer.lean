import Torque

namespace ArrayJoin

open Torque

inductive Res (α : Type) where
  | ok (x : α)
  | throws
  | bailout
  | ub
  | fatal
  deriving Repr

def Res.bind {α β : Type} : Res α → (α → Res β) → Res β
  | .ok x, f => f x
  | .throws, _ => .throws
  | .bailout, _ => .bailout
  | .ub, _ => .ub
  | .fatal, _ => .fatal

@[simp] theorem Res.ok_bind {α β : Type} (x : α) (f : α → Res β) : (Res.ok x).bind f = f x := rfl

def Res.Safe {α : Type} : Res α → Prop
  | .ub => False
  | .fatal => False
  | _ => True

structure Limits where
  strMax : Nat
  smiMax : Nat
  intMax : Nat
  maxChunk : Nat
  maxArray : Nat

structure Limits.OK (l : Limits) : Prop where
  chunk : 2 ≤ l.maxChunk
  smi : l.strMax ≤ l.smiMax
  int : l.strMax ≤ l.intMax

structure Str where
  id : Nat
  chars : List Nat
  deriving DecidableEq, Repr

def Str.len (s : Str) : Nat := s.chars.length

inductive Item where
  | str (s : Str)
  | seps (n : Nat)
  | rep (n : Nat)
  deriving DecidableEq, Repr

def sepRun (sep : List Nat) (n : Nat) : List Nat := (List.replicate n sep).flatten

def reps (sep s : List Nat) (n : Nat) : List Nat := (List.replicate n (sep ++ s)).flatten

def joinPieces (sep : List Nat) : List (List Nat) → List Nat
  | [] => []
  | p :: ps => p ++ (ps.map (sep ++ ·)).flatten

def grow (n : Nat) : Nat := n + n / 2 + 16

structure Buf where
  full : List (Nat × List Item)
  cap : Nat
  cur : List Item
  total : Nat
  last : Option Str
  deriving Repr

def Buf.flat (b : Buf) : List Item := (b.full.map Prod.snd).flatten ++ b.cur

def Buf.chunks (b : Buf) : List (Nat × List Item) := b.full ++ [(b.cap, b.cur)]

def newBuffer (l : Limits) (len : Nat) : Buf :=
  ⟨[], if l.maxChunk ≤ len then l.maxChunk else len + 1, [], 0, none⟩

def appendToChunk (l : Limits) (b : Buf) (x : Item) : Res Buf :=
  if b.cur.length + 1 < b.cap then .ok { b with cur := b.cur ++ [x] }
  else if b.cap = 0 then .fatal
  else if min (grow b.cap) l.maxChunk < 2 then .fatal
  else .ok { b with full := b.full ++ [(b.cap, b.cur)], cap := min (grow b.cap) l.maxChunk, cur := [x] }

def repeatLast (l : Limits) (b : Buf) : Res Buf :=
  match b.cur.getLast? with
  | none => .fatal
  | some (.str _) => appendToChunk l b (.rep 1)
  | some (.rep n) =>
    if n + 1 ≤ l.smiMax then .ok { b with cur := b.cur.dropLast ++ [.rep (n + 1)] } else .ub
  | some (.seps _) => .ub

def addLen (l : Limits) (a b : Nat) : Res Nat := if a + b ≤ l.strMax then .ok (a + b) else .throws

def addSeparators (l : Limits) (b : Buf) (n sepLen : Nat) (write : Bool) : Res Buf :=
  if n = 0 ∨ sepLen = 0 then .ok b
  else if l.intMax < sepLen * n then .ub
  else (addLen l b.total (sepLen * n)).bind fun t =>
    if write then
      if l.smiMax < n then .ub
      else (appendToChunk l { b with total := t } (.seps n)).bind fun b' =>
        .ok { b' with last := none }
    else .ok { b with total := t }

def add (l : Limits) (b : Buf) (s : Str) (n sepLen : Nat) : Res Buf :=
  (addSeparators l b n sepLen (b.cur.isEmpty || decide (1 < n))).bind fun b1 =>
  (addLen l b1.total s.len).bind fun t =>
  if b1.last = some s then repeatLast l { b1 with total := t }
  else (appendToChunk l { b1 with total := t } (.str s)).bind fun b2 =>
    .ok { b2 with last := some s }

structure WS where
  out : List Nat
  numSep : Nat
  last : Option Str
  deriving DecidableEq, Repr

def WS.init : WS := ⟨[], 0, none⟩

def writeSeps (sinkLen : Nat) (sep : List Nat) (w : WS) : Option WS :=
  if 0 < w.numSep ∧ 0 < sep.length then
    if w.out.length + w.numSep * sep.length ≤ sinkLen then
      some ⟨w.out ++ sepRun sep w.numSep, 0, w.last⟩
    else none
  else some w

def dbl (sinkLen copyEnd : Nat) (out : List Nat) (c : Nat) : Option (List Nat) :=
  if h : out.length + c < copyEnd then
    if hc : c = 0 then none
    else if hr : c ≤ out.length ∧ out.length + c ≤ sinkLen then
      dbl sinkLen copyEnd (out ++ out.drop (out.length - c)) (2 * c)
    else none
  else some out
termination_by copyEnd - out.length
decreasing_by
  simp only [List.length_append, List.length_drop]
  omega

def repTail (sinkLen copyEnd sepLen : Nat) (out : List Nat) : Option (List Nat) :=
  if copyEnd < out.length then none
  else if copyEnd - out.length = 0 then some out
  else if copyEnd - out.length + sepLen ≤ out.length ∧ copyEnd ≤ sinkLen then
    some (out ++ (out.drop (out.length - (copyEnd - out.length) - sepLen)).take
      (copyEnd - out.length))
  else none

def repStep (sinkLen : Nat) (sep : List Nat) (w : WS) (r : Nat) : Option WS :=
  if r = 0 then some ⟨w.out, w.numSep, none⟩
  else
    match w.last with
    | none => none
    | some s =>
      (dbl sinkLen (w.out.length + (s.len + sep.length) * r - sep.length) w.out
        (s.len + sep.length)).bind fun o =>
      (repTail sinkLen (w.out.length + (s.len + sep.length) * r - sep.length) sep.length o).map
        fun o' => ⟨o', 1, none⟩

def wItem (sinkLen : Nat) (sep : List Nat) (w : WS) : Item → Option WS
  | .seps n =>
    (writeSeps sinkLen sep (if 0 < n then { w with numSep := n } else w)).map
      fun w' => { w' with last := none }
  | .rep r => (writeSeps sinkLen sep w).bind fun w' => repStep sinkLen sep w' r
  | .str s => (writeSeps sinkLen sep w).bind fun w' =>
    if w'.out.length + s.len ≤ sinkLen then some ⟨w'.out ++ s.chars, 1, some s⟩ else none

def slots (cap : Nat) (items : List Item) : List Item :=
  items ++ List.replicate (cap - 1 - items.length) (.seps 0)

def readChunk (sinkLen : Nat) (sep : List Nat) (cap length : Nat) (items : List Item) (w : WS) :
    Option WS :=
  if 0 < length ∧ length ≤ cap then ((slots cap items).take (length - 1)).foldlM (wItem sinkLen sep) w
  else none

def writeChunks (sinkLen : Nat) (sep : List Nat) (lastLen : Nat) :
    List (Nat × List Item) → WS → Option WS
  | [], w => some w
  | [(cap, items)], w => readChunk sinkLen sep cap lastLen items w
  | (cap, items) :: c :: cs, w =>
    (readChunk sinkLen sep cap cap items w).bind (writeChunks sinkLen sep lastLen (c :: cs))

def bufferJoin (b : Buf) (sep : Str) : Res (List Nat) :=
  if b.total = 0 then .ok []
  else if b.cur.length = 1 ∧ b.full = [] then
    match b.cur with
    | [.str s] => .ok s.chars
    | [.seps n] => if 0 < n then .ok (sepRun sep.chars n) else .ub
    | _ => .ub
  else
    match writeChunks b.total sep.chars (b.cur.length + 1) b.chunks WS.init with
    | some w => if w.out.length = b.total then .ok w.out else .ub
    | none => .ub

end ArrayJoin
