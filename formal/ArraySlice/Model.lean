import ArrayCopyCommon
import ArrayBuild

namespace ArraySlice

open Torque ArrayCopyCommon

structure Config where
  lim : Limits
  smiMax : Nat
  maxFolded : Nat

structure Aliased where
  mapped : List (Option Nat)
  context : List Val
  unmapped : Option (List (Option Val))
  deriving Repr

inductive Recv where
  | array (a : JSArr)
  | strictArgs (elements : Option (List (Option Val)))
  | sloppyArgs (elements : Option (List (Option Val)))
  | aliasedArgs (s : Aliased)
  | other
  deriving Repr

inductive Out where
  | done (a : JSArr)
  | slow
  | ub
  | fatal
  deriving Repr

def holeyArray (store : List (Option Val)) : JSArr :=
  ⟨.holeyElem, true, true, false, false, store.length, store⟩

def simpleArgs (c : Config) (elements : Option (List (Option Val))) (start count : Nat) : Out :=
  match elements with
  | none => .slow
  | some src =>
    if src.length < start + count then .slow
    else if c.maxFolded < count then .slow
    else
      match copyElements (List.replicate count none) 0 src start count with
      | some s => .done (holeyArray s)
      | none => .ub

def mappedValue (s : Aliased) (src : List (Option Val)) (i : Nat) : Option (Option Val) :=
  match s.mapped[i]? with
  | none => none
  | some none => src[i]?
  | some (some j) => (s.context[j]?).map some

def aliasedLoop (s : Aliased) (src : List (Option Val)) : Nat → Nat → List (Option Val) →
    Option (List (Option Val))
  | 0, _, out => some out
  | n + 1, i, out =>
    match mappedValue s src i with
    | none => none
    | some x => aliasedLoop s src n (i + 1) (out ++ [x])

def aliasedArgs (c : Config) (s : Aliased) (start count : Nat) : Out :=
  match s.unmapped with
  | none => .slow
  | some src =>
    if src.length < start + count then .slow
    else if c.maxFolded < count then .slow
    else
      let to := min s.mapped.length (start + count)
      let rf := min (max s.mapped.length start) (start + count)
      match aliasedLoop s src (to - start) start [] with
      | none => .fatal
      | some head =>
        match copyElements (List.replicate count none) head.length src rf (start + count - rf)
          with
        | some rest => .done (holeyArray (blit rest 0 head))
        | none => .ub

def ofResult : Result JSArr → Out
  | .done _ r => .done r
  | .slow => .slow
  | .throws => .slow
  | .ub => .ub
  | .abort => .fatal

def handleFastSlice (c : Config) (o : Recv) (start count : Nat) : Out :=
  if c.smiMax < start ∨ c.smiMax < count then .slow
  else
    match o with
    | .array a =>
      if a.forCopy = false then .slow
      else if a.length < start + count then .slow
      else ofResult (extractFast c.lim a start count)
    | .strictArgs e => simpleArgs c e start count
    | .sloppyArgs e => simpleArgs c e start count
    | .aliasedArgs s => aliasedArgs c s start count
    | .other => .slow

def clamp (len : Nat) (rel : Int) : Nat := relIndex len rel

def sliceIndices (len : Nat) (relStart : Int) (relEnd : Option Int) : Nat × Nat :=
  let k := clamp len relStart
  let fin := match relEnd with
    | none => len
    | some e => clamp len e
  (k, fin - k)

inductive StartArg where
  | undef
  | smiZero
  | other (n : Int)
  deriving DecidableEq, Repr

def StartArg.value : StartArg → Int
  | .undef => 0
  | .smiZero => 0
  | .other n => n

def ofClone : ArrayBuild.CloneResult → Out
  | .done a => .done a
  | .ub => .ub

def slice (c : Config) (len : Nat) (receiver : Recv) (start : StartArg) (relEnd : Option Int)
    (o : Recv) : Out :=
  match start, relEnd, receiver with
  | .undef, none, .array a =>
    if a.forCopy = true then ofClone (ArrayBuild.cloneFastJSArray false a)
    else handleFastSlice c o (sliceIndices len 0 none).1 (sliceIndices len 0 none).2
  | .smiZero, none, .array a =>
    if a.forCopy = true then ofClone (ArrayBuild.cloneFastJSArray false a)
    else handleFastSlice c o (sliceIndices len 0 none).1 (sliceIndices len 0 none).2
  | _, _, _ =>
    handleFastSlice c o (sliceIndices len start.value relEnd).1
      (sliceIndices len start.value relEnd).2

def argsSpec (elements : List (Option Val)) (start count : Nat) : List (Option Val) :=
  specSlice elements start count

def aliasedSpec (s : Aliased) (src : List (Option Val)) (start count : Nat) : List (Option Val) :=
  (List.range count).map fun i =>
    match s.mapped[start + i]? with
    | some (some j) => s.context[j]?
    | _ => src.getD (start + i) none

def Aliased.OK (s : Aliased) : Prop :=
  ∀ i j : Nat, s.mapped[i]? = some (some j) → j < s.context.length

end ArraySlice
