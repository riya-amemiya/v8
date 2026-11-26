import Torque

namespace ArrayFromCollections

open Torque

inductive Slot where
  | hole
  | key (v : Val)
  deriving DecidableEq, Repr

structure Entry where
  key : Slot
  value : Val
  deriving DecidableEq, Repr

def Entry.live (e : Entry) : Bool :=
  match e.key with
  | .hole => false
  | .key _ => true

def Entry.spec (e : Entry) : Option (Val × Val) :=
  match e.key with
  | .hole => none
  | .key k => some (k, e.value)

structure Table where
  buckets : Nat
  nof : Nat
  nod : Nat
  data : List Entry
  deriving DecidableEq, Repr

def Table.used (t : Table) : Nat := t.nof + t.nod

def Table.empty : Table := ⟨0, 0, 0, []⟩

def liveCount (l : List Entry) : Nat := l.countP Entry.live

structure Table.Inv (t : Table) : Prop where
  used_le : t.used ≤ t.data.length
  count : liveCount (t.data.take t.used) = t.nof

structure Link where
  cleared : Bool
  removed : List Nat
  deriving DecidableEq, Repr

def healLoop : List Nat → Nat → Nat → Nat
  | [], _, v => v
  | r :: rs, index, v => if index ≤ r then v else healLoop rs index (v - 1)

def healIndex (l : Link) (index : Nat) : Nat :=
  if index = 0 then 0 else if l.cleared then 0 else healLoop l.removed index index

def transition : List Link → Nat → Nat
  | [], i => i
  | l :: ls, i => transition ls (healIndex l i)

structure Iter where
  protoInitial : Bool
  chain : List Link
  table : Table
  index : Nat
  deriving DecidableEq, Repr

def transitionAndUpdate (it : Iter) : Iter :=
  match it.chain with
  | [] => it
  | _ :: _ => { it with chain := [], index := transition it.chain it.index }

inductive Next where
  | done
  | found (key : Val) (entry : Nat) (next : Nat)
  | oob
  deriving DecidableEq, Repr

def nextSkip (t : Table) (i : Nat) : Next :=
  if _h : i < t.used then
    match t.data[i]? with
    | none => .oob
    | some e =>
      match e.key with
      | .hole => nextSkip t (i + 1)
      | .key k => .found k i (i + 1)
  else .done
termination_by t.used - i
decreasing_by omega

def loadValue (t : Table) (entry : Nat) : Option Val := (t.data[entry]?).map Entry.value

structure Copy where
  index : Nat
  offset : Nat
  store : List (Option Val)
  deriving DecidableEq, Repr

def storeAt (s : Copy) (v : Val) (n : Nat) : Step Copy Copy :=
  if s.offset < s.store.length then .cont ⟨n, s.offset + 1, s.store.set s.offset (some v)⟩
  else .ub

inductive MapKind where
  | keys
  | values
  | entries
  deriving DecidableEq, Repr

inductive SetKind where
  | values
  | entries
  deriving DecidableEq, Repr

def mapStep (kind : MapKind) (t : Table) (s : Copy) : Step Copy Copy :=
  match nextSkip t s.index with
  | .done => .done s
  | .oob => .ub
  | .found k e n =>
    match kind with
    | .keys => storeAt s k n
    | _ =>
      match loadValue t e with
      | some v => storeAt s v n
      | none => .ub

def setStep (t : Table) (s : Copy) : Step Copy Copy :=
  match nextSkip t s.index with
  | .done => .done s
  | .oob => .ub
  | .found k _ n => storeAt s k n

theorem nextSkip_found {t : Table} {i : Nat} {k : Val} {e n : Nat}
    (h : nextSkip t i = .found k e n) : i ≤ e ∧ e < t.used ∧ n = e + 1 := by
  rw [nextSkip] at h
  split at h
  · rename_i hlt
    split at h
    · cases h
    · split at h
      · have := nextSkip_found h
        omega
      · cases h
        omega
  · cases h
termination_by t.used - i
decreasing_by omega

theorem storeAt_cont {s t : Copy} {v : Val} {n : Nat} (h : storeAt s v n = .cont t) :
    t.index = n := by
  unfold storeAt at h
  split at h
  · cases h
    rfl
  · cases h

theorem mapStep_decreases (kind : MapKind) (t : Table) (s s' : Copy)
    (h : mapStep kind t s = .cont s') : t.used - s'.index < t.used - s.index := by
  unfold mapStep at h
  split at h
  · cases h
  · cases h
  · rename_i k e n hn
    obtain ⟨h1, h2, h3⟩ := nextSkip_found hn
    split at h
    · rw [storeAt_cont h]
      omega
    · split at h
      · rw [storeAt_cont h]
        omega
      · cases h

theorem setStep_decreases (t : Table) (s s' : Copy)
    (h : setStep t s = .cont s') : t.used - s'.index < t.used - s.index := by
  unfold setStep at h
  split at h
  · cases h
  · cases h
  · rename_i k e n hn
    obtain ⟨h1, h2, h3⟩ := nextSkip_found hn
    rw [storeAt_cont h]
    omega

def runMap (kind : MapKind) (t : Table) : Copy → Outcome Copy :=
  run (mapStep kind t) (fun s => t.used - s.index) (mapStep_decreases kind t)

def runSet (t : Table) : Copy → Outcome Copy :=
  run (setStep t) (fun s => t.used - s.index) (setStep_decreases t)

def mapOk {α β : Type} (f : α → β) : Outcome α → Outcome β
  | .ok a => .ok (f a)
  | .bailout => .bailout
  | .throwRange => .throwRange
  | .ub => .ub
  | .fatal => .fatal

def allocate (size : Nat) : List (Option Val) := List.replicate size none

def resultArray (size : Nat) (store : List (Option Val)) : JSArr :=
  ⟨.packedElem, true, true, true, false, size, store⟩

def exhaust (it : Iter) (index : Nat) : Iter :=
  { it with chain := [], table := Table.empty, index := index }

def mapIteratorToList (kind : MapKind) (it : Iter) : Outcome (JSArr × Iter) :=
  mapOk (fun s => (resultArray it.table.nof s.store, exhaust (transitionAndUpdate it) s.index))
    (runMap kind it.table ⟨transition it.chain it.index, 0, allocate it.table.nof⟩)

structure SetObj where
  protoInitial : Bool
  table : Table
  deriving DecidableEq, Repr

inductive Iterable where
  | mapIter (kind : MapKind) (it : Iter)
  | setIter (kind : SetKind) (it : Iter)
  | set (s : SetObj)
  | other
  deriving DecidableEq, Repr

def Iterable.table : Iterable → Table
  | .mapIter _ it => it.table
  | .setIter _ it => it.table
  | .set s => s.table
  | .other => Table.empty

def setOrSetIteratorToSet : Iterable → Iterable
  | .setIter kind it => .setIter kind (exhaust (transitionAndUpdate it) it.table.nof)
  | x => x

def setOrSetIteratorToList (x : Iterable) : Outcome (JSArr × Iterable) :=
  mapOk (fun s => (resultArray x.table.nof s.store, setOrSetIteratorToSet x))
    (runSet x.table ⟨0, 0, allocate x.table.nof⟩)

structure Env where
  forceSlow : Bool
  debugActive : Bool
  mapIteratorProtector : Bool
  setIteratorProtector : Bool
  mapIteratorProtoInitial : Bool
  setIteratorProtoInitial : Bool
  deriving DecidableEq, Repr

def MapKind.keyOrValue : MapKind → Bool
  | .keys => true
  | .values => true
  | .entries => false

def mapBranch (env : Env) (kind : MapKind) (it : Iter) : Bool :=
  kind.keyOrValue && it.index == 0 && env.mapIteratorProtector && it.protoInitial &&
    env.mapIteratorProtoInitial

def setIterBranch (env : Env) (kind : SetKind) (it : Iter) : Bool :=
  kind == .values && it.index == 0 && it.protoInitial && env.setIteratorProtoInitial &&
    env.setIteratorProtector

def setBranch (env : Env) (s : SetObj) : Bool := s.protoInitial && env.setIteratorProtector

def fastIterableToList (env : Env) (x : Iterable) : Outcome (JSArr × Iterable) :=
  if (env.forceSlow || env.debugActive) = true then .bailout
  else
    match x with
    | .mapIter kind it =>
      if mapBranch env kind it then
        mapOk (fun r => (r.1, Iterable.mapIter kind r.2)) (mapIteratorToList kind it)
      else .bailout
    | .setIter kind it => if setIterBranch env kind it then setOrSetIteratorToList x else .bailout
    | .set s => if setBranch env s then setOrSetIteratorToList x else .bailout
    | .other => .bailout

def specIter {α : Type} (entries : List (Option α)) (index : Nat) : List α :=
  if h : index < entries.length then
    match entries[index] with
    | none => specIter entries (index + 1)
    | some e => e :: specIter entries (index + 1)
  else []
termination_by entries.length - index
decreasing_by all_goals omega

def Table.mapData (t : Table) : List (Option (Val × Val)) := (t.data.take t.used).map Entry.spec

def Table.setData (t : Table) : List (Option Val) := t.mapData.map (Option.map Prod.fst)

def Iterable.spec : Iterable → List Val
  | .mapIter .keys it => specIter (it.table.mapData.map (Option.map Prod.fst)) 0
  | .mapIter .values it => specIter (it.table.mapData.map (Option.map Prod.snd)) 0
  | .mapIter .entries _ => []
  | .setIter _ it => specIter it.table.setData 0
  | .set s => specIter s.table.setData 0
  | .other => []

def Iterable.Exhausted : Iterable → Prop
  | .mapIter _ it => it.chain = [] ∧ it.table = Table.empty
  | .setIter _ it => it.chain = [] ∧ it.table = Table.empty
  | _ => True

def mapIteratorNext (kind : MapKind) (it : Iter) : Outcome (Option Val × Iter) :=
  match nextSkip it.table (transition it.chain it.index) with
  | .done => .ok (none, { transitionAndUpdate it with table := Table.empty })
  | .oob => .ub
  | .found k e n =>
    match kind with
    | .keys => .ok (some k, { transitionAndUpdate it with index := n })
    | .values =>
      match loadValue it.table e with
      | some v => .ok (some v, { transitionAndUpdate it with index := n })
      | none => .ub
    | .entries =>
      match loadValue it.table e with
      | some _ => .ok (some .other, { transitionAndUpdate it with index := n })
      | none => .ub

def setIteratorNext (kind : SetKind) (it : Iter) : Outcome (Option Val × Iter) :=
  match nextSkip it.table (transition it.chain it.index) with
  | .done => .ok (none, { transitionAndUpdate it with table := Table.empty })
  | .oob => .ub
  | .found k _ n =>
    match kind with
    | .values => .ok (some k, { transitionAndUpdate it with index := n })
    | .entries => .ok (some .other, { transitionAndUpdate it with index := n })

end ArrayFromCollections
