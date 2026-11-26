import ArraySort.Pres

namespace ArraySort

open Torque

structure Maps where
  kind : Nat → Kind
  fast : Nat → Bool

structure RecvOK (cfg : Cfg) (mp : Maps) (r : Recv) : Prop where
  wf : r.arr.WF
  kind : r.arr.kind = mp.kind r.map
  fast : r.arr.fast = (mp.fast r.map && r.prot)
  dbl : r.arr.kind.isDouble = true → ∀ x ∈ r.arr.elems,
    x = none ∨ (∃ k, x = some (.num k)) ∨ (x = some .undef ∧ cfg.ud = true)

structure RecvStep (cfg : Cfg) (mp : Maps) (r r' : Recv) : Prop where
  ok : RecvOK cfg mp r'
  prot : r'.prot = true → r.prot = true
  cow : r'.arr.cow = true → r.arr.cow = true

def EnvOK (cfg : Cfg) (mp : Maps) (env : Env) : Prop :=
  (∀ t r x y n r', env.call t r x y = some (n, r') → RecvOK cfg mp r → RecvStep cfg mp r r') ∧
  (∀ t r x y z r', env.str t r x y = some (z, r') → RecvOK cfg mp r → RecvStep cfg mp r r') ∧
  (∀ b t r i v r', env.load b t r i = some (v, r') → RecvOK cfg mp r → RecvStep cfg mp r r') ∧
  (∀ t r i v r', env.set t r i v = some r' → RecvOK cfg mp r → RecvStep cfg mp r r') ∧
  (∀ t r i r', env.del t r i = some r' → RecvOK cfg mp r → RecvStep cfg mp r r') ∧
  (∀ t r v r', env.toNum t r v = some r' → RecvOK cfg mp r → RecvStep cfg mp r r')

def Reach (cfg : Cfg) (mp : Maps) (r1 : Recv) (e : Ext) : Prop :=
  RecvOK cfg mp e.recv ∧ (e.recv.prot = true → r1.prot = true) ∧ (e.recv.arr.cow = true → r1.arr.cow = true)

def gstep (isToSorted : Bool) (acc : List Val × Nat) : Option Val → List Val × Nat
  | none => (acc.1, if isToSorted then acc.2 + 1 else acc.2)
  | some v => if v = .undef then (acc.1, acc.2 + 1) else (acc.1 ++ [v], acc.2)

def gatherGen (env : Env) (isToSorted : Bool) (len : Nat) :
    Nat → Ext → List Val × Nat → Option (List Val × Nat × Ext)
  | i, e, acc =>
    if _h : i < len then
      match env.load (!isToSorted) e.tick e.recv i with
      | some (x, r) => gatherGen env isToSorted len (i + 1) (e.step r) (gstep isToSorted acc x)
      | none => none
    else some (acc.1, acc.2, e)
termination_by i => len - i

def gather (env : Env) (isToSorted : Bool) (len : Nat) (e : Ext) : Option (List Val × Nat × Ext) :=
  if e.recv.arr.fast then
    some (((e.recv.arr.store.take len).foldl (gstep isToSorted) ([], 0)).1,
      ((e.recv.arr.store.take len).foldl (gstep isToSorted) ([], 0)).2, e)
  else gatherGen env isToSorted len 0 e ([], 0)

def writeLog (sorted : List Val) (u len : Nat) : List WB :=
  (List.range sorted.length).map (fun i => WB.store i (sorted.getD i .undef)) ++
    (List.range' sorted.length u).map (fun i => WB.store i .undef) ++
    (List.range' (sorted.length + u) (len - sorted.length - u)).map WB.del

end ArraySort
