import ArrayBuild

namespace ArrayConcat

open Torque ArrayBuild

structure Env where
  concatSpreadable : Bool

inductive Result where
  | done (a : JSArr)
  | generic
  | ub
  deriving Repr

def ofClone : CloneResult → Result
  | .done a => .done a
  | .ub => .ub

def forConcat (env : Env) (a : JSArr) : Bool := env.concatSpreadable && a.forCopy

def fastPath (env : Env) (H : Heap) (receiver : Val) (args : List Val) : Result :=
  match receiver with
  | .arr p =>
    if args = [] ∧ forConcat env (H p) = true then ofClone (cloneFastJSArray false (H p))
    else if forConcat env (H p) = true ∧ (H p).length = 0 then
      match args with
      | [.arr q] =>
        if (H q).forCopy = true then ofClone (cloneFastJSArray false (H q)) else .generic
      | _ => .generic
    else .generic
  | _ => .generic

def specConcat (items : List JSArr) : List (Option Val) := (items.map JSArr.elems).flatten

end ArrayConcat
