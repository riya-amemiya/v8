import ArrayJoin.Buffer

namespace ArrayJoin

open Torque

inductive Next where
  | skip
  | str (s : Str)
  | bail
  | bad
  deriving DecidableEq, Repr

def ofConv : Option (Option Str) → Next
  | none => .bail
  | some none => .skip
  | some (some s) => if s.chars = [] then .skip else .str s

def fastNext (conv : Val → Option (Option Str)) : Kind → Option Val → Next
  | .packedSmi, some v => if v.isSmi then ofConv (conv v) else .bad
  | .packedSmi, none => .bad
  | .holeySmi, some v => if v.isSmi then ofConv (conv v) else .bad
  | .holeySmi, none => .skip
  | .packedDouble, some v => if v.isNumber then ofConv (conv v) else .bad
  | .packedDouble, none => .bad
  | .holeyDouble, some v => if v = .undef then .skip else if v.isNumber then ofConv (conv v) else .bad
  | .holeyDouble, none => .skip
  | .packedElem, some v => ofConv (conv v)
  | .packedElem, none => .bail
  | .holeyElem, some v => ofConv (conv v)
  | .holeyElem, none => .skip
  | .slow, _ => .bad

def fastLoop (l : Limits) (conv : Val → Option (Option Str)) (kind : Kind)
    (store : List (Option Val)) (sep : Str) (cur : Nat) (k : Nat) (b : Buf) (nof : Nat) :
    Res (Buf × Nat) :=
  if _h : k < cur then
    match store[k]? with
    | none => .fatal
    | some x =>
      match fastNext conv kind x with
      | .skip => fastLoop l conv kind store sep cur (k + 1) b (if 0 < k then nof + 1 else nof)
      | .bail => .bailout
      | .bad => .ub
      | .str s =>
        (add l b s (if 0 < k then nof + 1 else nof) sep.len).bind fun b' =>
          fastLoop l conv kind store sep cur (k + 1) b' 0
  else .ok (b, nof)
termination_by cur - k

def finalSeps (k extra nof : Nat) : Nat :=
  if 0 < extra then (if 0 < k then nof + 1 else nof) + (extra - 1) else nof

def fastArrayJoin (l : Limits) (conv : Val → Option (Option Str)) (a : JSArr) (sep : Str)
    (len : Nat) : Res (List Nat) :=
  if 1 < sep.len ∧ 1 < len ∧ l.strMax < (len - 1) * sep.len then .throws
  else
    (fastLoop l conv a.kind a.store sep (min len a.length) 0 (newBuffer l len) 0).bind fun r =>
      (addSeparators l r.1 (finalSeps (min len a.length) (len - a.length) r.2) sep.len true).bind
        fun b => bufferJoin b sep

def fastPiece (conv : Val → Option (Option Str)) (kind : Kind) (x : Option Val) : List Nat :=
  match fastNext conv kind x with
  | .str s => s.chars
  | _ => []

def fastSpec (conv : Val → Option (Option Str)) (a : JSArr) (sep : List Nat) (len : Nat) :
    List Nat :=
  joinPieces sep ((a.store.take (min len a.length)).map (fastPiece conv a.kind) ++
    List.replicate (len - a.length) [])

end ArrayJoin
