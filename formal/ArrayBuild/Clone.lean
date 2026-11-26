import ArrayBuild.StoreSafety

namespace ArrayBuild

open Torque

inductive CloneResult where
  | done (a : JSArr)
  | ub
  deriving Repr

def holeToUndef : Option Val → Option Val
  | none => some .undef
  | some v => some v

def cloneKind (a : JSArr) (converted : Bool) : Kind :=
  if converted = true ∨ a.fast = false then .packedElem else a.kind

def cloneFastJSArray (convert : Bool) (a : JSArr) : CloneResult :=
  if a.length = 0 then
    .done ⟨cloneKind a false, true, true, a.forCopy, false, 0, []⟩
  else if convert = true ∧ a.kind.isHoley = true then
    if a.store.length < a.length then .ub
    else
      .done ⟨cloneKind a (a.elems.any (· == none)), true, true, a.forCopy, false, a.length,
        a.elems.map holeToUndef⟩
  else if a.cow = true then
    .done ⟨cloneKind a false, true, true, a.forCopy, true, a.length, a.store⟩
  else if a.store.length < a.length then .ub
  else .done ⟨cloneKind a false, true, true, a.forCopy, false, a.length, a.elems⟩

def cloneElems (convert : Bool) (a : JSArr) : List (Option Val) :=
  if convert = true ∧ a.kind.isHoley = true then a.elems.map holeToUndef else a.elems

end ArrayBuild
