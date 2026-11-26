import InPlace

namespace ArrayShift

open Torque InPlace

def kMinAddedElementsCapacity : Nat := 16

def kMaxCopyElements : Nat := 100

def shiftElements (b : JSArr) : Res (Option Val × List (Option Val)) := do
  castElements b.kind b.store
  let result ← loadSlot b.store 0
  castElements b.kind b.store
  let s1 ← memmove b.cow b.store 0 1 (b.length - 1)
  castElements b.kind s1
  let s2 ← storeSlot b.cow s1 (b.length - 1 : Nat) none
  pure (result, s2)

def tryFast (c : Config) (m : MapInfo) (a : JSArr) : Result Val :=
  if a.fast = false then .slow
  else if m.pushable = false then .slow
  else (ensureWritableChecked c a).then fun b =>
    if b.length = 0 then .done b .undef
    else if 2 * (b.length - 1) + kMinAddedElementsCapacity < b.store.length then .slow
    else if kMaxCopyElements < b.length - 1 then .slow
    else (shiftElements b).then fun (result, s2) =>
      .done { b with length := b.length - 1, store := s2 } (result.getD .undef)

def specShift : List (Option Val) → List (Option Val) × Val
  | [] => ([], .undef)
  | first :: rest => (rest, first.getD .undef)

end ArrayShift
