import ArrayFill.Safety

namespace ArrayFill.Examples

open Torque

def cfg : FillConfig := ⟨16, 4, true⟩

def env : Env := ⟨true, false, false, true⟩

def mk (kind : Kind) (xs : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, xs.length, xs⟩

def smis (ns : List Int) : List (Option Val) := ns.map fun n => some (.smi n)

def view : Result → Option (Kind × Nat × List (Option Val) × Bool)
  | .done a d => some (a.kind, a.length, a.elems, d)
  | _ => none

def isSlow : Result → Bool
  | .slow => true
  | _ => false

#guard view (fastPath cfg env (mk .packedSmi (smis [1, 2, 3, 4, 5])) (.smi 0) 5
    ⟨some 1, some 3⟩) == some (.packedSmi, 5, smis [1, 0, 0, 4, 5], false)

#guard view (fastPath cfg env (mk .packedSmi (smis [1, 2, 3, 4, 5])) (.smi 9) 5
    ⟨some (-2), none⟩) == some (.packedSmi, 5, smis [1, 2, 3, 9, 9], false)

#guard view (fastPath cfg env (mk .packedSmi (smis [1, 2, 3])) (.num 7) 3 ⟨some 1, some 2⟩) ==
  some (.packedDouble, 3, [some (.smi 1), some (.num 7), some (.smi 3)], false)

#guard view (fastPath cfg env (mk .holeySmi [some (.smi 1), none, some (.smi 3)]) .other 3
    ⟨some 2, none⟩) == some (.holeyElem, 3, [some (.smi 1), none, some .other], false)

#guard view (fastPath cfg env (mk .packedElem [some .other, some .other]) (.smi 5) 2
    ⟨none, none⟩) == some (.packedSmi, 2, smis [5, 5], false)

#guard view (fastPath cfg { env with replaced := false } (mk .packedElem [some .other, some .other])
    (.smi 5) 2 ⟨none, none⟩) == some (.packedElem, 2, smis [5, 5], false)

#guard view (fastPath cfg env (mk .packedDouble [some (.num 1), some (.num 2)]) .undef 2
    ⟨some 1, none⟩) == some (.holeyDouble, 2, [some (.num 1), some .undef], false)

#guard view (fastPath { cfg with undefinedDouble := false } env
    (mk .packedDouble [some (.num 1), some (.num 2)]) .undef 2 ⟨some 1, none⟩) ==
  some (.packedElem, 2, [some (.num 1), some .undef], false)

#guard view (fastPath cfg env { mk .packedSmi (smis [1, 2, 3]) with cow := true } (.smi 0) 3
    ⟨some 1, none⟩) == some (.packedSmi, 3, smis [1, 0, 0], false)

#guard view (fastPath cfg env (mk .packedSmi (smis [1])) (.smi 7) 8 ⟨some 3, none⟩) ==
  some (.holeySmi, 8, [some (.smi 1), none, none] ++ smis [7, 7, 7, 7, 7], true)

#guard view (fastPath cfg env (mk .packedSmi (smis [1])) (.smi 7) 4 ⟨some 2, none⟩) ==
  some (.holeySmi, 4, [some (.smi 1), none] ++ smis [7, 7], false)

#guard isSlow (fastPath cfg env (mk .packedSmi (smis [1])) (.smi 7) 17 ⟨some 2, none⟩)

#guard isSlow (fastPath cfg { env with readOnlyLength := true } (mk .packedSmi (smis [1])) (.smi 7)
    4 ⟨some 2, none⟩)

#guard view (fastPath cfg { env with readOnlyLength := true } (mk .packedSmi (smis [1, 2, 3, 4]))
    (.smi 7) 4 ⟨some 2, none⟩) == some (.packedSmi, 4, smis [1, 2, 7, 7], false)

#guard (accessorFill cfg (mk .packedDouble [some (.num 1)]) .other 0 1).isNone

#guard (accessorFill cfg { mk .packedDouble [some (.num 1)] with cow := true } (.num 2) 0 1).isNone

#guard !kindOk .packedSmi none

def v8 : FillConfig := ⟨128 * 1024 * 1024, 32 * 1024 * 1024, true⟩

def shrunk : JSArr := mk .packedSmi (smis [0])

theorem dcheck_reachable :
    ∃ a', fastPath v8 env shrunk (.smi 1) (32 * 1024 * 1024 + 1) ⟨some 0, none⟩ = .done a' true := by
  have hw : shrunk.WF := {
    length_le := Nat.le_refl _
    kind_ok := by decide
    forRead_fast := fun _ => rfl
    fast_forRead := fun _ => rfl
    forCopy_fast := fun _ => rfl
    cow_not_double := nofun }
  have hsl : shrunk.SlackHoles := by
    intro x hx
    simp [shrunk, mk] at hx
  have hs : startIndex (32 * 1024 * 1024 + 1) ⟨some 0, none⟩ = 0 := rfl
  have he : endIndex (32 * 1024 * 1024 + 1) ⟨some 0, none⟩ = 32 * 1024 * 1024 + 1 := rfl
  unfold fastPath
  rw [hs, he, ite_eq_right (by decide)]
  obtain ⟨a', d, h⟩ := tryFast_handles (c := v8) (env := env) (v := .smi 1) (start := 0)
    (fin := 32 * 1024 * 1024 + 1) hw (Nat.zero_le _) (by decide) rfl rfl rfl (by decide) rfl
  have hd := (tryFast_done hw hsl (by decide) h).2.2.2.2.2
  have : d = true := hd.mpr ⟨by decide, by decide⟩
  subst this
  exact ⟨a', h⟩

end ArrayFill.Examples
