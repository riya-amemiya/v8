import ArrayIsArray.Model

namespace ArrayIsArray

open Torque

theorem isArray_spec (proxyTarget : Option Bool) (v : Val) :
    (∃ b, isArray v = .value b ∧ specIsArray proxyTarget v = some b) ∨
      (isArray v = .runtime ∧ v = .proxy) := by
  cases v with
  | arr p => exact Or.inl ⟨true, rfl, rfl⟩
  | proxy => exact Or.inr ⟨rfl, rfl⟩
  | smi n => exact Or.inl ⟨false, rfl, rfl⟩
  | num n => exact Or.inl ⟨false, rfl, rfl⟩
  | undef => exact Or.inl ⟨false, rfl, rfl⟩
  | other => exact Or.inl ⟨false, rfl, rfl⟩

end ArrayIsArray
