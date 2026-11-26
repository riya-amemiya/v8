import ArrayAt.Model

namespace ArrayAt

open Torque

theorem convertRelativeIndex_spec {fadd : Int → Int → Int} (hf : FAdd fadd) {len : Nat}
    (hlen : len ≤ 2 ^ 53 - 1) (index : ExtInt) :
    convertRelativeIndex fadd index len = specAt len index := by
  cases index with
  | posInf => rfl
  | negInf => rfl
  | fin n =>
    unfold convertRelativeIndex specAt
    dsimp only
    by_cases hn : 0 ≤ n
    · rw [ite_eq_left hn]
      by_cases hl : (len : Int) ≤ n
      · rw [ite_eq_left hl, ite_eq_left ⟨fun _ => hl, fun h => absurd hn (by omega)⟩]
      · rw [ite_eq_right hl, ite_eq_right (fun h => hl (h.1 hn)), ite_eq_left hn]
    · rw [ite_eq_right hn]
      by_cases hneg : (len : Int) + n < 0
      · rw [ite_eq_left (hf.sign _ _ hneg), ite_eq_left ⟨fun h => absurd h hn, fun _ => hneg⟩]
      · have he := hf.exact len n (by omega) (by omega)
        rw [he, ite_eq_right hneg, ite_eq_right (by omega),
          ite_eq_right (fun h => hneg (h.2 (by omega))), ite_eq_right hn]

theorem convertRelativeIndex_lt {fadd : Int → Int → Int} {index : ExtInt} {len k : Nat}
    (h : convertRelativeIndex fadd index len = some k) : k < len := by
  unfold convertRelativeIndex at h
  split at h
  · cases h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        omega
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          omega

end ArrayAt
