import ArrayFlat.Model

namespace ArrayFlat

open Torque

theorem descend?_some {d : Nat} {v : Val} {d' q : Nat} (h : descend? d v = some (d', q)) :
    d = d' + 1 ∧ v = .arr q := by
  cases d with
  | zero => simp [descend?] at h
  | succ n =>
    cases v <;> simp [descend?] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem descend?_none_of_ne {d : Nat} {v : Val} (h : ∀ p, v ≠ .arr p) : descend? d v = none := by
  cases d with
  | zero => rfl
  | succ n =>
    cases v with
    | arr p => exact absurd rfl (h p)
    | _ => rfl

theorem leaves_nil (H : Heap) (d : Nat) : leaves H d [] = [] := by
  cases d <;> simp [leaves]

theorem leaves_none (H : Heap) (d : Nat) (l : List (Option Val)) :
    leaves H d (none :: l) = leaves H d l := by
  cases d <;> simp [leaves]

theorem leaves_descend (H : Heap) {d d' q : Nat} {v : Val} (l : List (Option Val))
    (h : descend? d v = some (d', q)) :
    leaves H d (some v :: l) = leaves H d' (H q).elems ++ leaves H d l := by
  obtain ⟨rfl, rfl⟩ := descend?_some h
  simp [leaves]

theorem leaves_leaf (H : Heap) {d : Nat} {v : Val} (l : List (Option Val))
    (h : descend? d v = none) :
    leaves H d (some v :: l) = v :: leaves H d l := by
  cases d with
  | zero => simp [leaves]
  | succ n =>
    cases v <;> simp_all [leaves, descend?]

theorem leaves_of_noArr (H : Heap) (d : Nat) :
    ∀ l : List (Option Val), (∀ x ∈ l, ∃ v, x = some v ∧ ∀ p, v ≠ .arr p) →
      leaves H d l = l.filterMap id
  | [], _ => by simp [leaves_nil]
  | x :: l, hl => by
    obtain ⟨v, rfl, hv⟩ := hl x (by simp)
    rw [leaves_leaf H l (descend?_none_of_ne hv),
      leaves_of_noArr H d l (fun y hy => hl y (by simp [hy]))]
    simp

theorem leaves_numeric (H : Heap) (d : Nat) {a : JSArr} (hw : a.WF)
    (hk : a.kind = .packedSmi ∨ a.kind = .packedDouble) :
    leaves H d a.elems = a.elems.filterMap id := by
  apply leaves_of_noArr
  intro x hx
  obtain ⟨v, rfl, hv⟩ := numeric_elems hw hk x hx
  exact ⟨v, rfl, not_arr_of_isNumber hv⟩

theorem leaves_numeric_length (H : Heap) (d : Nat) {a : JSArr} (hw : a.WF)
    (hk : a.kind = .packedSmi ∨ a.kind = .packedDouble) :
    (leaves H d a.elems).length = a.length := by
  rw [leaves_numeric H d hw hk, length_filterMap_id_of_all_some _ (numeric_elems_some hw hk),
    JSArr.elems_length hw]

theorem leaves_numeric_map_some (H : Heap) (d : Nat) {a : JSArr} (hw : a.WF)
    (hk : a.kind = .packedSmi ∨ a.kind = .packedDouble) :
    (leaves H d a.elems).map some = a.elems := by
  rw [leaves_numeric H d hw hk, map_some_filterMap_id _ (numeric_elems_some hw hk)]

theorem cost_nil (H : Heap) (d : Nat) : cost H d [] = 1 := by
  cases d <;> simp [cost]

theorem cost_cons_none (H : Heap) (d : Nat) (l : List (Option Val)) :
    cost H d (none :: l) = cost H d l + 1 := by
  cases d <;> simp [cost] <;> omega

theorem cost_cons_descend (H : Heap) {d d' q : Nat} {v : Val} (l : List (Option Val))
    (h : descend? d v = some (d', q)) :
    cost H d (some v :: l) = cost H d' (H q).elems + 1 + cost H d l := by
  obtain ⟨rfl, rfl⟩ := descend?_some h
  simp [cost]
  omega

theorem cost_cons_leaf (H : Heap) {d : Nat} {v : Val} (l : List (Option Val))
    (h : descend? d v = none) : cost H d (some v :: l) = cost H d l + 1 := by
  cases d with
  | zero => simp [cost]
  | succ n =>
    cases v <;> simp_all [cost, descend?] <;> omega

theorem rest_of_elem {H : Heap} {f : Frame} {x : Option Val} (h : fetch H f = .elem x) :
    f.rest H = x :: f.next.rest H := by
  unfold fetch at h
  split at h
  · rename_i hlt
    split at h
    · cases h
    · rename_i hle
      split at h
      · rename_i y hy
        cases h
        have hlen : f.idx < (H f.arr).store.length := by
          rcases List.getElem?_eq_some_iff.mp hy with ⟨hb, _⟩
          exact hb
        have hl : f.idx < ((H f.arr).elems.take f.len).length := by
          simp [JSArr.elems, List.length_take]
          omega
        simp only [Frame.rest, Frame.next]
        rw [List.drop_eq_getElem_cons hl]
        congr 1
        rcases List.getElem?_eq_some_iff.mp hy with ⟨_, hy'⟩
        simp [JSArr.elems, List.getElem_take, hy']
      · cases h
  · cases h

theorem rest_of_exhausted {H : Heap} {f : Frame} (h : fetch H f = .exhausted) :
    f.rest H = [] := by
  unfold fetch at h
  split at h
  · split at h
    · cases h
    · split at h <;> cases h
  · rename_i hge
    simp only [Frame.rest]
    apply List.drop_eq_nil_of_le
    simp [List.length_take]
    omega

theorem fetch_ne_oob {H : Heap} {f : Frame} (hw : (H f.arr).WF) : fetch H f ≠ .oob := by
  unfold fetch
  split
  · split
    · simp
    · rename_i hle
      have : f.idx < (H f.arr).store.length := by
        have := hw.length_le
        omega
      rw [List.getElem?_eq_getElem this]
      simp
  · simp

theorem Frame.rest_new (H : Heap) (q d : Nat) :
    (⟨q, (H q).length, 0, d⟩ : Frame).rest H = (H q).elems := by
  simp [Frame.rest, JSArr.elems, List.take_take]

theorem pending_of_hole {H : Heap} {f : Frame} (h : fetch H f = .elem none) :
    f.pending H = f.next.pending H := by
  simp only [Frame.pending, rest_of_elem h, leaves_none]
  rfl

theorem pending_of_leaf {H : Heap} {f : Frame} {v : Val} (h : fetch H f = .elem (some v))
    (hd : descend? f.depth v = none) : f.pending H = v :: f.next.pending H := by
  simp only [Frame.pending, rest_of_elem h, leaves_leaf H _ hd]
  rfl

theorem pending_of_descend {H : Heap} {f : Frame} {v : Val} {d q : Nat}
    (h : fetch H f = .elem (some v)) (hd : descend? f.depth v = some (d, q)) :
    f.pending H = leaves H d (H q).elems ++ f.next.pending H := by
  simp only [Frame.pending, rest_of_elem h, leaves_descend H _ hd]
  rfl

theorem pending_of_exhausted {H : Heap} {f : Frame} (h : fetch H f = .exhausted) :
    f.pending H = [] := by
  simp [Frame.pending, rest_of_exhausted h, leaves_nil]

theorem Frame.pending_new (H : Heap) (q d : Nat) :
    (⟨q, (H q).length, 0, d⟩ : Frame).pending H = leaves H d (H q).elems := by
  simp [Frame.pending, Frame.rest_new]

theorem pendingAll_hole {H : Heap} {f : Frame} (S : List Frame) (h : fetch H f = .elem none) :
    pendingAll H f S = pendingAll H f.next S := by
  simp [pendingAll, pending_of_hole h]

theorem pendingAll_leaf {H : Heap} {f : Frame} {v : Val} (S : List Frame)
    (h : fetch H f = .elem (some v)) (hd : descend? f.depth v = none) :
    pendingAll H f S = v :: pendingAll H f.next S := by
  simp [pendingAll, pending_of_leaf h hd]

theorem pendingAll_skip {H : Heap} {f : Frame} {v : Val} {d q : Nat} (S : List Frame)
    (h : fetch H f = .elem (some v)) (hd : descend? f.depth v = some (d, q)) :
    pendingAll H f S = leaves H d (H q).elems ++ pendingAll H f.next S := by
  simp [pendingAll, pending_of_descend h hd]

theorem pendingAll_descend {H : Heap} {f : Frame} {v : Val} {d q : Nat} (S : List Frame)
    (h : fetch H f = .elem (some v)) (hd : descend? f.depth v = some (d, q)) :
    pendingAll H f S = pendingAll H ⟨q, (H q).length, 0, d⟩ (f.next :: S) := by
  simp [pendingAll, pending_of_descend h hd, Frame.pending_new]

theorem pendingAll_pop {H : Heap} {f : Frame} (g : Frame) (S : List Frame)
    (h : fetch H f = .exhausted) : pendingAll H f (g :: S) = pendingAll H g S := by
  simp [pendingAll, pending_of_exhausted h]

theorem pendingAll_done {H : Heap} {f : Frame} (h : fetch H f = .exhausted) :
    pendingAll H f [] = [] := by
  simp [pendingAll, pending_of_exhausted h]

theorem measure_hole {H : Heap} {f : Frame} (S : List Frame) (h : fetch H f = .elem none) :
    frameMeasure H f.next S < frameMeasure H f S := by
  simp only [frameMeasure, Frame.cost, rest_of_elem h, cost_cons_none]
  simp only [Frame.next]
  omega

theorem measure_leaf {H : Heap} {f : Frame} {v : Val} (S : List Frame)
    (h : fetch H f = .elem (some v)) (hd : descend? f.depth v = none) :
    frameMeasure H f.next S < frameMeasure H f S := by
  simp only [frameMeasure, Frame.cost, rest_of_elem h, cost_cons_leaf H _ hd]
  simp only [Frame.next]
  omega

theorem measure_skip {H : Heap} {f : Frame} {v : Val} {d q : Nat} (S : List Frame)
    (h : fetch H f = .elem (some v)) (hd : descend? f.depth v = some (d, q)) :
    frameMeasure H f.next S < frameMeasure H f S := by
  simp only [frameMeasure, Frame.cost, rest_of_elem h, cost_cons_descend H _ hd]
  simp only [Frame.next]
  omega

theorem measure_descend {H : Heap} {f : Frame} {v : Val} {d q : Nat} (S : List Frame)
    (h : fetch H f = .elem (some v)) (hd : descend? f.depth v = some (d, q)) :
    frameMeasure H ⟨q, (H q).length, 0, d⟩ (f.next :: S) < frameMeasure H f S := by
  simp only [frameMeasure, Frame.cost, rest_of_elem h, cost_cons_descend H _ hd,
    Frame.rest_new, List.map_cons, List.sum_cons]
  simp only [Frame.next]
  omega

theorem measure_pop {H : Heap} {f : Frame} (g : Frame) (S : List Frame)
    (h : fetch H f = .exhausted) : frameMeasure H g S < frameMeasure H f (g :: S) := by
  simp only [frameMeasure, Frame.cost, rest_of_exhausted h, cost_nil, List.map_cons,
    List.sum_cons]
  omega

end ArrayFlat
