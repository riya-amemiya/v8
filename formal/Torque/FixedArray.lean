import Torque.JSArray

namespace Torque

def blit (buf : List (Option Val)) (pos : Nat) (src : List (Option Val)) :
    List (Option Val) :=
  buf.take pos ++ src ++ buf.drop (pos + src.length)

def moveElements (store : List (Option Val)) (dst src count : Nat) : List (Option Val) :=
  blit store dst ((store.drop src).take count)

def ensureWritable (a : JSArr) : JSArr :=
  if a.cow then { a with cow := false, store := a.store.take a.length } else a

def growTo (store : List (Option Val)) (n : Nat) : List (Option Val) :=
  store ++ List.replicate (n - store.length) none

theorem blit_spec (out : List Val) (src : List (Option Val)) (k : Nat) :
    blit (out.map some ++ List.replicate k none) out.length src =
      out.map some ++ src ++ List.replicate (k - src.length) none := by
  have h1 : (out.map some ++ List.replicate k none).take out.length = out.map some := by
    simp
  have h2 : (out.map some ++ List.replicate k none).drop (out.length + src.length) =
      List.replicate (k - src.length) none := by
    rw [List.drop_append]
    simp [List.drop_replicate]
  simp only [blit, h1, h2]

theorem length_blit {buf src : List (Option Val)} {pos : Nat}
    (h : pos + src.length ≤ buf.length) : (blit buf pos src).length = buf.length := by
  simp [blit, List.length_take]
  omega

theorem getElem?_blit {buf src : List (Option Val)} {pos : Nat}
    (h : pos + src.length ≤ buf.length) (j : Nat) :
    (blit buf pos src)[j]? =
      if j < pos then buf[j]? else if j < pos + src.length then src[j - pos]? else buf[j]? := by
  have htake : (buf.take pos).length = pos := by
    simp [List.length_take]
    omega
  unfold blit
  rw [List.append_assoc]
  by_cases h1 : j < pos
  · rw [List.getElem?_append_left (by omega), List.getElem?_take]
    simp [h1]
  · rw [List.getElem?_append_right (by omega), htake]
    by_cases h2 : j < pos + src.length
    · rw [List.getElem?_append_left (by omega)]
      simp [h1, h2]
    · rw [List.getElem?_append_right (by omega), List.getElem?_drop]
      simp only [h1, h2, ite_false]
      congr 1
      omega

theorem getElem?_moveElements {store : List (Option Val)} {dst src count : Nat}
    (hd : dst + count ≤ store.length) (hs : src + count ≤ store.length) (j : Nat) :
    (moveElements store dst src count)[j]? =
      if dst ≤ j ∧ j < dst + count then store[src + (j - dst)]? else store[j]? := by
  have hlen : ((store.drop src).take count).length = count := by
    simp [List.length_take, List.length_drop]
    omega
  unfold moveElements
  rw [getElem?_blit (by omega), hlen]
  by_cases h1 : j < dst
  · simp [h1]
    omega
  · by_cases h2 : j < dst + count
    · simp only [h1, h2, ite_false, ite_true, List.getElem?_take, List.getElem?_drop]
      simp [show j - dst < count by omega, show dst ≤ j by omega]
    · simp only [h1, h2, ite_false]
      simp

theorem length_moveElements {store : List (Option Val)} {dst src count : Nat}
    (hd : dst + count ≤ store.length) :
    (moveElements store dst src count).length = store.length := by
  apply length_blit
  simp [List.length_take, List.length_drop]
  omega

end Torque
