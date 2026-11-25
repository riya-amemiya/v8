import ArrayFlat.Lemmas

namespace ArrayFlat

open Torque

structure P1 where
  cur : Frame
  stack : List Frame
  tl : Nat
  seenSmi : Bool
  seenDouble : Bool
  seenObject : Bool

def P1.targetKind (s : P1) : Kind :=
  if s.seenObject then .packedElem else if s.seenDouble then .packedDouble else .packedSmi

def P1.measure (H : Heap) (s : P1) : Nat := frameMeasure H s.cur s.stack

def step1 (cfg : Config) (H : Heap) (s : P1) : Step P1 (Nat × Kind) :=
  match fetch H s.cur with
  | .exhausted =>
    match s.stack with
    | [] => .done (s.tl, s.targetKind)
    | g :: rest =>
      if (H g.arr).forRead then .cont { s with cur := g, stack := rest } else .bailout
  | .bail => .bailout
  | .oob => .ub
  | .elem none => .cont { s with cur := s.cur.next }
  | .elem (some v) =>
    match descend? s.cur.depth v with
    | some (d, q) =>
      if (H q).forRead = false then .bailout
      else if (H q).kind = .packedSmi then
        if cfg.smiMax < (H q).length then .bailout
        else if cfg.smiMax < s.tl + (H q).length then .bailout
        else if cfg.maxLen < s.tl + (H q).length then .throwRange
        else .cont { s with cur := s.cur.next, tl := s.tl + (H q).length, seenSmi := true }
      else if (H q).kind = .packedDouble then
        if cfg.smiMax < (H q).length then .bailout
        else if cfg.smiMax < s.tl + (H q).length then .bailout
        else if cfg.maxLen < s.tl + (H q).length then .throwRange
        else .cont { s with cur := s.cur.next, tl := s.tl + (H q).length, seenDouble := true }
      else if cfg.smiMax < s.cur.idx + 1 then .bailout
      else if kMaxFlatFastStackEntries ≤ 4 * s.stack.length then .bailout
      else if cfg.smiMax < (H q).length then .bailout
      else .cont { s with cur := ⟨q, (H q).length, 0, d⟩, stack := s.cur.next :: s.stack }
    | none =>
      if 0 < s.cur.depth ∧ v = .proxy then .bailout
      else if cfg.smiMax < s.tl + 1 then .bailout
      else if cfg.maxLen < s.tl + 1 then .throwRange
      else .cont { s with
        cur := s.cur.next
        tl := s.tl + 1
        seenObject := s.seenObject || !v.isNumber
        seenDouble := s.seenDouble || (v.isNumber && !v.isSmi)
        seenSmi := s.seenSmi || v.isSmi }

theorem step1_decreases (cfg : Config) (H : Heap) (s s' : P1)
    (h : step1 cfg H s = .cont s') : s'.measure H < s.measure H := by
  unfold step1 at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hs : s.stack with
    | nil => simp [hs] at h
    | cons g rest =>
      simp only [hs] at h
      split at h
      · cases h
        simp only [P1.measure, hs]
        exact measure_pop g rest hf
      · cases h
  | bail => simp [hf] at h
  | oob => simp [hf] at h
  | elem x =>
    cases x with
    | none =>
      simp only [hf] at h
      cases h
      exact measure_hole s.stack hf
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        exact measure_leaf s.stack hf hd
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        · exact measure_skip s.stack hf hd
        · exact measure_skip s.stack hf hd
        · exact measure_descend s.stack hf hd

def run1 (cfg : Config) (H : Heap) : P1 → Outcome (Nat × Kind) :=
  run (step1 cfg H) (P1.measure H) (step1_decreases cfg H)

structure P2 where
  cur : Frame
  stack : List Frame
  ti : Nat
  buf : List (Option Val)

def P2.measure (H : Heap) (s : P2) : Nat := frameMeasure H s.cur s.stack

def stepGen (cfg : Config) (H : Heap) (s : P2) : Step P2 P2 :=
  match fetch H s.cur with
  | .exhausted =>
    match s.stack with
    | [] => .done s
    | g :: rest =>
      if (H g.arr).forRead then .cont { s with cur := g, stack := rest } else .bailout
  | .bail => .bailout
  | .oob => .ub
  | .elem none => .cont { s with cur := s.cur.next }
  | .elem (some v) =>
    match descend? s.cur.depth v with
    | some (d, q) =>
      if (H q).kind = .packedSmi then
        if cfg.smiMax < (H q).length then .bailout
        else if cfg.smiMax < s.ti + (H q).length then .bailout
        else if s.buf.length < s.ti + (H q).length then .bailout
        else if s.ti + (H q).length ≤ s.buf.length ∧ (H q).length ≤ (H q).store.length then
          .cont { s with
            cur := s.cur.next
            ti := s.ti + (H q).length
            buf := blit s.buf s.ti ((H q).store.take (H q).length) }
        else .ub
      else if (H q).forRead = false then .bailout
      else if cfg.smiMax < s.cur.idx + 1 then .bailout
      else if kMaxFlatFastStackEntries ≤ 4 * s.stack.length then .bailout
      else if cfg.smiMax < (H q).length then .bailout
      else .cont { s with cur := ⟨q, (H q).length, 0, d⟩, stack := s.cur.next :: s.stack }
    | none =>
      if 0 < s.cur.depth ∧ v = .proxy then .bailout
      else if s.buf.length ≤ s.ti then .bailout
      else if s.ti < s.buf.length then
        .cont { s with cur := s.cur.next, ti := s.ti + 1, buf := blit s.buf s.ti [some v] }
      else .ub

def stepDbl (cfg : Config) (H : Heap) (s : P2) : Step P2 P2 :=
  match fetch H s.cur with
  | .exhausted =>
    match s.stack with
    | [] => .done s
    | g :: rest =>
      if (H g.arr).forRead then .cont { s with cur := g, stack := rest } else .bailout
  | .bail => .bailout
  | .oob => .ub
  | .elem none => .cont { s with cur := s.cur.next }
  | .elem (some v) =>
    match descend? s.cur.depth v with
    | some (d, q) =>
      if (H q).kind = .packedDouble then
        if cfg.smiMax < (H q).length then .bailout
        else if cfg.smiMax < s.ti + (H q).length then .bailout
        else if s.buf.length < s.ti + (H q).length then .bailout
        else if s.ti + (H q).length ≤ s.buf.length ∧ (H q).length ≤ (H q).store.length then
          .cont { s with
            cur := s.cur.next
            ti := s.ti + (H q).length
            buf := blit s.buf s.ti ((H q).store.take (H q).length) }
        else .ub
      else if (H q).forRead = false then .bailout
      else if cfg.smiMax < s.cur.idx + 1 then .bailout
      else if cfg.smiMax < (H q).length then .bailout
      else .cont { s with cur := ⟨q, (H q).length, 0, d⟩, stack := s.cur.next :: s.stack }
    | none =>
      if 0 < s.cur.depth ∧ v = .proxy then .bailout
      else if s.buf.length ≤ s.ti then .bailout
      else if v.isNumber = false then .ub
      else if s.ti < s.buf.length then
        .cont { s with cur := s.cur.next, ti := s.ti + 1, buf := blit s.buf s.ti [some v] }
      else .ub

theorem stepGen_decreases (cfg : Config) (H : Heap) (s s' : P2)
    (h : stepGen cfg H s = .cont s') : s'.measure H < s.measure H := by
  unfold stepGen at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hs : s.stack with
    | nil => simp [hs] at h
    | cons g rest =>
      simp only [hs] at h
      split at h
      · cases h
        simp only [P2.measure, hs]
        exact measure_pop g rest hf
      · cases h
  | bail => simp [hf] at h
  | oob => simp [hf] at h
  | elem x =>
    cases x with
    | none =>
      simp only [hf] at h
      cases h
      exact measure_hole s.stack hf
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        exact measure_leaf s.stack hf hd
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        · exact measure_skip s.stack hf hd
        · exact measure_descend s.stack hf hd

theorem stepDbl_decreases (cfg : Config) (H : Heap) (s s' : P2)
    (h : stepDbl cfg H s = .cont s') : s'.measure H < s.measure H := by
  unfold stepDbl at h
  cases hf : fetch H s.cur with
  | exhausted =>
    simp only [hf] at h
    cases hs : s.stack with
    | nil => simp [hs] at h
    | cons g rest =>
      simp only [hs] at h
      split at h
      · cases h
        simp only [P2.measure, hs]
        exact measure_pop g rest hf
      · cases h
  | bail => simp [hf] at h
  | oob => simp [hf] at h
  | elem x =>
    cases x with
    | none =>
      simp only [hf] at h
      cases h
      exact measure_hole s.stack hf
    | some v =>
      simp only [hf] at h
      cases hd : descend? s.cur.depth v with
      | none =>
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        exact measure_leaf s.stack hf hd
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only [hd] at h
        repeat' split at h
        all_goals cases h
        · exact measure_skip s.stack hf hd
        · exact measure_descend s.stack hf hd

def runGen (cfg : Config) (H : Heap) : P2 → Outcome P2 :=
  run (stepGen cfg H) (P2.measure H) (stepGen_decreases cfg H)

def runDbl (cfg : Config) (H : Heap) : P2 → Outcome P2 :=
  run (stepDbl cfg H) (P2.measure H) (stepDbl_decreases cfg H)

def init1 (root srcLen depth : Nat) : P1 :=
  ⟨⟨root, srcLen, 0, depth⟩, [], 0, false, false, false⟩

def init2 (root srcLen depth len : Nat) : P2 :=
  ⟨⟨root, srcLen, 0, depth⟩, [], 0, List.replicate len none⟩

def calcLength (cfg : Config) (H : Heap) (root srcLen depth : Nat) : Outcome (Nat × Kind) :=
  if (H root).kind = .packedSmi ∨ (H root).kind = .packedDouble then
    .ok (srcLen, (H root).kind)
  else if (H root).forRead = false then .bailout
  else run1 cfg H (init1 root srcLen depth)

def finish (len : Nat) (k : Kind) : Outcome P2 → Outcome JSArr
  | .ok s => if s.ti = len then .ok ⟨k, true, true, true, false, len, s.buf⟩ else .bailout
  | .bailout => .bailout
  | .throwRange => .throwRange
  | .ub => .ub
  | .fatal => .fatal

def tryFastFlat (cfg : Config) (H : Heap) (root srcLen depth : Nat) : Outcome JSArr :=
  if cfg.smiMax < srcLen then .bailout
  else if (H root).forCopy = false then .bailout
  else match calcLength cfg H root srcLen depth with
    | .ok (len, k) =>
      if len = 0 then .ok ⟨.packedSmi, true, true, true, false, 0, []⟩
      else if cfg.maxLen < len then .fatal
      else if (H root).forRead = false then .bailout
      else if k = .packedDouble then finish len k (runDbl cfg H (init2 root srcLen depth len))
      else finish len k (runGen cfg H (init2 root srcLen depth len))
    | .bailout => .bailout
    | .throwRange => .throwRange
    | .ub => .ub
    | .fatal => .fatal

end ArrayFlat
