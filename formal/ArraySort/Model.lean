import Torque

namespace ArraySort

open Torque

def kMaxMergePending : Int := 85

def kMinGallopWins : Int := 7

def kMaxBinaryInsertionSortLength : Int := 16

def kSortStateTempSize : Int := 32

structure Core where
  work : List (Option Val)
  temp : List (Option Val)
  runs : List Int
  powers : List Int
  size : Int
  minGallop : Int
  deriving Repr

def Core.init (work : List (Option Val)) : Core := ⟨work, [], [], [], 0, kMinGallopWins⟩

inductive Arr where
  | work
  | temp
  deriving DecidableEq, Repr

def Core.get (c : Core) : Arr → List (Option Val)
  | .work => c.work
  | .temp => c.temp

def Core.put (c : Core) : Arr → List (Option Val) → Core
  | .work, l => { c with work := l }
  | .temp, l => { c with temp := l }

inductive Res (ε α : Type) where
  | ok (a : α) (e : ε) (c : Core)
  | throw (e : ε)
  | ub
  | abort

def M (ε α : Type) : Type := ε → Core → Res ε α

def M.pure {ε α : Type} (a : α) : M ε α := fun e c => .ok a e c

def M.bind {ε α β : Type} (m : M ε α) (f : α → M ε β) : M ε β := fun e c =>
  match m e c with
  | .ok a e' c' => f a e' c'
  | .throw e' => .throw e'
  | .ub => .ub
  | .abort => .abort

instance {ε : Type} : Monad (M ε) where
  pure := M.pure
  bind := M.bind

abbrev Cmp (ε : Type) : Type := ε → Val → Val → Option (Int × ε)

section

variable {ε : Type}

def ub {α : Type} : M ε α := fun _ _ => .ub

def abort {α : Type} : M ε α := fun _ _ => .abort

def dcheck (p : Prop) [Decidable p] : M ε Unit := fun e c => if p then .ok () e c else .ub

def jsAny : Option Val → M ε Val
  | some v => pure v
  | none => ub

def getCore : M ε Core := fun e c => .ok c e c

def setCore (c' : Core) : M ε Unit := fun e _ => .ok () e c'

def getExt : M ε ε := fun e c => .ok e e c

def ld (a : Arr) (i : Int) : M ε (Option Val) := fun e c =>
  if 0 ≤ i ∧ i < (c.get a).length then .ok ((c.get a).getD i.toNat none) e c else .abort

def st (a : Arr) (i : Int) (x : Option Val) : M ε Unit := fun e c =>
  if 0 ≤ i ∧ i < (c.get a).length then .ok () e (c.put a ((c.get a).set i.toNat x)) else .abort

def mv (src : Arr) (i : Int) (dst : Arr) (j : Int) : M ε Unit := do
  let x ← ld src i
  st dst j x

def compare (cmp : Cmp ε) (x y : Val) : M ε Int := fun e c =>
  match cmp e x y with
  | some (o, e') => .ok o e' c
  | none => .throw e

def ldInt (l : List Int) (i : Int) : M ε Int := fun e c =>
  if 0 ≤ i ∧ i < l.length then .ok (l.getD i.toNat 0) e c else .abort

def runBase (run : Int) : M ε Int := fun e c => ldInt c.runs (2 * run) e c

def runLen (run : Int) : M ε Int := fun e c => ldInt c.runs (2 * run + 1) e c

def setRun (i v : Int) : M ε Unit := fun e c =>
  if 0 ≤ i ∧ i < c.runs.length then .ok () e { c with runs := c.runs.set i.toNat v } else .abort

def setRunBase (run v : Int) : M ε Unit := setRun (2 * run) v

def setRunLen (run v : Int) : M ε Unit := setRun (2 * run + 1) v

def getPower (run : Int) : M ε Int := fun e c => ldInt c.powers run e c

def setPower (run v : Int) : M ε Unit := fun e c =>
  if 0 ≤ run ∧ run < c.powers.length then .ok () e { c with powers := c.powers.set run.toNat v }
  else .abort

def getSize : M ε Int := fun e c => if 0 ≤ c.size then .ok c.size e c else .ub

def setSize (s : Int) : M ε Unit := fun e c => .ok () e { c with size := s }

def getMinGallop : M ε Int := fun e c => .ok c.minGallop e c

def setMinGallop (g : Int) : M ε Unit := fun e c => .ok () e { c with minGallop := g }

def copyFwd (src dst : Arr) (to srcIdx dstIdx : Int) : M ε Unit :=
  if h : srcIdx < to then do
    mv src srcIdx dst dstIdx
    copyFwd src dst to (srcIdx + 1) (dstIdx + 1)
  else pure ()
termination_by (to - srcIdx).toNat
decreasing_by omega

def copyBwd (src dst : Arr) (srcPos srcIdx dstIdx : Int) : M ε Unit :=
  if h : srcPos ≤ srcIdx then do
    mv src srcIdx dst dstIdx
    copyBwd src dst srcPos (srcIdx - 1) (dstIdx - 1)
  else pure ()
termination_by (srcIdx + 1 - srcPos).toNat
decreasing_by omega

def copy (src : Arr) (srcPos : Int) (dst : Arr) (dstPos length : Int) : M ε Unit := do
  dcheck (0 ≤ srcPos)
  dcheck (0 ≤ dstPos)
  let c ← getCore
  dcheck (srcPos ≤ (c.get src).length - length)
  dcheck (dstPos ≤ (c.get dst).length - length)
  if srcPos < dstPos then copyBwd src dst srcPos (srcPos + length - 1) (dstPos + length - 1)
  else copyFwd src dst (srcPos + length) srcPos dstPos

def getTempArray (requested : Int) : M ε Unit := fun e c =>
  if max kSortStateTempSize requested ≤ c.temp.length then .ok () e c
  else .ok () e { c with temp := List.replicate (max kSortStateTempSize requested).toNat (some (.smi 0)) }

variable (cmp : Cmp ε) (smiMax : Nat)

def bisSearch (pivot : Val) (left right : Int) : M ε (Int × Int) :=
  if h : left < right then do
    let mid := left + (right - left) / 2
    let order ← compare cmp pivot (← jsAny (← ld .work mid))
    if order < 0 then bisSearch pivot left mid else bisSearch pivot (mid + 1) right
  else pure (left, right)
termination_by (right - left).toNat
decreasing_by all_goals omega

def bisShift (left p : Int) : M ε Unit :=
  if h : left < p then do
    mv .work (p - 1) .work p
    bisShift left (p - 1)
  else pure ()
termination_by (p - left).toNat
decreasing_by omega

def bisLoop (low high start : Int) : M ε Unit :=
  if h : start < high then do
    let pivot ← jsAny (← ld .work start)
    dcheck (low < start)
    let lr ← bisSearch cmp pivot low start
    dcheck (lr.1 = lr.2)
    bisShift lr.1 start
    st .work lr.1 (some pivot)
    bisLoop low high (start + 1)
  else pure ()
termination_by (high - start).toNat
decreasing_by omega

def binaryInsertionSort (low startArg high : Int) : M ε Unit := do
  dcheck (low ≤ startArg ∧ startArg ≤ high)
  bisLoop cmp low high (if low = startArg then startArg + 1 else startArg)

def countRunLoop (isDesc : Bool) (high : Int) (prev : Val) (idx runLength : Int) : M ε Int :=
  if h : idx < high then do
    let cur ← jsAny (← ld .work idx)
    let order ← compare cmp cur prev
    if (if isDesc then decide (0 ≤ order) else decide (order < 0)) = true then pure runLength
    else countRunLoop isDesc high cur (idx + 1) (runLength + 1)
  else pure runLength
termination_by (high - idx).toNat
decreasing_by omega

def reverseLoop (low high : Int) : M ε Unit :=
  if h : low < high then do
    let eLow ← ld .work low
    let eHigh ← ld .work high
    st .work low eHigh
    st .work high eLow
    reverseLoop (low + 1) (high - 1)
  else pure ()
termination_by (high - low).toNat
decreasing_by omega

def reverseRange (frm to : Int) : M ε Unit := reverseLoop frm (to - 1)

def countAndMakeRun (lowArg high : Int) : M ε Int := do
  dcheck (lowArg < high)
  if lowArg + 1 = high then pure 1
  else do
    let eLow ← jsAny (← ld .work (lowArg + 1))
    let ePred ← jsAny (← ld .work lowArg)
    let order ← compare cmp eLow ePred
    let runLength ← countRunLoop cmp (decide (order < 0)) high eLow (lowArg + 2) 2
    if order < 0 then reverseRange lowArg (lowArg + runLength) else pure ()
    pure runLength

def gallopNext (maxOfs : Int) (offset : Nat) : Nat :=
  if 2 * offset + 1 ≤ smiMax then 2 * offset + 1 else maxOfs.toNat

def gallopPhase (a : Arr) (key : Val) (keyFirst plus breakNeg : Bool) (base hint maxOfs : Int)
    (lastOfs offset : Nat) : M ε (Nat × Nat) :=
  if h : (offset : Int) < maxOfs then do
    let el ← jsAny (← ld a (if plus then base + hint + offset else base + hint - offset))
    let order ← if keyFirst then compare cmp key el else compare cmp el key
    if (if breakNeg then decide (order < 0) else decide (0 ≤ order)) = true then
      pure (lastOfs, offset)
    else
      gallopPhase a key keyFirst plus breakNeg base hint maxOfs offset (gallopNext smiMax maxOfs offset)
  else pure (lastOfs, offset)
termination_by (maxOfs - offset).toNat
decreasing_by
  unfold gallopNext
  split <;> omega

def gallopSearch (a : Arr) (key : Val) (keyFirst : Bool) (base lastOfs offset : Int) :
    M ε (Int × Int) :=
  if h : lastOfs < offset then do
    let m := lastOfs + (offset - lastOfs) / 2
    let el ← jsAny (← ld a (base + m))
    let order ← if keyFirst then compare cmp key el else compare cmp el key
    if decide (order < 0) = keyFirst then gallopSearch a key keyFirst base lastOfs m
    else gallopSearch a key keyFirst base (m + 1) offset
  else pure (lastOfs, offset)
termination_by (offset - lastOfs).toNat
decreasing_by all_goals omega

def gallop (isRight : Bool) (a : Arr) (key : Val) (base length hint : Int) : M ε Int := do
  dcheck (0 < length ∧ 0 ≤ base)
  dcheck (0 ≤ hint ∧ hint < length)
  let bh ← jsAny (← ld a (base + hint))
  let order ← if isRight then compare cmp key bh else compare cmp bh key
  let neg := decide (order < 0)
  let plus := neg != isRight
  let maxOfs := if plus then length - hint else hint + 1
  let r ← gallopPhase cmp smiMax a key isRight plus (!neg) base hint maxOfs 0 1
  let off : Int := if maxOfs < (r.2 : Int) then maxOfs else r.2
  let lastOfs : Int := if plus then r.1 + hint else hint - off
  let offset : Int := if plus then off + hint else hint - r.1
  dcheck (-1 ≤ lastOfs ∧ lastOfs < offset ∧ offset ≤ length)
  let s ← gallopSearch cmp a key isRight base (lastOfs + 1) offset
  dcheck (s.1 = s.2)
  dcheck (0 ≤ s.2 ∧ s.2 ≤ length)
  pure s.2

end

structure MS where
  dest : Int
  ct : Int
  cur : Int
  la : Int
  lb : Int
  deriving Repr

inductive Exit where
  | succeed (s : MS)
  | copy (s : MS)

inductive Ph where
  | simple (wa wb : Int)
  | gallop (first : Bool) (wa wb : Int)

def Ph.rank : Ph → Nat
  | .simple _ _ => 0
  | .gallop _ _ _ => 1

section

variable {ε : Type} (cmp : Cmp ε) (smiMax : Nat)

def lowLoop (mg : Int) (ph : Ph) (s : MS) : M ε Exit :=
  match ph with
  | .simple wa wb =>
    if h : 1 < s.la ∧ 0 < s.lb then do
      let order ← compare cmp (← jsAny (← ld .work s.cur)) (← jsAny (← ld .temp s.ct))
      if order < 0 then do
        mv .work s.cur .work s.dest
        if s.lb - 1 = 0 then pure (.succeed ⟨s.dest + 1, s.ct, s.cur + 1, s.la, s.lb - 1⟩)
        else if mg ≤ wb + 1 then
          lowLoop (mg + 1) (.gallop true 0 (wb + 1)) ⟨s.dest + 1, s.ct, s.cur + 1, s.la, s.lb - 1⟩
        else lowLoop mg (.simple 0 (wb + 1)) ⟨s.dest + 1, s.ct, s.cur + 1, s.la, s.lb - 1⟩
      else do
        mv .temp s.ct .work s.dest
        if s.la - 1 = 1 then pure (.copy ⟨s.dest + 1, s.ct + 1, s.cur, s.la - 1, s.lb⟩)
        else if mg ≤ wa + 1 then
          lowLoop (mg + 1) (.gallop true (wa + 1) 0) ⟨s.dest + 1, s.ct + 1, s.cur, s.la - 1, s.lb⟩
        else lowLoop mg (.simple (wa + 1) 0) ⟨s.dest + 1, s.ct + 1, s.cur, s.la - 1, s.lb⟩
    else ub
  | .gallop first wa wb =>
    if kMinGallopWins ≤ wa ∨ kMinGallopWins ≤ wb ∨ first = true then
      if h : 1 < s.la ∧ 0 < s.lb then do
        let mg' := max 1 (mg - 1)
        setMinGallop mg'
        let na ← gallop cmp smiMax true .temp (← jsAny (← ld .work s.cur)) s.ct s.la 0
        if h1 : 0 ≤ na then do
          if 0 < na then copy .temp s.ct .work s.dest na else pure ()
          if 0 < na ∧ s.la - na = 1 then pure (.copy ⟨s.dest + na, s.ct + na, s.cur, s.la - na, s.lb⟩)
          else if 0 < na ∧ s.la - na = 0 then
            pure (.succeed ⟨s.dest + na, s.ct + na, s.cur, s.la - na, s.lb⟩)
          else do
            mv .work s.cur .work (s.dest + na)
            if s.lb - 1 = 0 then
              pure (.succeed ⟨s.dest + na + 1, s.ct + na, s.cur + 1, s.la - na, s.lb - 1⟩)
            else do
              let nb ← gallop cmp smiMax false .work (← jsAny (← ld .temp (s.ct + na))) (s.cur + 1)
                (s.lb - 1) 0
              if h2 : 0 ≤ nb then do
                if 0 < nb then copy .work (s.cur + 1) .work (s.dest + na + 1) nb else pure ()
                if 0 < nb ∧ s.lb - 1 - nb = 0 then
                  pure (.succeed ⟨s.dest + na + 1 + nb, s.ct + na, s.cur + 1 + nb, s.la - na,
                    s.lb - 1 - nb⟩)
                else do
                  mv .temp (s.ct + na) .work (s.dest + na + 1 + nb)
                  if s.la - na - 1 = 1 then
                    pure (.copy ⟨s.dest + na + 2 + nb, s.ct + na + 1, s.cur + 1 + nb, s.la - na - 1,
                      s.lb - 1 - nb⟩)
                  else lowLoop mg' (.gallop false na nb) ⟨s.dest + na + 2 + nb, s.ct + na + 1,
                    s.cur + 1 + nb, s.la - na - 1, s.lb - 1 - nb⟩
              else ub
        else ub
      else ub
    else do
      setMinGallop (mg + 1)
      lowLoop (mg + 1) (.simple 0 0) s
termination_by 2 * (s.la.toNat + s.lb.toNat) + ph.rank
decreasing_by all_goals simp only [Ph.rank]; omega

def mergeLow (baseA lengthA baseB lengthB : Int) : M ε Unit := do
  dcheck (0 < lengthA ∧ 0 < lengthB)
  dcheck (0 ≤ baseA ∧ 0 < baseB)
  dcheck (baseA + lengthA = baseB)
  getTempArray lengthA
  copy .work baseA .temp 0 lengthA
  mv .work baseB .work baseA
  let s : MS := ⟨baseA + 1, 0, baseB + 1, lengthA, lengthB - 1⟩
  let x ← if s.lb = 0 then pure (Exit.succeed s)
    else if s.la = 1 then pure (Exit.copy s)
    else do
      let mg ← getMinGallop
      lowLoop cmp smiMax mg (.simple 0 0) s
  match x with
  | .succeed s => if 0 < s.la then copy .temp s.ct .work s.dest s.la else pure ()
  | .copy s => do
    dcheck (s.la = 1 ∧ 0 < s.lb)
    copy .work s.cur .work s.dest s.lb
    mv .temp s.ct .work (s.dest + s.lb)

def highLoop (baseA : Int) (mg : Int) (ph : Ph) (s : MS) : M ε Exit :=
  match ph with
  | .simple wa wb =>
    if h : 0 < s.la ∧ 1 < s.lb then do
      let order ← compare cmp (← jsAny (← ld .temp s.ct)) (← jsAny (← ld .work s.cur))
      if order < 0 then do
        mv .work s.cur .work s.dest
        if s.la - 1 = 0 then pure (.succeed ⟨s.dest - 1, s.ct, s.cur - 1, s.la - 1, s.lb⟩)
        else if mg ≤ wa + 1 then
          highLoop baseA (mg + 1) (.gallop true (wa + 1) 0) ⟨s.dest - 1, s.ct, s.cur - 1, s.la - 1, s.lb⟩
        else highLoop baseA mg (.simple (wa + 1) 0) ⟨s.dest - 1, s.ct, s.cur - 1, s.la - 1, s.lb⟩
      else do
        mv .temp s.ct .work s.dest
        if s.lb - 1 = 1 then pure (.copy ⟨s.dest - 1, s.ct - 1, s.cur, s.la, s.lb - 1⟩)
        else if mg ≤ wb + 1 then
          highLoop baseA (mg + 1) (.gallop true 0 (wb + 1)) ⟨s.dest - 1, s.ct - 1, s.cur, s.la, s.lb - 1⟩
        else highLoop baseA mg (.simple 0 (wb + 1)) ⟨s.dest - 1, s.ct - 1, s.cur, s.la, s.lb - 1⟩
    else ub
  | .gallop first _ _ =>
    if kMinGallopWins ≤ (match ph with | .gallop _ wa _ => wa | _ => 0) ∨
        kMinGallopWins ≤ (match ph with | .gallop _ _ wb => wb | _ => 0) ∨ first = true then
      if h : 0 < s.la ∧ 1 < s.lb then do
        let mg' := max 1 (mg - 1)
        setMinGallop mg'
        let k ← gallop cmp smiMax true .work (← jsAny (← ld .temp s.ct)) baseA s.la (s.la - 1)
        dcheck (0 ≤ k)
        let na := s.la - k
        if 0 < na then copy .work (s.cur - na + 1) .work (s.dest - na + 1) na else pure ()
        if 0 < na ∧ s.la - na = 0 then pure (.succeed ⟨s.dest - na, s.ct, s.cur - na, s.la - na, s.lb⟩)
        else do
          let d1 := if 0 < na then s.dest - na else s.dest
          let c1 := if 0 < na then s.cur - na else s.cur
          let l1 := if 0 < na then s.la - na else s.la
          mv .temp s.ct .work d1
          if s.lb - 1 = 1 then pure (.copy ⟨d1 - 1, s.ct - 1, c1, l1, s.lb - 1⟩)
          else do
            let k2 ← gallop cmp smiMax false .temp (← jsAny (← ld .work c1)) 0 (s.lb - 1) (s.lb - 2)
            dcheck (0 ≤ k2)
            let nb := s.lb - 1 - k2
            if 0 < nb then copy .temp (s.ct - 1 - nb + 1) .work (d1 - 1 - nb + 1) nb else pure ()
            let d2 := if 0 < nb then d1 - 1 - nb else d1 - 1
            let t2 := if 0 < nb then s.ct - 1 - nb else s.ct - 1
            let m2 := if 0 < nb then s.lb - 1 - nb else s.lb - 1
            if 0 < nb ∧ m2 = 1 then pure (.copy ⟨d2, t2, c1, l1, m2⟩)
            else if 0 < nb ∧ m2 = 0 then pure (.succeed ⟨d2, t2, c1, l1, m2⟩)
            else do
              mv .work c1 .work d2
              if l1 - 1 = 0 then pure (.succeed ⟨d2 - 1, t2, c1 - 1, l1 - 1, m2⟩)
              else if h3 : l1.toNat + m2.toNat < s.la.toNat + s.lb.toNat then
                highLoop baseA mg' (.gallop false na nb) ⟨d2 - 1, t2, c1 - 1, l1 - 1, m2⟩
              else ub
      else ub
    else do
      setMinGallop (mg + 1)
      highLoop baseA (mg + 1) (.simple 0 0) s
termination_by 2 * (s.la.toNat + s.lb.toNat) + ph.rank
decreasing_by all_goals simp only [Ph.rank]; omega

end

end ArraySort
