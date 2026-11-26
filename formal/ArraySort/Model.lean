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
  if _h : (offset : Int) < maxOfs then do
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
  | .gallop first wa wb =>
    if kMinGallopWins ≤ wa ∨ kMinGallopWins ≤ wb ∨ first = true then
      if h : 0 < s.la ∧ 1 < s.lb then do
        let mg' := max 1 (mg - 1)
        setMinGallop mg'
        let k ← gallop cmp smiMax true .work (← jsAny (← ld .temp s.ct)) baseA s.la (s.la - 1)
        dcheck (0 ≤ k)
        let na := s.la - k
        let pa := max na 0
        if 0 < na then copy .work (s.cur - pa + 1) .work (s.dest - pa + 1) pa else pure ()
        if 0 < na ∧ s.la - pa = 0 then
          pure (.succeed ⟨s.dest - pa, s.ct, s.cur - pa, s.la - pa, s.lb⟩)
        else do
          mv .temp s.ct .work (s.dest - pa)
          if s.lb - 1 = 1 then pure (.copy ⟨s.dest - pa - 1, s.ct - 1, s.cur - pa, s.la - pa, s.lb - 1⟩)
          else do
            let k2 ← gallop cmp smiMax false .temp (← jsAny (← ld .work (s.cur - pa))) 0 (s.lb - 1)
              (s.lb - 2)
            dcheck (0 ≤ k2)
            let nb := s.lb - 1 - k2
            let pb := max nb 0
            if 0 < nb then copy .temp (s.ct - 1 - pb + 1) .work (s.dest - pa - 1 - pb + 1) pb
            else pure ()
            if 0 < nb ∧ s.lb - 1 - pb = 1 then
              pure (.copy ⟨s.dest - pa - 1 - pb, s.ct - 1 - pb, s.cur - pa, s.la - pa, s.lb - 1 - pb⟩)
            else if 0 < nb ∧ s.lb - 1 - pb = 0 then
              pure (.succeed ⟨s.dest - pa - 1 - pb, s.ct - 1 - pb, s.cur - pa, s.la - pa, s.lb - 1 - pb⟩)
            else do
              mv .work (s.cur - pa) .work (s.dest - pa - 1 - pb)
              if s.la - pa - 1 = 0 then
                pure (.succeed ⟨s.dest - pa - 2 - pb, s.ct - 1 - pb, s.cur - pa - 1, s.la - pa - 1,
                  s.lb - 1 - pb⟩)
              else highLoop baseA mg' (.gallop false na nb) ⟨s.dest - pa - 2 - pb, s.ct - 1 - pb,
                s.cur - pa - 1, s.la - pa - 1, s.lb - 1 - pb⟩
      else ub
    else do
      setMinGallop (mg + 1)
      highLoop baseA (mg + 1) (.simple 0 0) s
termination_by 2 * (s.la.toNat + s.lb.toNat) + ph.rank
decreasing_by all_goals simp only [Ph.rank]; omega

def mergeHigh (baseA lengthA baseB lengthB : Int) : M ε Unit := do
  dcheck (0 < lengthA ∧ 0 < lengthB)
  dcheck (0 ≤ baseA ∧ 0 < baseB)
  dcheck (baseA + lengthA = baseB)
  getTempArray lengthB
  copy .work baseB .temp 0 lengthB
  mv .work (baseA + lengthA - 1) .work (baseB + lengthB - 1)
  let s : MS := ⟨baseB + lengthB - 2, lengthB - 1, baseA + lengthA - 2, lengthA - 1, lengthB⟩
  let x ← if s.la = 0 then pure (Exit.succeed s)
    else if s.lb = 1 then pure (Exit.copy s)
    else do
      let mg ← getMinGallop
      highLoop cmp smiMax baseA mg (.simple 0 0) s
  match x with
  | .succeed s =>
    if 0 < s.lb then do
      dcheck (s.la = 0)
      copy .temp 0 .work (s.dest - (s.lb - 1)) s.lb
    else pure ()
  | .copy s => do
    dcheck (s.lb = 1 ∧ 0 < s.la)
    copy .work (s.cur - s.la + 1) .work (s.dest - s.la + 1) s.la
    mv .temp s.ct .work (s.dest - s.la)

def mergeAt (i : Int) : M ε Unit := do
  let stackSize ← getSize
  dcheck (2 ≤ stackSize)
  dcheck (0 ≤ i)
  dcheck (i = stackSize - 2 ∨ i = stackSize - 3)
  let baseA ← runBase i
  let lengthA ← runLen i
  let baseB ← runBase (i + 1)
  let lengthB ← runLen (i + 1)
  dcheck (0 < lengthA ∧ 0 < lengthB)
  dcheck (baseA + lengthA = baseB)
  setRunLen i (lengthA + lengthB)
  if i = stackSize - 3 then do
    let base ← runBase (i + 2)
    let length ← runLen (i + 2)
    setRunBase (i + 1) base
    setRunLen (i + 1) length
  else pure ()
  setSize (stackSize - 1)
  let keyRight ← jsAny (← ld .work baseB)
  let k ← gallop cmp smiMax true .work keyRight baseA lengthA 0
  dcheck (0 ≤ k)
  if lengthA - k = 0 then pure ()
  else do
    dcheck (0 < lengthA - k)
    let keyLeft ← jsAny (← ld .work (baseA + k + (lengthA - k) - 1))
    let lb ← gallop cmp smiMax false .work keyLeft baseB lengthB (lengthB - 1)
    dcheck (0 ≤ lb)
    if lb = 0 then pure ()
    else if lengthA - k ≤ lb then mergeLow cmp smiMax (baseA + k) (lengthA - k) baseB lb
    else mergeHigh cmp smiMax (baseA + k) (lengthA - k) baseB lb

end

def clz32 (x : Nat) : Nat := if x = 0 then 32 else 31 - Nat.log2 x

def nodePowerValue (s1 n1 n2 n : Int) : Int :=
  let a := 2 * s1 + n1
  let b := a + n1 + n2
  let aScaled := a * 2 ^ 30 / n
  let bScaled := b * 2 ^ 30 / n
  clz32 ((aScaled.toNat % 2 ^ 32) ^^^ (bScaled.toNat % 2 ^ 32))

def nodePower {ε : Type} (s1 n1 n2 n : Int) : M ε Int := do
  dcheck (0 ≤ s1)
  dcheck (0 < n1 ∧ 0 < n2)
  dcheck (s1 + n1 + n2 ≤ n)
  pure (nodePowerValue s1 n1 n2 n)

def nodePower32Loop (n : Int) : Nat → Int → Int → Int → Int
  | 0, result, _, _ => result
  | fuel + 1, result, a, b =>
    if n ≤ a then nodePower32Loop n fuel (result + 1) (2 * (a - n)) (2 * (b - n))
    else if n ≤ b then result + 1
    else nodePower32Loop n fuel (result + 1) (2 * a) (2 * b)

def nodePower32 (s1 n1 n2 n : Int) : Int :=
  nodePower32Loop n 64 0 (2 * s1 + n1) (2 * s1 + n1 + n1 + n2)

section

variable {ε : Type} (cmp : Cmp ε) (smiMax : Nat)

def pushRun (base length : Int) : M ε Unit := do
  let stackSize ← getSize
  dcheck (stackSize < kMaxMergePending)
  setRunBase stackSize base
  setRunLen stackSize length
  setSize (stackSize + 1)

def mergeCollapse (p stackSize : Int) : M ε Int :=
  if h : 1 < stackSize then do
    let pw ← getPower (stackSize - 2)
    if p < pw then do
      mergeAt cmp smiMax (stackSize - 2)
      let s' ← getSize
      if _h2 : s' < stackSize then mergeCollapse p s' else ub
    else pure stackSize
  else pure stackSize
termination_by stackSize.toNat
decreasing_by omega

def mainLoop (length mrStep mrRemainder mrThreshold low remaining mrAccum : Int) : M ε Unit :=
  if _h : remaining ≠ 0 then do
    let acc := mrAccum + mrRemainder
    let minRun := if mrThreshold ≤ acc then mrStep + 1 else mrStep
    dcheck (length < 64 ∨ (32 ≤ minRun ∧ minRun ≤ 64))
    let r ← countAndMakeRun cmp low (low + remaining)
    let cur ← if r < minRun then do
        binaryInsertionSort cmp low (low + r) (low + min minRun remaining)
        pure (min minRun remaining)
      else pure r
    let stackSize ← getSize
    if stackSize = 0 then pushRun low cur
    else do
      let prevBase ← runBase (stackSize - 1)
      let prevLen ← runLen (stackSize - 1)
      let p ← nodePower prevBase prevLen cur length
      let ss ← mergeCollapse cmp smiMax p stackSize
      if 2 ≤ ss then do
        let pw ← getPower (ss - 2)
        dcheck (pw < p)
      else pure ()
      setPower (ss - 1) p
      pushRun low cur
    if _h2 : 0 < cur ∧ cur ≤ remaining then
      mainLoop length mrStep mrRemainder mrThreshold (low + cur) (remaining - cur)
        (if mrThreshold ≤ acc then acc - mrThreshold else acc)
    else ub
  else pure ()
termination_by remaining.toNat
decreasing_by omega

def finalLoop (s : Int) : M ε Unit :=
  if h : 1 < s then do
    let n ← if 0 < s - 2 then do
        let l1 ← runLen (s - 2 - 1)
        let l2 ← runLen (s - 2 + 1)
        pure (if l1 < l2 then s - 2 - 1 else s - 2)
      else pure (s - 2)
    mergeAt cmp smiMax n
    let s' ← getSize
    if _h2 : s' < s then finalLoop s' else ub
  else pure ()
termination_by s.toNat
decreasing_by omega

def mrLoop (mrStep mrMask : Int) : Int × Int :=
  if h : 64 ≤ mrStep then mrLoop (mrStep / 2) (2 * mrMask + 1) else (mrStep, mrMask)
termination_by mrStep.toNat
decreasing_by omega

def powerSortImpl (length : Int) : M ε Unit :=
  if length < 2 then pure ()
  else do
    let c ← getCore
    setCore { c with runs := List.replicate 85 0, powers := List.replicate 85 0 }
    let mr := mrLoop length 0
    mainLoop cmp smiMax length mr.1 ((length.toNat &&& mr.2.toNat : Nat) : Int) (mr.2 + 1) 0 length 0
    let s ← getSize
    finalLoop cmp smiMax s
    let s' ← getSize
    dcheck (s' = 1)
    let l ← runLen 0
    dcheck (l = length)

def sortCore (n : Int) : M ε Unit :=
  if n < kMaxBinaryInsertionSortLength then binaryInsertionSort cmp 0 0 n
  else powerSortImpl cmp smiMax n

end

structure Cfg where
  smiMax : Nat
  maxFast : Nat
  ud : Bool

inductive Num where
  | nan
  | fin (z : Int)
  deriving DecidableEq, Repr

inductive WB where
  | store (i : Nat) (v : Val)
  | del (i : Nat)
  deriving DecidableEq, Repr

structure Recv where
  map : Nat
  prot : Bool
  obj : Bool
  arr : JSArr
  deriving Repr

structure Ext where
  recv : Recv
  tick : Nat
  log : List WB
  deriving Repr

structure Env where
  call : Nat → Recv → Val → Val → Option (Num × Recv)
  str : Nat → Recv → Val → Val → Option (Int × Recv)
  load : Bool → Nat → Recv → Nat → Option (Option Val × Recv)
  set : Nat → Recv → Nat → Val → Option Recv
  del : Nat → Recv → Nat → Option Recv
  toNum : Nat → Recv → Val → Option Recv

def smiLexCompare (a b : Int) : Int :=
  if toString a < toString b then -1 else if toString b < toString a then 1 else 0

def Ext.step (e : Ext) (r : Recv) : Ext := { e with recv := r, tick := e.tick + 1 }

def sortCompare (env : Env) (user : Bool) : Cmp Ext := fun e x y =>
  if user then
    match env.call e.tick e.recv x y with
    | some (.nan, r) => some (0, e.step r)
    | some (.fin z, r) => some (z, e.step r)
    | none => none
  else
    match x, y with
    | .smi a, .smi b => some (smiLexCompare a b, e)
    | _, _ =>
      match env.str e.tick e.recv x y with
      | some (z, r) => some (z, e.step r)
      | none => none

structure GFA where
  array : List (Option Val)
  capacity : Nat
  length : Nat
  deriving Repr

def gfaPush {ε : Type} (g : GFA) (x : Option Val) : M ε GFA := do
  dcheck (g.length ≤ g.capacity)
  let g' ← if g.capacity = g.length then do
      dcheck (g.length ≤ g.capacity + g.capacity / 2 + 16)
      pure (⟨g.array.take g.length ++
        List.replicate (g.capacity + g.capacity / 2 + 16 - g.length) none,
        g.capacity + g.capacity / 2 + 16, g.length⟩ : GFA)
    else pure g
  if g'.length < g'.array.length then pure ⟨g'.array.set g'.length x, g'.capacity, g'.length + 1⟩
  else abort

def compactFast {ε : Type} (isToSorted : Bool) (elems : List (Option Val)) (len : Nat) :
    Nat → GFA → Nat → M ε (GFA × Nat)
  | i, g, nu =>
    if _h : i < len then do
      let x ← if i < elems.length then pure (elems.getD i none) else abort
      match x with
      | none => compactFast isToSorted elems len (i + 1) g (if isToSorted then nu + 1 else nu)
      | some v =>
        if v = .undef then compactFast isToSorted elems len (i + 1) g (nu + 1)
        else do
          let g' ← gfaPush g (some v)
          compactFast isToSorted elems len (i + 1) g' nu
    else pure (g, nu)
termination_by i => len - i

def loadGeneric (env : Env) (isToSorted : Bool) (i : Nat) : M Ext (Option Val) := fun e c =>
  match env.load (!isToSorted) e.tick e.recv i with
  | some (x, r) => .ok x (e.step r) c
  | none => .throw e

def compactGeneric (env : Env) (isToSorted : Bool) (len : Nat) :
    Nat → GFA → Nat → M Ext (GFA × Nat)
  | i, g, nu =>
    if _h : i < len then do
      let x ← loadGeneric env isToSorted i
      match x with
      | none => compactGeneric env isToSorted len (i + 1) g (if isToSorted then nu + 1 else nu)
      | some v =>
        if v = .undef then compactGeneric env isToSorted len (i + 1) g (nu + 1)
        else do
          let g' ← gfaPush g (some v)
          compactGeneric env isToSorted len (i + 1) g' nu
    else pure (g, nu)
termination_by i => len - i

def compact (env : Env) (isToSorted : Bool) (len : Nat) : M Ext (Nat × Nat) := do
  let c ← getCore
  let e ← getExt
  let g0 : GFA := ⟨c.work, c.work.length, 0⟩
  let res ← if e.recv.arr.fast then
      if e.recv.arr.kind.isDouble then do
        if e.recv.arr.store = [] then ub else pure ()
        compactFast isToSorted e.recv.arr.store len 0 g0 0
      else compactFast isToSorted e.recv.arr.store len 0 g0 0
    else compactGeneric env isToSorted len 0 g0 0
  let c' ← getCore
  setCore { c' with work := res.1.array }
  pure (res.1.length, res.2)

inductive Acc where
  | smi
  | obj
  | dbl
  | generic
  deriving DecidableEq, Repr

def isSmiKind : Kind → Bool
  | .packedSmi => true
  | .holeySmi => true
  | _ => false

def selectAcc (reset : Bool) (r : Recv) : Acc :=
  if reset = true ∨ r.arr.fast = false then .generic
  else if r.arr.kind.isDouble then .dbl
  else if isSmiKind r.arr.kind then .smi
  else .obj

def putElem (r : Recv) (i : Nat) (x : Option Val) : Recv :=
  { r with arr := { r.arr with store := r.arr.store.set i x } }

def fastWrite (checkCow : Bool) (e : Ext) (c : Core) (i : Nat) (x : Option Val) : Res Ext Unit :=
  if i < e.recv.arr.store.length then
    if checkCow ∧ e.recv.arr.cow = true then .ub else .ok () { e with recv := putElem e.recv i x } c
  else .abort

def storeTo (cfg : Cfg) (env : Env) (acc : Acc) (i : Nat) (v : Val) : M Ext Unit := fun e c =>
  let e' : Ext := { e with log := e.log ++ [.store i v] }
  match acc with
  | .generic =>
    match env.set e.tick e.recv i v with
    | some r => .ok () (e'.step r) c
    | none => .throw e'
  | .smi => if v.isSmi then fastWrite true e' c i (some v) else .ub
  | .obj => fastWrite true e' c i (some v)
  | .dbl =>
    if e.recv.arr.store = [] then .ub
    else
      match v with
      | .num _ => fastWrite false e' c i (some v)
      | .undef => if cfg.ud then fastWrite false e' c i (some v) else .ub
      | _ => .ub

def deleteAt (env : Env) (acc : Acc) (i : Nat) : M Ext Unit := fun e c =>
  let e' : Ext := { e with log := e.log ++ [.del i] }
  match acc with
  | .generic =>
    match env.del e.tick e.recv i with
    | some r => .ok () (e'.step r) c
    | none => .throw e'
  | .dbl =>
    if e.recv.arr.kind.isHoley then
      if e.recv.arr.store = [] then .ub else fastWrite false e' c i none
    else .ub
  | _ => if e.recv.arr.kind.isHoley then fastWrite true e' c i none else .ub

def storeLoop (cfg : Cfg) (env : Env) (acc : Acc) (n : Nat) : Nat → M Ext Unit
  | i =>
    if h : i < n then do
      let v ← jsAny (← ld .work i)
      storeTo cfg env acc i v
      storeLoop cfg env acc n (i + 1)
    else pure ()
termination_by i => n - i

def undefLoop (cfg : Cfg) (env : Env) (acc : Acc) (n : Nat) : Nat → M Ext Unit
  | i =>
    if h : i < n then do
      storeTo cfg env acc i .undef
      undefLoop cfg env acc n (i + 1)
    else pure ()
termination_by i => n - i

def deleteLoop (env : Env) (acc : Acc) (n : Nat) : Nat → M Ext Unit
  | i =>
    if h : i < n then do
      deleteAt env acc i
      deleteLoop env acc n (i + 1)
    else pure ()
termination_by i => n - i

def copyBack (cfg : Cfg) (env : Env) (reset : Bool) (n nu sortLength : Nat) : M Ext Unit := do
  let e ← getExt
  let c ← getCore
  dcheck (n ≤ c.work.length)
  dcheck (n + nu ≤ sortLength)
  storeLoop cfg env (selectAcc reset e.recv) n 0
  if n = sortLength then pure ()
  else do
    undefLoop cfg env (selectAcc reset e.recv) (nu + n) n
    let e' ← getExt
    deleteLoop env (selectAcc reset e'.recv) sortLength (nu + n)

def checkAccessor (cfg : Cfg) (initMap initLen : Nat) : M Ext Bool := do
  let e ← getExt
  if e.recv.arr.fast = false then pure false
  else if e.recv.map ≠ initMap then pure false
  else do
    dcheck (initLen ≤ cfg.smiMax)
    pure (decide (e.recv.arr.length = initLen))

def sortTail (cfg : Cfg) (env : Env) (user : Bool) (initMap initLen : Nat) (reset : Bool)
    (n nu sortLength : Nat) : M Ext Unit := do
  sortCore (sortCompare env user) cfg.smiMax n
  let ok ← checkAccessor cfg initMap initLen
  copyBack cfg env (reset || !ok) n nu sortLength

inductive CmpArg where
  | undef
  | fn
  | other
  deriving DecidableEq, Repr

inductive Result (ρ : Type) where
  | done (r : ρ) (e : Ext)
  | throws (e : Ext)
  | throwType
  | throwRange
  | ub
  | abort

def Res.toResult {ρ : Type} : Res Ext ρ → Result ρ
  | .ok r e _ => .done r e
  | .throw e => .throws e
  | .ub => .ub
  | .abort => .abort

def workArrayLength (smiMax : Nat) (r : Recv) (len : Nat) : Nat :=
  if r.obj = true ∧ r.arr.store.length ≠ 0 then min (min len smiMax) r.arr.store.length
  else min len smiMax

def ensureWritableRecv (r : Recv) : Recv :=
  if r.arr.fast then { r with arr := ensureWritable r.arr } else r

def arraySort (cfg : Cfg) (env : Env) (arg : CmpArg) (r0 : Recv) (len : Nat) : Result Unit :=
  if arg = .other then .throwType
  else if len < 2 then .done () ⟨r0, 0, []⟩
  else if cfg.smiMax < len then .throwRange
  else
    let r1 := ensureWritableRecv r0
    let work := List.replicate (workArrayLength cfg.smiMax r1 len) (some (Val.smi 0))
    Res.toResult ((do
      let cn ← compact env false len
      sortTail cfg env (decide (arg = CmpArg.fn)) r0.map len false cn.1 cn.2 len) ⟨r1, 0, []⟩
      (Core.init work))

def newArray (kind : Kind) (store : List (Option Val)) : JSArr :=
  ⟨kind, true, true, false, false, store.length, store⟩

def fillUndef {ε : Type} (len : Nat) : Nat → List (Option Val) → M ε (List (Option Val))
  | i, copy =>
    if h : i < len then
      if i < copy.length then fillUndef len (i + 1) (copy.set i (some .undef)) else abort
    else pure copy
termination_by i => len - i

def copyToNewFast {ε : Type} (cfg : Cfg) (kind : Kind) (n nu sortLength : Nat) : M ε JSArr := do
  dcheck (kind = .packedSmi ∨ kind = .packedElem)
  dcheck (sortLength = n + nu)
  dcheck (sortLength ≤ cfg.maxFast)
  let c ← getCore
  dcheck (n ≤ sortLength ∧ n ≤ c.work.length)
  let copy := c.work.take n ++ List.replicate (sortLength - n) none
  dcheck (nu = 0 ∨ kind = .packedElem)
  let copy ← fillUndef sortLength n copy
  pure (newArray kind copy)

def smiScan {ε : Type} (n : Nat) : Nat → M ε Bool
  | i =>
    if h : i < n then do
      let v ← jsAny (← ld .work i)
      if v.isSmi then smiScan n (i + 1) else pure false
    else pure true
termination_by i => n - i

def slowCopy {ε : Type} (n : Nat) : Nat → List (Option Val) → M ε (List (Option Val))
  | i, acc =>
    if _h : i < n then do
      let v ← jsAny (← ld .work i)
      slowCopy n (i + 1) (acc ++ [some v])
    else pure acc
termination_by i => n - i

def intoCopy (cfg : Cfg) (env : Env) (user : Bool) (n nu sortLength : Nat) : M Ext JSArr := do
  sortCore (sortCompare env user) cfg.smiMax n
  if sortLength ≤ cfg.maxFast then
    if nu ≠ 0 then copyToNewFast cfg .packedElem n nu sortLength
    else do
      let c ← getCore
      dcheck (n ≤ c.work.length)
      let allSmi ← smiScan n 0
      copyToNewFast cfg (if allSmi then .packedSmi else .packedElem) n nu sortLength
  else do
    let vs ← slowCopy n 0 []
    pure ⟨.slow, false, false, false, false, sortLength,
      vs ++ List.replicate (sortLength - n) (some .undef)⟩

def arrayToSorted (cfg : Cfg) (env : Env) (arg : CmpArg) (r0 : Recv) (len : Nat) : Result JSArr :=
  if arg = .other then .throwType
  else if len = 0 then .done (newArray .packedSmi []) ⟨r0, 0, []⟩
  else if len = 1 then
    match env.load false 0 r0 0 with
    | some (x, r) => .done (newArray .holeyElem [some (x.getD .undef)]) ⟨r, 1, []⟩
    | none => .throws ⟨r0, 0, []⟩
  else if cfg.smiMax < len then .throwRange
  else
    let work := List.replicate (workArrayLength cfg.smiMax r0 len) (some (Val.smi 0))
    Res.toResult ((do
      let cn ← compact env true len
      intoCopy cfg env (decide (arg = CmpArg.fn)) cn.1 cn.2 len) ⟨r0, 0, []⟩ (Core.init work))

def continueFromSnapshot (cfg : Cfg) (env : Env) (user : Bool) (e0 : Ext)
    (tempArray : List (Option Val)) (originalLength : Nat) : Result Unit :=
  Res.toResult (sortTail cfg env user e0.recv.map originalLength true originalLength 0
    originalLength e0 (Core.init tempArray))

def continueAfterCallback (cfg : Cfg) (env : Env) (user : Bool) (r0 : Recv)
    (tempArray : List (Option Val)) (originalLength : Nat) (result : Val) : Result Unit :=
  match env.toNum 0 r0 result with
  | some r1 => continueFromSnapshot cfg env user ⟨r1, 1, []⟩ tempArray originalLength
  | none => .throws ⟨r0, 0, []⟩

end ArraySort
