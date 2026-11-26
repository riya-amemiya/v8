import ArrayJoin.Entry

namespace ArrayJoin.Examples

open Torque ArrayJoin

def lim : Limits := ⟨1000, 1073741823, 2147483647, 4, 4294967295⟩

def hello : Str := ⟨1, [104, 101, 108, 108, 111]⟩
def world : Str := ⟨2, [119, 111, 114, 108, 100]⟩
def ab : Str := ⟨3, [97, 98]⟩
def empty : Str := ⟨4, []⟩
def none' : Str := ⟨5, []⟩

def resBuf : Res Buf → Option Buf
  | .ok b => some b
  | _ => none

def resList : Res (List Nat) → Option (List Nat)
  | .ok s => some s
  | _ => none

def step (sep : Nat) (r : Option Buf) (s : Str) (n : Nat) : Option Buf :=
  r.bind fun b => resBuf (add lim b s n sep)

def finish (sep : Str) (n : Nat) (r : Option Buf) : Option (List Nat) :=
  r.bind fun b => resList ((addSeparators lim b n sep.len true).bind fun b' => bufferJoin b' sep)

def hellos : Option Buf :=
  step 1 (step 1 (step 1 (step 1 (some (newBuffer lim 4)) hello 0) hello 1) hello 1) world 1

#guard (hellos.map Buf.flat) == some [.str hello, .rep 2, .str world]

#guard finish comma 0 hellos ==
  some (hello.chars ++ [44] ++ hello.chars ++ [44] ++ hello.chars ++ [44] ++ world.chars)

def abs (sep : Nat) : Option Buf :=
  step sep (step sep (step sep (step sep (step sep (some (newBuffer lim 5)) ab 0) ab 1) ab 1) ab 1) ab 1

#guard ((abs 1).map Buf.flat) == some [.str ab, .rep 4]

#guard finish comma 0 (abs 1) == some [97, 98, 44, 97, 98, 44, 97, 98, 44, 97, 98, 44, 97, 98]

#guard finish ⟨0, []⟩ 0 (abs 0) == some [97, 98, 97, 98, 97, 98, 97, 98, 97, 98]

def holesAround : Option Buf := step 1 (step 1 (some (newBuffer lim 5)) hello 1) world 2

#guard (holesAround.map Buf.flat) == some [.seps 1, .str hello, .seps 2, .str world]

#guard finish comma 1 holesAround ==
  some ([44] ++ hello.chars ++ [44, 44] ++ world.chars ++ [44])

#guard wItem 10 [44] ⟨[], 1, some empty⟩ (.rep 2) = none

#guard wItem 10 [44] ⟨[120], 1, some empty⟩ (.rep 2) = some ⟨[120, 44, 120], 1, none⟩

#guard wItem 10 [44] ⟨ab.chars, 1, some ab⟩ (.rep 1) = some ⟨[97, 98, 44, 97, 98], 1, none⟩

def digit (n : Int) : Str := ⟨100 + n.toNat, [48 + n.toNat]⟩

def conv : Val → Option (Option Str)
  | .smi n => some (some (digit n))
  | .num n => some (some ⟨200 + n, [48 + n]⟩)
  | .undef => some none
  | .other => some (some hello)
  | .arr _ => none
  | .proxy => none

def arr (kind : Kind) (len : Nat) (store : List (Option Val)) : JSArr :=
  ⟨kind, true, true, true, false, len, store⟩

#guard resList (fastArrayJoin lim conv (arr .holeySmi 3 [some (.smi 1), none, some (.smi 2)]) comma 3) ==
  some [49, 44, 44, 50]

#guard resList (fastArrayJoin lim conv (arr .packedSmi 2 [some (.smi 1), some (.smi 2), none, none]) comma 4) ==
  some [49, 44, 50, 44, 44]

#guard resList (fastArrayJoin lim conv (arr .holeyElem 3 [none, none, none]) comma 3) == some [44, 44]

#guard (match fastArrayJoin lim conv (arr .packedElem 2 [some (.smi 1), some (.arr 0)]) comma 2 with
  | .bailout => true
  | _ => false)

def ten : List (Option Val) := (List.range 10).map fun i => some (.smi (Int.ofNat i))

#guard resList (fastArrayJoin lim conv (arr .packedSmi 10 ten) comma 10) ==
  some [48, 44, 49, 44, 50, 44, 51, 44, 52, 44, 53, 44, 54, 44, 55, 44, 56, 44, 57]

#guard (resBuf ((fastLoop lim conv .packedSmi ten comma 10 0 (newBuffer lim 10) 0).bind
  fun r => .ok r.1)).map (fun b => b.full.length) == some 3

#guard resList (fastArrayJoin lim conv (arr .packedSmi 10 ten) comma 10) ==
  some (fastSpec conv (arr .packedSmi 10 ten) comma.chars 10)

def holey : JSArr := arr .holeySmi 3 [some (.smi 1), none, some (.smi 2)]

def localeEnv (onEmpty : Option Str) : Env Unit where
  arr := fun _ => holey
  protector := fun _ => true
  get := fun k _ => some ((holey.store.getD k none).getD .undef, ())
  conv := fun e _ =>
    match e with
    | .empty => some (onEmpty, ())
    | .val v => (conv v).map fun o => (o, ())

def joined : Res (List Nat × Unit × List (List Nat)) → Option (List Nat)
  | .ok (s, _, _) => some s
  | _ => none

#guard joined (implJoin lim (localeEnv (some ⟨9, [88]⟩)) .holeySmi .fastObj comma 3 ()) ==
  some [49, 44, 88, 44, 50]

#guard joined (implJoin lim (localeEnv (some ⟨9, [88]⟩)) .holeySmi .generic comma 3 ()) ==
  some [49, 44, 44, 50]

#guard joined (implJoin lim (localeEnv none) .holeySmi .fastObj comma 3 ()) == some [49, 44, 44, 50]

#guard pushInline none 1 = some (true, some [some 1, none])

#guard (pushInline (some [some 1, none]) 1) = some (false, some [some 1, none])

def pushPop : Option Stack := do
  let (_, s1) ← pushInline none 1
  let (_, s2) ← pushInline s1 2
  let (_, s3) ← pushInline s2 3
  let s4 ← popInline s3 3
  let s5 ← popInline s4 2
  popInline s5 1

#guard pushPop = some (some [none, none])

#guard (do
  let (_, s1) ← pushInline none 1
  let (_, s2) ← pushInline s1 2
  let (_, s3) ← pushInline s2 3
  pure s3 : Option Stack) =
    some (some ([some 1, some 2, some 3] ++ List.replicate (grow 2 - 2 - 1) none))

#guard popInline (some [some 1, none]) 2 = none

end ArrayJoin.Examples
