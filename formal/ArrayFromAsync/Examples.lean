import ArrayFromAsync.Agreement

namespace ArrayFromAsync.Examples

open Torque ArrayFromAsync

def smiMax : Nat := SmiRepr.compressed.max

def view : Outcome (List Op × End) → Option (List Op × End)
  | .ok r => some r
  | _ => none

def v8 (inp : Input) (rs : List Resp) : Option (List Op × End) := view (run smiMax 64 inp rs)

def spec (inp : Input) (rs : List Resp) : List Op × End × List Dev := specRun smiMax 64 inp rs

def agrees (inp : Input) (rs : List Resp) : Bool :=
  v8 inp rs == some ((spec inp rs).1, (spec inp rs).2.1)

def A : JSVal := .obj 5

def items : JSVal := .obj 1

def iterator : JSVal := .obj 3

def nextFn : JSVal := .fn 4

def mapper : JSVal := .fn 20

def plain : Input := ⟨.ctor 0, items, .undef, .undef⟩

def mapped : Input := ⟨.ctor 0, items, mapper, .undef⟩

def openAsync : List Resp := [.ok (.fn 2), .ok iterator, .ok nextFn, .ok A]

def openOps : List Op :=
  [.getAsyncIteratorMethod items, .callIteratorMethod (.fn 2) items, .getNextMethod iterator,
    .construct (.ctor 0) none]

def yieldValue (v : JSVal) : List Resp :=
  [.ok (.promise 6), .ok .undef, .ok (.obj 7), .ok (.bool false), .ok v]

def yieldOps : List Op :=
  [.callNext nextFn iterator, .await (.promise 6), .iteratorComplete (.obj 7), .iteratorValue (.obj 7)]

def finish : List Resp := [.ok (.promise 6), .ok .undef, .ok (.obj 8), .ok (.bool true), .ok .undef]

def finishOps (n : Int) : List Op :=
  [.callNext nextFn iterator, .await (.promise 6), .iteratorComplete (.obj 8), .setLength A n,
    .resolve A]

def defined : List Resp := [.ok .undef]

def mapTo (m : JSVal) : List Resp := [.ok (.promise 11), .ok .undef, .ok m]

def twoValues : List Resp :=
  openAsync ++ yieldValue (.smi 10) ++ defined ++ yieldValue (.smi 20) ++ defined ++ finish

#guard v8 plain twoValues ==
  some (openOps ++ yieldOps ++ [.define A 0 (.smi 10)] ++ yieldOps ++ [.define A 1 (.smi 20)] ++
    finishOps 2, .settled)

#guard agrees plain twoValues && (spec plain twoValues).2.2 == []

def twoMapped : List Resp :=
  openAsync ++ yieldValue (.smi 10) ++ mapTo (.smi 100) ++ defined ++ yieldValue (.smi 20) ++
    mapTo (.smi 200) ++ defined ++ finish

#guard v8 mapped twoMapped ==
  some (openOps ++ yieldOps ++
    [.callMapfn mapper .undef (.smi 10) 0, .await (.promise 11), .define A 0 (.smi 100)] ++ yieldOps ++
    [.callMapfn mapper .undef (.smi 20) 1, .await (.promise 11), .define A 1 (.smi 200)] ++
    finishOps 2, .settled)

#guard agrees mapped twoMapped && (spec mapped twoMapped).2.2 == []

def mappedRejects : List Resp :=
  openAsync ++ yieldValue (.smi 10) ++ mapTo (.smi 100) ++ defined ++ yieldValue (.smi 20) ++
    [.ok (.promise 11), .ok .undef, .err (.str 5), .ok .undef]

#guard v8 mapped mappedRejects ==
  some (openOps ++ yieldOps ++
    [.callMapfn mapper .undef (.smi 10) 0, .await (.promise 11), .define A 0 (.smi 100)] ++ yieldOps ++
    [.callMapfn mapper .undef (.smi 20) 1, .await (.promise 11), .getReturn iterator, .reject (.str 5)],
    .settled)

#guard agrees mapped mappedRejects && (spec mapped mappedRejects).2.2 == []

def arrayLike : List Resp :=
  [.ok .undef, .ok .undef, .ok (.smi 2), .ok A, .ok (.smi 1), .ok .undef, .ok (.smi 1), .ok .undef,
    .err (.str 9)]

#guard v8 plain arrayLike ==
  some ([.getAsyncIteratorMethod items, .getIteratorMethod items, .getLength items,
    .construct (.ctor 0) (some 2), .get items 0, .await (.smi 1), .define A 0 (.smi 1), .get items 1,
    .reject (.str 9)], .settled)

#guard agrees plain arrayLike && (spec plain arrayLike).2.2 == []

def arrayLikeDone : List Resp :=
  [.ok .undef, .ok .null, .ok (.smi 1), .ok A, .ok (.smi 7), .ok .undef, .ok (.smi 7), .ok (.promise 11),
    .ok .undef, .ok (.smi 49), .ok .undef, .ok .undef]

#guard v8 mapped arrayLikeDone ==
  some ([.getAsyncIteratorMethod items, .getIteratorMethod items, .getLength items,
    .construct (.ctor 0) (some 1), .get items 0, .await (.smi 7), .callMapfn mapper .undef (.smi 7) 0,
    .await (.promise 11), .define A 0 (.smi 49), .setLength A 1, .resolve A], .settled)

#guard agrees mapped arrayLikeDone && (spec mapped arrayLikeDone).2.2 == []

#guard agrees mapped (arrayLikeDone.take 6) && agrees plain [] && agrees mapped (twoMapped.take 13)

def nextRejects : List Resp :=
  openAsync ++ yieldValue (.smi 10) ++ defined ++ [.ok (.promise 6), .ok .undef, .err (.str 5), .ok .undef]

#guard v8 plain nextRejects ==
  some (openOps ++ yieldOps ++
    [.define A 0 (.smi 10), .callNext nextFn iterator, .await (.promise 6), .getReturn iterator,
      .reject (.str 5)], .settled)

#guard (spec plain nextRejects).1 ==
  openOps ++ yieldOps ++
    [.define A 0 (.smi 10), .callNext nextFn iterator, .await (.promise 6), .reject (.str 5)]

#guard !agrees plain nextRejects && (spec plain nextRejects).2.2 == [.closesIterator]

def nextThrows : List Resp := openAsync ++ [.err (.str 5), .ok .undef]

#guard v8 plain nextThrows ==
  some (openOps ++ [.callNext nextFn iterator, .getReturn iterator, .reject (.str 5)], .settled)

#guard (spec plain nextThrows).1 == openOps ++ [.callNext nextFn iterator, .reject (.str 5)]

def returnGetterThrows : List Resp := openAsync ++ yieldValue (.smi 10) ++ [.err (.str 7), .err (.str 8)]

#guard v8 mapped returnGetterThrows ==
  some (openOps ++ yieldOps ++ [.callMapfn mapper .undef (.smi 10) 0, .getReturn iterator], .idle)

#guard spec mapped returnGetterThrows ==
  (openOps ++ yieldOps ++
    [.callMapfn mapper .undef (.smi 10) 0, .getReturn iterator, .reject (.str 7)], .settled,
    [.closeAbrupt])

def returnRejects : List Resp :=
  openAsync ++ yieldValue (.smi 10) ++
    [.err (.str 7), .ok (.fn 30), .ok (.promise 31), .ok .undef, .err (.str 32), .ok .undef]

#guard v8 mapped returnRejects ==
  some (openOps ++ yieldOps ++
    [.callMapfn mapper .undef (.smi 10) 0, .getReturn iterator, .callReturn (.fn 30) iterator,
      .await (.promise 31), .getReturn iterator, .reject (.str 32)], .settled)

#guard spec mapped returnRejects ==
  (openOps ++ yieldOps ++
    [.callMapfn mapper .undef (.smi 10) 0, .getReturn iterator, .callReturn (.fn 30) iterator,
      .await (.promise 31), .reject (.str 7)], .settled, [.closeRejected])

def threeValues : List Resp :=
  openAsync ++ yieldValue (.smi 10) ++ defined ++ yieldValue (.smi 20) ++ defined ++
    yieldValue (.smi 30) ++ defined ++ finish

#guard view (run 1 64 plain threeValues) ==
  some (openOps ++ yieldOps ++ [.define A 0 (.smi 10)] ++ yieldOps ++ [.define A 1 (.smi 20)] ++
    yieldOps ++ [.define A (-2) (.smi 30)] ++ finishOps (-1), .settled)

#guard specRun 1 64 plain threeValues ==
  (openOps ++ yieldOps ++ [.define A 0 (.smi 10)] ++ yieldOps ++ [.define A 1 (.smi 20)] ++
    yieldOps ++ [.define A 2 (.smi 30)] ++ finishOps 3, .settled, [.indexOverflow])

def arrayLikeThree : List Resp :=
  [.ok .undef, .ok .undef, .ok (.smi 3), .ok A] ++
    [.ok (.smi 1), .ok .undef, .ok (.smi 1), .ok .undef, .ok (.smi 2), .ok .undef, .ok (.smi 2),
      .ok .undef, .ok (.smi 3), .ok .undef]

#guard (view (run 1 64 plain arrayLikeThree)).map (·.1.drop 10) ==
  some [.get items (-2), .await (.smi 3)]

#guard ((specRun 1 64 plain arrayLikeThree).1.drop 10, (specRun 1 64 plain arrayLikeThree).2.2) ==
  ([.get items 2, .await (.smi 3)], [.indexOverflow])

#guard smiInc smiMax smiMax = -1073741824

def resumeView : Outcome (Exit × IterCtx × W) → Option (Exit × JSVal × List Op)
  | .ok (x, c, w) => some (x, c.index, w.tr.reverse)
  | _ => none

def atSmiMax : IterCtx :=
  { initIterCtx mapped iterator nextFn A with step := .smi Label.getIteratorValueWithMapping.code, index := .smi smiMax }

#guard resumeView (iterOnFulfilled smiMax atSmiMax (.smi 1) ⟨[.ok .undef, .ok (.promise 6), .ok .undef], []⟩) ==
  some (.suspended, .smi (-1073741824),
    [.define A 1073741823 (.smi 1), .callNext nextFn iterator, .await (.promise 6)])

def afterWrap : IterCtx :=
  { atSmiMax with step := .smi Label.checkIteratorValueAndMapping.code, index := .smi (-1073741824) }

#guard resumeView (iterOnFulfilled smiMax afterWrap (.obj 7) ⟨[.ok (.bool false), .ok (.smi 2), .ok (.promise 11), .ok .undef], []⟩) ==
  some (.suspended, .smi (-1073741824),
    [.iteratorComplete (.obj 7), .iteratorValue (.obj 7), .callMapfn mapper .undef (.smi 2) (-1073741824),
      .await (.promise 11)])

def syncIterable : List Resp := [.ok .undef, .ok (.fn 2), .ok iterator, .ok nextFn, .ok nextFn, .ok A] ++ finish

#guard v8 plain syncIterable ==
  some ([.getAsyncIteratorMethod items, .getIteratorMethod items, .callIteratorMethod (.fn 2) items,
    .getNextMethod iterator, .getNextMethod iterator, .construct (.ctor 0) none,
    .callNext .asyncFromSyncNext .asyncFromSyncIterator, .await (.promise 6), .iteratorComplete (.obj 8),
    .setLength A 0, .resolve A], .settled)

#guard ((spec plain syncIterable).1.take 5, (spec plain syncIterable).2.2.head?) ==
  ([.getAsyncIteratorMethod items, .getIteratorMethod items, .callIteratorMethod (.fn 2) items,
    .getNextMethod iterator, .construct (.ctor 0) none], some .nextReadTwice)

#guard (runEvents smiMax mapped [.reject (.str 1), .fulfil (.smi 3), .fulfil .undef, .reject .undef]
  twoMapped) matches .ok _

#guard (runEvents smiMax plain [.fulfil (.obj 7), .fulfil (.obj 7), .reject (.str 2)] arrayLike) matches .ok _

#guard (v8 mapped returnRejects).map (fun r => r.1.countP Op.isSettle) == some 1

#guard (v8 mapped returnGetterThrows).map (fun r => r.1.countP Op.isSettle) == some 0

end ArrayFromAsync.Examples
