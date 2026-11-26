import ArrayFromAsync.Model

namespace ArrayFromAsync

open Torque

def cnt (tr : List Op) : Nat := tr.countP Op.isSettle

def bit (x : Exit) : Nat := if x = .settled then 1 else 0

theorem cnt_cons_of {o : Op} (h : o.isSettle = false) (tr : List Op) : cnt (o :: tr) = cnt tr := by
  simp [cnt, h]

@[simp] theorem cnt_cons (o : Op) (tr : List Op) :
    cnt (o :: tr) = cnt tr + (if o.isSettle then 1 else 0) := by
  cases h : o.isSettle <;> simp [cnt, h]

theorem cnt_settle {o : Op} (h : o.isSettle = true) (tr : List Op) : cnt (o :: tr) = cnt tr + 1 := by
  simp [cnt, h]

theorem chk_true {α : Type} {t : Ty} {v : JSVal} {k : JSVal → Outcome α} (h : t.holds v = true) :
    chk t v k = k v := by
  simp [chk, h]

theorem chk_any {α : Type} {v : JSVal} {k : JSVal → Outcome α} : chk .any v k = k v := rfl

theorem perform_ind {β : Type} {P : β → Prop} {o : Op} {w : W} {exh : W → β}
    {k : Resp → W → β} (h1 : ∀ w' : W, w'.tr = o :: w.tr → P (exh w'))
    (h2 : ∀ r w', w'.tr = o :: w.tr → P (k r w')) : P (perform o w exh k) := by
  unfold perform
  split
  · exact h1 _ rfl
  · exact h2 _ _ rfl

theorem obind_ok {α β : Type} (a : α) (f : α → Outcome β) : obind (.ok a) f = f a := rfl

theorem omap_ok {α β : Type} (a : α) (f : α → β) : omap f (.ok a) = .ok (f a) := rfl

def OkWith {α : Type} (Q : α → Prop) (x : Outcome α) : Prop := ∃ a, x = .ok a ∧ Q a

theorem OkWith.ok {α : Type} {Q : α → Prop} {a : α} (h : Q a) : OkWith Q (.ok a) := ⟨a, rfl, h⟩

theorem OkWith.bind {α β : Type} {Q : α → Prop} {R : β → Prop} {v : Outcome α}
    {f : α → Outcome β} (h : OkWith Q v) (hf : ∀ a, Q a → OkWith R (f a)) :
    OkWith R (obind v f) := by
  obtain ⟨a, rfl, ha⟩ := h
  exact hf a ha

theorem OkWith.map {α β : Type} {Q : α → Prop} {R : β → Prop} {v : Outcome α} {f : α → β}
    (h : OkWith Q v) (hf : ∀ a, Q a → R (f a)) : OkWith R (omap f v) :=
  h.bind fun a ha => OkWith.ok (hf a ha)

theorem OkWith.chk {α : Type} {Q : α → Prop} {t : Ty} {v : JSVal} {k : JSVal → Outcome α}
    (h : t.holds v = true) (hk : OkWith Q (k v)) : OkWith Q (chk t v k) := by
  rw [chk_true h]
  exact hk

def Label.iterResumable : Label → Bool
  | .getIteratorStep => true
  | .checkIteratorValueAndMapping => true
  | .getIteratorValueWithMapping => true
  | .closeAsyncIterator => true
  | .rejectPromise => true
  | _ => false

def Label.iterHandled : Label → Bool
  | .getArrayLikeValue => false
  | .checkArrayLikeValueAndMapping => false
  | .getArrayLikeValueWithMapping => false
  | .addArrayLikeValueToTheArray => false
  | _ => true

def Label.iterRank : Label → Nat
  | .checkIteratorValueAndMapping => 2
  | .getIteratorValueWithMapping => 2
  | .addIteratorValueToTheArray => 1
  | .closeAsyncIterator => 1
  | _ => 0

def Label.alResumable : Label → Bool
  | .getArrayLikeValue => true
  | .checkArrayLikeValueAndMapping => true
  | .addArrayLikeValueToTheArray => true
  | .rejectPromise => true
  | _ => false

def Label.alHandled : Label → Bool
  | .getArrayLikeValue => true
  | .checkArrayLikeValueAndMapping => true
  | .getArrayLikeValueWithMapping => true
  | .addArrayLikeValueToTheArray => true
  | .doneAndResolvePromise => true
  | .rejectPromise => true
  | _ => false

def Label.alRank : Label → Nat
  | .checkArrayLikeValueAndMapping => 3
  | .addArrayLikeValueToTheArray => 2
  | .getArrayLikeValue => 1
  | _ => 0

def MapfnOK (f : JSVal) : Prop := f = .undef ∨ f.isCallable = true

structure IterInv (c : IterCtx) : Prop where
  step : ∃ l : Label, c.step = .smi l.code ∧ l.iterResumable = true
  index : c.index.isSmi = true
  promise : c.promise.isPromise = true
  promiseFunction : c.promiseFunction = .promiseCtor
  onFulfilled : c.onFulfilled.isFunctionOrUndefined = true
  onRejected : c.onRejected.isFunctionOrUndefined = true
  resultArray : c.resultArray.isReceiver = true
  iterator : c.iterator.isReceiver = true
  mapfn : MapfnOK c.mapfn

structure ALInv (c : ALCtx) : Prop where
  step : ∃ l : Label, c.step = .smi l.code ∧ l.alResumable = true
  len : c.len.isNumber = true
  index : c.index.isSmi = true
  promise : c.promise.isPromise = true
  promiseFunction : c.promiseFunction = .promiseCtor
  onFulfilled : c.onFulfilled.isFunctionOrUndefined = true
  onRejected : c.onRejected.isFunctionOrUndefined = true
  resultArray : c.resultArray.isReceiver = true
  arrayLike : c.arrayLike.isReceiver = true
  mapfn : MapfnOK c.mapfn

def ResGood {σ : Type} (I : σ → Prop) (n : Nat) : Res σ → Prop
  | .exit x c w => I c ∧ cnt w.tr = n + bit x
  | .thrown _ c w => I c ∧ cnt w.tr = n

def AwGood {σ : Type} (I : σ → Prop) (n : Nat) : Aw σ → Prop
  | .registered c w => I c ∧ cnt w.tr = n
  | .thrown _ c w => I c ∧ cnt w.tr = n
  | .exhausted c w => I c ∧ cnt w.tr = n

def CloseGood {σ : Type} (I : σ → Prop) (n : Nat) : CloseRes σ → Prop
  | .normal _ c w => I c ∧ cnt w.tr = n
  | .rejectPromise c w => I c ∧ cnt w.tr = n
  | .exhausted c w => I c ∧ cnt w.tr = n

def BodyGood {σ : Type} (I : σ → Prop) (n : Nat) (r : Exit × σ × W) : Prop :=
  I r.2.1 ∧ cnt r.2.2.tr = n + bit r.1

theorem promiseResolve_promise (v : JSVal) : (promiseResolve .promiseCtor v).isPromise = true := by
  unfold promiseResolve
  cases v <;> rfl

theorem Aw.toRes_good {σ : Type} {I : σ → Prop} {n : Nat} {a : Aw σ} (h : AwGood I n a) :
    ResGood I n a.toRes := by
  cases a <;> simpa [Aw.toRes, ResGood, AwGood, bit] using h

theorem Aw.toClose_good {σ : Type} {I : σ → Prop} {n : Nat} {a : Aw σ} (h : AwGood I n a) :
    CloseGood I n a.toClose := by
  cases a <;> simpa [Aw.toClose, CloseGood, AwGood] using h

theorem IterInv.setStep {c : IterCtx} (h : IterInv c) {l : Label} (hl : l.iterResumable = true) :
    IterInv { c with step := .smi l.code } :=
  { h with step := ⟨l, rfl, hl⟩ }

theorem iterAwaitPoint_good {c : IterCtx} (hc : IterInv c) {l : Label} (hl : l.iterResumable = true)
    (v : JSVal) (w : W) : OkWith (AwGood IterInv (cnt w.tr)) (iterAwaitPoint c l v w) := by
  have hc' := hc.setStep hl
  unfold iterAwaitPoint
  refine OkWith.chk (by simp [Ty.holds, hc.promiseFunction, JSVal.isReceiver]) ?_
  refine OkWith.chk (by simpa [Ty.holds] using hc.onFulfilled) ?_
  refine OkWith.chk (by simpa [Ty.holds] using hc.onRejected) ?_
  apply perform_ind
  · intro w' hw'
    exact OkWith.ok ⟨hc', by simp [hw', cnt_cons, Op.isSettle]⟩
  · intro r w' hw'
    cases r with
    | err e => exact OkWith.ok ⟨hc', by simp [hw', cnt_cons, Op.isSettle]⟩
    | ok _ =>
      refine OkWith.chk (by simpa [Ty.holds, hc.promiseFunction] using promiseResolve_promise v) ?_
      exact OkWith.ok ⟨hc', by simp [hw', cnt_cons, Op.isSettle]⟩

theorem iterClose_good {c : IterCtx} (hc : IterInv c) (it : JSVal) (w : W) :
    OkWith (CloseGood IterInv (cnt w.tr)) (iterClose c it w) := by
  unfold iterClose
  apply perform_ind
  · intro w' hw'
    exact OkWith.ok ⟨hc, by simp [hw', cnt_cons, Op.isSettle]⟩
  · intro r w' hw'
    cases r with
    | err e => exact OkWith.ok ⟨hc, by simp [hw', cnt_cons, Op.isSettle]⟩
    | ok m =>
      simp only
      split
      · exact OkWith.ok ⟨hc, by simp [hw', cnt_cons, Op.isSettle]⟩
      split
      · apply perform_ind
        · intro w'' hw''
          exact OkWith.ok ⟨hc, by simp [hw'', hw', cnt_cons, Op.isSettle]⟩
        · intro r w'' hw''
          cases r with
          | err e => exact OkWith.ok ⟨hc, by simp [hw'', hw', cnt_cons, Op.isSettle]⟩
          | ok ir =>
            have hn : cnt w''.tr = cnt w.tr := by simp [hw'', hw', cnt_cons, Op.isSettle]
            refine (iterAwaitPoint_good hc (l := .rejectPromise) rfl ir w'').map ?_
            intro a ha
            rw [hn] at ha
            exact Aw.toClose_good ha
      · exact OkWith.ok ⟨hc, by simp [hw', cnt_cons, Op.isSettle]⟩

def IterLocOK (mapfn : JSVal) (fuel : Nat) (s : IterLocals) : Prop :=
  ∃ l : Label, s.step = some l ∧ l.iterHandled = true ∧ l.iterRank < fuel ∧
    (l = .iteratorMapping → mapfn ≠ .undef)

theorem iterLoop_good (smiMax : Nat) {mapfn thisArg arr : JSVal} (hm : MapfnOK mapfn)
    (ha : arr.isReceiver = true) :
    ∀ (fuel : Nat) (s : IterLocals) (c : IterCtx) (w : W), IterInv c → IterLocOK mapfn fuel s →
      OkWith (ResGood IterInv (cnt w.tr)) (iterLoop smiMax mapfn thisArg arr fuel s c w)
  | 0, _, _, _, _, ⟨_, _, _, hr, _⟩ => absurd hr (Nat.not_lt_zero _)
  | fuel + 1, ⟨st, av, ix, mv, nv⟩, c, w, hc, ⟨l, hs, hh, hr, hmap⟩ => by
    simp only at hs
    subst hs
    cases l with
    | getIteratorStep =>
      simp only [iterLoop]
      refine OkWith.chk (by simpa [Ty.holds] using hc.iterator) ?_
      refine OkWith.chk rfl ?_
      split
      · apply perform_ind
        · intro w' hw'
          exact OkWith.ok ⟨hc, by simp [hw', Op.isSettle, bit]⟩
        · intro r w' hw'
          cases r with
          | err e => exact OkWith.ok ⟨hc, by simp [hw', Op.isSettle]⟩
          | ok v =>
            have hn : cnt w'.tr = cnt w.tr := by simp [hw', Op.isSettle]
            refine (iterAwaitPoint_good hc (l := .checkIteratorValueAndMapping) rfl v w').map ?_
            intro a h
            rw [hn] at h
            exact Aw.toRes_good h
      · exact OkWith.ok ⟨hc, rfl⟩
    | checkIteratorValueAndMapping =>
      simp only [Label.iterRank] at hr
      simp only [iterLoop]
      split
      · apply perform_ind
        · intro w' hw'
          exact OkWith.ok ⟨hc, by simp [hw', Op.isSettle, bit]⟩
        · intro r w' hw'
          have hn : cnt w'.tr = cnt w.tr := by simp [hw', Op.isSettle]
          cases r with
          | err e => exact OkWith.ok ⟨hc, hn⟩
          | ok d =>
            simp only
            split
            · rw [← hn]
              exact iterLoop_good smiMax hm ha fuel _ c w' hc
                ⟨.doneAndResolvePromise, rfl, rfl, by simp [Label.iterRank]; omega, by simp⟩
            · apply perform_ind
              · intro w'' hw''
                exact OkWith.ok ⟨hc, by simp [hw'', hn, Op.isSettle, bit]⟩
              · intro r w'' hw''
                have hn' : cnt w''.tr = cnt w.tr := by simp [hw'', hn, Op.isSettle]
                cases r with
                | err e => exact OkWith.ok ⟨hc, hn'⟩
                | ok v =>
                  simp only
                  split
                  · rw [← hn']
                    exact iterLoop_good smiMax hm ha fuel _ c w'' hc
                      ⟨.addIteratorValueToTheArray, rfl, rfl, by simp [Label.iterRank]; omega, by simp⟩
                  · rename_i hne
                    rw [← hn']
                    exact iterLoop_good smiMax hm ha fuel _ c w'' hc
                      ⟨.iteratorMapping, rfl, rfl, by simp [Label.iterRank]; omega, fun _ => hne⟩
      · exact OkWith.ok ⟨hc, rfl⟩
    | iteratorMapping =>
      have hf : mapfn.isCallable = true := by
        rcases hm with h | h
        · exact absurd h (hmap rfl)
        · exact h
      simp only [iterLoop]
      refine OkWith.chk (by simpa [Ty.holds] using hf) ?_
      apply perform_ind
      · intro w' hw'
        exact OkWith.ok ⟨hc, by simp [hw', Op.isSettle, bit]⟩
      · intro r w' hw'
        have hn : cnt w'.tr = cnt w.tr := by simp [hw', Op.isSettle]
        cases r with
        | err e => exact OkWith.ok ⟨hc, hn⟩
        | ok m =>
          refine (iterAwaitPoint_good hc (l := .getIteratorValueWithMapping) rfl m w').map ?_
          intro a h
          rw [hn] at h
          exact Aw.toRes_good h
    | getIteratorValueWithMapping =>
      simp only [Label.iterRank] at hr
      simp only [iterLoop]
      exact iterLoop_good smiMax hm ha fuel _ c w hc
        ⟨.addIteratorValueToTheArray, rfl, rfl, by simp [Label.iterRank]; omega, by simp⟩
    | addIteratorValueToTheArray =>
      simp only [Label.iterRank] at hr
      simp only [iterLoop]
      apply perform_ind
      · intro w' hw'
        exact OkWith.ok ⟨hc, by simp [hw', Op.isSettle, bit]⟩
      · intro r w' hw'
        have hn : cnt w'.tr = cnt w.tr := by simp [hw', Op.isSettle]
        cases r with
        | err e => exact OkWith.ok ⟨hc, hn⟩
        | ok _ =>
          simp only
          rw [← hn]
          exact iterLoop_good smiMax hm ha fuel _ _ w' { hc with index := rfl }
            ⟨.getIteratorStep, rfl, rfl, by simp [Label.iterRank]; omega, by simp⟩
    | doneAndResolvePromise =>
      simp only [iterLoop]
      apply perform_ind
      · intro w' hw'
        exact OkWith.ok ⟨hc, by simp [hw', Op.isSettle, bit]⟩
      · intro r w' hw'
        have hn : cnt w'.tr = cnt w.tr := by simp [hw', Op.isSettle]
        cases r with
        | err e => exact OkWith.ok ⟨hc, hn⟩
        | ok _ =>
          refine OkWith.chk (by simpa [Ty.holds] using hc.promise) ?_
          exact OkWith.ok ⟨hc, by simp [W.emit, hn, Op.isSettle, bit]⟩
    | closeAsyncIterator =>
      simp only [Label.iterRank] at hr
      simp only [iterLoop]
      refine OkWith.chk (by simpa [Ty.holds] using hc.iterator) ?_
      refine OkWith.chk rfl ?_
      refine (iterClose_good hc c.iterator w).bind ?_
      intro a h
      cases a with
      | normal reg c' w' =>
        exact OkWith.ok ⟨h.1, by cases reg <;> simp [h.2, bit]⟩
      | rejectPromise c' w' =>
        simp only
        rw [← h.2]
        exact iterLoop_good smiMax hm ha fuel _ c' w' h.1
          ⟨.rejectPromise, rfl, rfl, by simp [Label.iterRank]; omega, by simp⟩
      | exhausted c' w' => exact OkWith.ok ⟨h.1, by simp [h.2, bit]⟩
    | rejectPromise =>
      simp only [iterLoop]
      refine OkWith.chk rfl ?_
      refine OkWith.chk (by simpa [Ty.holds] using hc.promise) ?_
      exact OkWith.ok ⟨hc, by simp [W.emit, Op.isSettle, bit]⟩
    | getArrayLikeValue => simp [Label.iterHandled] at hh
    | checkArrayLikeValueAndMapping => simp [Label.iterHandled] at hh
    | getArrayLikeValueWithMapping => simp [Label.iterHandled] at hh
    | addArrayLikeValueToTheArray => simp [Label.iterHandled] at hh

theorem iterResumable_handled {l : Label} (h : l.iterResumable = true) :
    l.iterHandled = true ∧ l.iterRank < 8 ∧ l ≠ .iteratorMapping := by
  cases l <;> simp_all [Label.iterResumable, Label.iterHandled, Label.iterRank]

theorem iterTry_good (smiMax : Nat) {c : IterCtx} (hc : IterInv c) (w : W) :
    OkWith (ResGood IterInv (cnt w.tr)) (iterTry smiMax c w) := by
  obtain ⟨l, hl, hres⟩ := hc.step
  obtain ⟨h1, h2, h3⟩ := iterResumable_handled hres
  unfold iterTry
  refine OkWith.chk rfl ?_
  refine OkWith.chk rfl ?_
  refine OkWith.chk (by simpa [Ty.holds] using hc.resultArray) ?_
  refine OkWith.chk (by simp [Ty.holds, hl, JSVal.isSmi]) ?_
  refine OkWith.chk rfl ?_
  refine OkWith.chk (by simpa [Ty.holds] using hc.index) ?_
  exact iterLoop_good smiMax hc.mapfn hc.resultArray 8 _ c w hc
    ⟨l, by simp [hl, JSVal.num, Label.decode_code], h1, h2, fun h => absurd h h3⟩

theorem iterCatch_good {c : IterCtx} (hc : IterInv c) (e : JSVal) (w : W) :
    OkWith (BodyGood IterInv (cnt w.tr)) (iterCatch c e w) := by
  have hc' : IterInv { c with error := e } := { hc with }
  unfold iterCatch
  simp only
  refine OkWith.chk (by simpa [Ty.holds] using hc.iterator) ?_
  refine OkWith.chk rfl ?_
  refine (iterClose_good hc' c.iterator w).bind ?_
  intro a h
  cases a with
  | normal reg c' w' => exact OkWith.ok ⟨h.1, by cases reg <;> simp [h.2, bit]⟩
  | rejectPromise c' w' =>
    unfold iterRejectFromSlots
    refine OkWith.chk rfl ?_
    refine OkWith.chk (by simpa [Ty.holds] using h.1.promise) ?_
    exact OkWith.ok ⟨h.1, by simp [W.emit, h.2, Op.isSettle, bit]⟩
  | exhausted c' w' => exact OkWith.ok ⟨h.1, by simp [h.2, bit]⟩

theorem iterBody_good (smiMax : Nat) {c : IterCtx} (hc : IterInv c) (w : W) :
    OkWith (BodyGood IterInv (cnt w.tr)) (iterBody smiMax c w) := by
  unfold iterBody
  refine (iterTry_good smiMax hc w).bind ?_
  intro r h
  unfold iterHandler
  cases r with
  | exit x c' w' => exact OkWith.ok h
  | thrown e c' w' =>
    have := iterCatch_good h.1 e w'
    rw [h.2] at this
    exact this

theorem ALInv.setStep {c : ALCtx} (h : ALInv c) {l : Label} (hl : l.alResumable = true) :
    ALInv { c with step := .smi l.code } :=
  { h with step := ⟨l, rfl, hl⟩ }

theorem alAwaitPoint_good {c : ALCtx} (hc : ALInv c) {l : Label} (hl : l.alResumable = true)
    (v : JSVal) (w : W) : OkWith (AwGood ALInv (cnt w.tr)) (alAwaitPoint c l v w) := by
  have hc' := hc.setStep hl
  unfold alAwaitPoint
  refine OkWith.chk (by simp [Ty.holds, hc.promiseFunction, JSVal.isReceiver]) ?_
  refine OkWith.chk (by simpa [Ty.holds] using hc.onFulfilled) ?_
  refine OkWith.chk (by simpa [Ty.holds] using hc.onRejected) ?_
  apply perform_ind
  · intro w' hw'
    exact OkWith.ok ⟨hc', by simp [hw', Op.isSettle]⟩
  · intro r w' hw'
    cases r with
    | err e => exact OkWith.ok ⟨hc', by simp [hw', Op.isSettle]⟩
    | ok _ =>
      refine OkWith.chk (by simpa [Ty.holds, hc.promiseFunction] using promiseResolve_promise v) ?_
      exact OkWith.ok ⟨hc', by simp [hw', Op.isSettle]⟩

def ALLocOK (mapfn : JSVal) (fuel : Nat) (s : ALLocals) : Prop :=
  ∃ l : Label, s.step = some l ∧ l.alHandled = true ∧ l.alRank < fuel ∧
    (l = .getArrayLikeValueWithMapping → mapfn ≠ .undef)

theorem alLoop_good (smiMax : Nat) {mapfn thisArg arr : JSVal} (hm : MapfnOK mapfn)
    (ha : arr.isReceiver = true) :
    ∀ (fuel : Nat) (s : ALLocals) (c : ALCtx) (w : W), ALInv c → ALLocOK mapfn fuel s →
      OkWith (ResGood ALInv (cnt w.tr)) (alLoop smiMax mapfn thisArg arr fuel s c w)
  | 0, _, _, _, _, ⟨_, _, _, hr, _⟩ => absurd hr (Nat.not_lt_zero _)
  | fuel + 1, ⟨st, av, len, ix⟩, c, w, hc, ⟨l, hs, hh, hr, hmap⟩ => by
    simp only at hs
    subst hs
    cases l with
    | getArrayLikeValue =>
      simp only [Label.alRank] at hr
      simp only [alLoop]
      refine OkWith.chk (by simpa [Ty.holds] using hc.arrayLike) ?_
      split
      · apply perform_ind
        · intro w' hw'
          exact OkWith.ok ⟨hc, by simp [hw', Op.isSettle, bit]⟩
        · intro r w' hw'
          have hn : cnt w'.tr = cnt w.tr := by simp [hw', Op.isSettle]
          cases r with
          | err e => exact OkWith.ok ⟨hc, hn⟩
          | ok v =>
            refine (alAwaitPoint_good hc (l := .checkArrayLikeValueAndMapping) rfl v w').map ?_
            intro a h
            rw [hn] at h
            exact Aw.toRes_good h
      · exact alLoop_good smiMax hm ha fuel _ c w hc
          ⟨.doneAndResolvePromise, rfl, rfl, by simp [Label.alRank]; omega, by simp⟩
    | checkArrayLikeValueAndMapping =>
      simp only [Label.alRank] at hr
      simp only [alLoop]
      split
      · exact alLoop_good smiMax hm ha fuel _ c w hc
          ⟨.addArrayLikeValueToTheArray, rfl, rfl, by simp [Label.alRank]; omega, by simp⟩
      · rename_i hne
        exact alLoop_good smiMax hm ha fuel _ c w hc
          ⟨.getArrayLikeValueWithMapping, rfl, rfl, by simp [Label.alRank]; omega, fun _ => hne⟩
    | getArrayLikeValueWithMapping =>
      have hf : mapfn.isCallable = true := by
        rcases hm with h | h
        · exact absurd h (hmap rfl)
        · exact h
      simp only [alLoop]
      refine OkWith.chk (by simpa [Ty.holds] using hf) ?_
      apply perform_ind
      · intro w' hw'
        exact OkWith.ok ⟨hc, by simp [hw', Op.isSettle, bit]⟩
      · intro r w' hw'
        have hn : cnt w'.tr = cnt w.tr := by simp [hw', Op.isSettle]
        cases r with
        | err e => exact OkWith.ok ⟨hc, hn⟩
        | ok m =>
          refine (alAwaitPoint_good hc (l := .addArrayLikeValueToTheArray) rfl m w').map ?_
          intro a h
          rw [hn] at h
          exact Aw.toRes_good h
    | addArrayLikeValueToTheArray =>
      simp only [Label.alRank] at hr
      simp only [alLoop]
      apply perform_ind
      · intro w' hw'
        exact OkWith.ok ⟨hc, by simp [hw', Op.isSettle, bit]⟩
      · intro r w' hw'
        have hn : cnt w'.tr = cnt w.tr := by simp [hw', Op.isSettle]
        cases r with
        | err e => exact OkWith.ok ⟨hc, hn⟩
        | ok _ =>
          simp only
          rw [← hn]
          exact alLoop_good smiMax hm ha fuel _ _ w' { hc with index := rfl }
            ⟨.getArrayLikeValue, rfl, rfl, by simp [Label.alRank]; omega, by simp⟩
    | doneAndResolvePromise =>
      simp only [alLoop]
      apply perform_ind
      · intro w' hw'
        exact OkWith.ok ⟨hc, by simp [hw', Op.isSettle, bit]⟩
      · intro r w' hw'
        have hn : cnt w'.tr = cnt w.tr := by simp [hw', Op.isSettle]
        cases r with
        | err e => exact OkWith.ok ⟨hc, hn⟩
        | ok _ =>
          refine OkWith.chk (by simpa [Ty.holds] using hc.promise) ?_
          exact OkWith.ok ⟨hc, by simp [W.emit, hn, Op.isSettle, bit]⟩
    | rejectPromise =>
      simp only [alLoop]
      refine OkWith.chk rfl ?_
      refine OkWith.chk (by simpa [Ty.holds] using hc.promise) ?_
      exact OkWith.ok ⟨hc, by simp [W.emit, Op.isSettle, bit]⟩
    | getIteratorStep => simp [Label.alHandled] at hh
    | checkIteratorValueAndMapping => simp [Label.alHandled] at hh
    | iteratorMapping => simp [Label.alHandled] at hh
    | getIteratorValueWithMapping => simp [Label.alHandled] at hh
    | addIteratorValueToTheArray => simp [Label.alHandled] at hh
    | closeAsyncIterator => simp [Label.alHandled] at hh

theorem alResumable_handled {l : Label} (h : l.alResumable = true) :
    l.alHandled = true ∧ l.alRank < 8 ∧ l ≠ .getArrayLikeValueWithMapping := by
  cases l <;> simp_all [Label.alResumable, Label.alHandled, Label.alRank]

theorem alTry_good (smiMax : Nat) {c : ALCtx} (hc : ALInv c) (w : W) :
    OkWith (ResGood ALInv (cnt w.tr)) (alTry smiMax c w) := by
  obtain ⟨l, hl, hres⟩ := hc.step
  obtain ⟨h1, h2, h3⟩ := alResumable_handled hres
  unfold alTry
  refine OkWith.chk rfl ?_
  refine OkWith.chk rfl ?_
  refine OkWith.chk (by simpa [Ty.holds] using hc.resultArray) ?_
  refine OkWith.chk (by simp [Ty.holds, hl, JSVal.isSmi]) ?_
  refine OkWith.chk rfl ?_
  refine OkWith.chk (by simpa [Ty.holds] using hc.len) ?_
  refine OkWith.chk (by simpa [Ty.holds] using hc.index) ?_
  exact alLoop_good smiMax hc.mapfn hc.resultArray 8 _ c w hc
    ⟨l, by simp [hl, JSVal.num, Label.decode_code], h1, h2, fun h => absurd h h3⟩

theorem alBody_good (smiMax : Nat) {c : ALCtx} (hc : ALInv c) (w : W) :
    OkWith (BodyGood ALInv (cnt w.tr)) (alBody smiMax c w) := by
  unfold alBody
  refine (alTry_good smiMax hc w).bind ?_
  intro r h
  unfold alHandler
  cases r with
  | exit x c' w' => exact OkWith.ok h
  | thrown e c' w' =>
    have hc' : ALInv { c' with error := e } := { h.1 with }
    unfold alCatch
    refine OkWith.chk rfl ?_
    refine OkWith.chk (by simpa [Ty.holds] using h.1.promise) ?_
    exact OkWith.ok ⟨hc', by simp [W.emit, h.2, Op.isSettle, bit]⟩

def CtxInv : Ctx → Prop
  | .iter c => IterInv c
  | .arrayLike c => ALInv c

theorem react_good (smiMax : Nat) {c : Ctx} (hc : CtxInv c) (ev : Event) (w : W) :
    OkWith (fun r => CtxInv r.2.1 ∧ cnt r.2.2.tr = cnt w.tr + bit r.1) (react smiMax c ev w) := by
  cases c with
  | iter c =>
    have hc : IterInv c := hc
    cases ev with
    | fulfil v =>
      exact (iterBody_good smiMax (c := { c with awaitedValue := v }) { hc with } w).map
        fun a h => h
    | reject v =>
      exact (iterBody_good smiMax (c := { c with step := .smi Label.closeAsyncIterator.code, error := v })
        { hc with step := ⟨.closeAsyncIterator, rfl, rfl⟩ } w).map fun a h => h
  | arrayLike c =>
    have hc : ALInv c := hc
    cases ev with
    | fulfil v =>
      exact (alBody_good smiMax (c := { c with awaitedValue := v }) { hc with } w).map
        fun a h => h
    | reject v =>
      exact (alBody_good smiMax (c := { c with step := .smi Label.rejectPromise.code, error := v })
        { hc with step := ⟨.rejectPromise, rfl, rfl⟩ } w).map fun a h => h

def StartGood (n : Nat) : Start → Prop
  | .withCtx x c w => CtxInv c ∧ cnt w.tr = n + bit x
  | .noCtx x w => x ≠ .suspended ∧ cnt w.tr = n + bit x

theorem toReceiver_isReceiver (v : JSVal) : v.toReceiver.isReceiver = true := by
  unfold JSVal.toReceiver
  split
  · assumption
  · rfl

theorem startReject_good {n : Nat} {w : W} (hw : cnt w.tr = n) (e : JSVal) :
    OkWith (StartGood n) (startReject e w) :=
  OkWith.ok ⟨by simp, by simp [W.emit, hw, Op.isSettle, bit]⟩

theorem startExh_good {n : Nat} {w : W} (hw : cnt w.tr = n) :
    OkWith (StartGood n) (startExh w) :=
  OkWith.ok ⟨by simp, by simp [hw, bit]⟩

theorem perform_start {n : Nat} {o : Op} (ho : o.isSettle = false) {w : W} (hw : cnt w.tr = n)
    {k : Resp → W → Outcome Start}
    (hk : ∀ r w', cnt w'.tr = n → OkWith (StartGood n) (k r w')) :
    OkWith (StartGood n) (perform o w startExh k) := by
  apply perform_ind
  · intro w' hw'
    exact startExh_good (by simp [hw', ho, hw])
  · intro r w' hw'
    exact hk r w' (by simp [hw', ho, hw])

theorem createArray_good {n : Nat} {c : JSVal} {len : Option Nat} {w : W} (hw : cnt w.tr = n)
    {k : JSVal → W → Outcome Start}
    (hk : ∀ a w', a.isReceiver = true → cnt w'.tr = n → OkWith (StartGood n) (k a w')) :
    OkWith (StartGood n) (createArray c len w k) := by
  unfold createArray
  split
  · refine perform_start rfl hw ?_
    intro r w' hw'
    cases r with
    | err e => exact startReject_good hw' e
    | ok a => exact hk _ _ (toReceiver_isReceiver a) hw'
  · refine perform_start rfl hw ?_
    intro r w' hw'
    cases r with
    | err e => exact startReject_good hw' e
    | ok a => exact hk _ _ (toReceiver_isReceiver a) hw'

theorem getIterator_good {n : Nat} {items m : JSVal} {w : W} (hw : cnt w.tr = n)
    {k : JSVal → JSVal → W → Outcome Start}
    (hk : ∀ it nx w', it.isReceiver = true → cnt w'.tr = n → OkWith (StartGood n) (k it nx w')) :
    OkWith (StartGood n) (getIterator items m w k) := by
  unfold getIterator
  refine perform_start rfl hw ?_
  intro r w' hw'
  cases r with
  | err e => exact startReject_good hw' e
  | ok it =>
    simp only
    split
    · rename_i hit
      refine perform_start rfl hw' ?_
      intro r w'' hw''
      cases r with
      | err e => exact startReject_good hw'' e
      | ok nx => exact hk _ _ _ hit hw''
    · exact startReject_good hw' _

theorem startIter_good (smiMax : Nat) {inp : Input} (hm : MapfnOK inp.mapfn) {it nx arr : JSVal}
    (hit : it.isReceiver = true) (harr : arr.isReceiver = true) {n : Nat} {w : W}
    (hw : cnt w.tr = n) : OkWith (StartGood n) (startIter smiMax inp it nx arr w) := by
  have hc : IterInv (initIterCtx inp it nx arr) :=
    ⟨⟨.getIteratorStep, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, harr, hit, hm⟩
  unfold startIter
  refine (iterBody_good smiMax hc w).map ?_
  intro a h
  rw [hw] at h
  exact h

theorem numberOf_isNumber (smiMax n : Nat) : (numberOf smiMax n).isNumber = true := by
  unfold numberOf
  split <;> rfl

theorem startAL_good (smiMax : Nat) {inp : Input} (hm : MapfnOK inp.mapfn) {al arr : JSVal}
    {len : Nat} (hal : al.isReceiver = true) (harr : arr.isReceiver = true) {n : Nat} {w : W}
    (hw : cnt w.tr = n) : OkWith (StartGood n) (startAL smiMax inp al len arr w) := by
  have hc : ALInv (initALCtx smiMax inp al len arr) :=
    ⟨⟨.getArrayLikeValue, rfl, rfl⟩, numberOf_isNumber smiMax len, rfl, rfl, rfl, rfl, rfl, harr,
      hal, hm⟩
  unfold startAL
  refine (alBody_good smiMax hc w).map ?_
  intro a h
  rw [hw] at h
  exact h

theorem mapfnOK_of {f : JSVal} (h : ¬(f ≠ .undef ∧ f.isCallable = false)) : MapfnOK f := by
  by_cases hu : f = .undef
  · exact Or.inl hu
  · right
    cases hf : f.isCallable
    · exact absurd ⟨hu, hf⟩ h
    · rfl

theorem arrayFromAsync_good (smiMax : Nat) (inp : Input) (w : W) :
    OkWith (StartGood (cnt w.tr)) (arrayFromAsync smiMax inp w) := by
  unfold arrayFromAsync
  split
  · exact startReject_good rfl _
  · rename_i hmap
    have hm := mapfnOK_of hmap
    refine perform_start rfl rfl ?_
    intro r w1 h1
    cases r with
    | err e => exact startReject_good h1 e
    | ok m =>
      simp only
      split
      · refine perform_start rfl h1 ?_
        intro r w2 h2
        cases r with
        | err e => exact startReject_good h2 e
        | ok m' =>
          simp only
          split
          · refine perform_start rfl h2 ?_
            intro r w3 h3
            cases r with
            | err e => exact startReject_good h3 e
            | ok lv =>
              refine createArray_good h3 ?_
              intro arr w4 harr h4
              exact startAL_good smiMax hm (toReceiver_isReceiver _) harr h4
          · split
            · refine getIterator_good h2 ?_
              intro it nx w3 hit h3
              refine perform_start rfl h3 ?_
              intro r w4 h4
              cases r with
              | err e => exact startReject_good h4 e
              | ok _ =>
                refine createArray_good h4 ?_
                intro arr w5 harr h5
                exact startIter_good smiMax hm rfl harr h5
            · exact startReject_good h2 _
      · split
        · refine getIterator_good h1 ?_
          intro it nx w2 hit h2
          refine createArray_good h2 ?_
          intro arr w3 harr h3
          exact startIter_good smiMax hm hit harr h3
        · exact startReject_good h1 _

theorem reactAll_good (smiMax : Nat) :
    ∀ (c : Ctx) (evs : List Event) (w : W), CtxInv c →
      OkWith (fun r => CtxInv r.1) (reactAll smiMax c evs w)
  | c, [], w, hc => OkWith.ok hc
  | c, e :: es, w, hc => by
    unfold reactAll
    exact (react_good smiMax hc e w).bind fun r h => reactAll_good smiMax r.2.1 es r.2.2 h.1

theorem runEvents_safe (smiMax : Nat) (inp : Input) (evs : List Event) (rs : List Resp) :
    ∃ tr, runEvents smiMax inp evs rs = .ok tr := by
  unfold runEvents
  obtain ⟨st, hst, hg⟩ := arrayFromAsync_good smiMax inp ⟨rs, []⟩
  rw [hst, obind_ok]
  cases st with
  | withCtx x c w =>
    obtain ⟨r, hr, _⟩ := reactAll_good smiMax c evs w hg.1
    simp only
    rw [hr, omap_ok]
    exact ⟨_, rfl⟩
  | noCtx x w => exact ⟨_, rfl⟩

theorem runEvents_ne_ub_fatal (smiMax : Nat) (inp : Input) (evs : List Event) (rs : List Resp) :
    runEvents smiMax inp evs rs ≠ .ub ∧ runEvents smiMax inp evs rs ≠ .fatal := by
  obtain ⟨tr, h⟩ := runEvents_safe smiMax inp evs rs
  rw [h]
  exact ⟨nofun, nofun⟩

def settleBit (e : End) : Nat := if e = .settled then 1 else 0

theorem drive_good (smiMax : Nat) :
    ∀ (n : Nat) (c : Ctx) (w : W), CtxInv c → cnt w.tr = 0 →
      OkWith (fun r => cnt r.2.tr = settleBit r.1) (drive smiMax n c w)
  | 0, c, w, _, hw => OkWith.ok (by simp [hw, settleBit])
  | n + 1, c, w, hc, hw => by
    unfold drive
    split
    · exact OkWith.ok (by simp [hw, settleBit])
    · rename_i r rs _
      refine (react_good smiMax hc (Event.ofResp r) ⟨rs, w.tr⟩).bind ?_
      intro res h
      obtain ⟨x, c', w'⟩ := res
      obtain ⟨hc', hw'⟩ := h
      simp only at hc' hw' ⊢
      cases x with
      | suspended => exact drive_good smiMax n c' w' hc' (by simp [hw', hw, bit])
      | settled => exact OkWith.ok (by simp [hw', hw, bit, settleBit, Exit.toEnd])
      | idle => exact OkWith.ok (by simp [hw', hw, bit, settleBit, Exit.toEnd])
      | exhausted => exact OkWith.ok (by simp [hw', hw, bit, settleBit, Exit.toEnd])

theorem run_good (smiMax fuel : Nat) (inp : Input) (rs : List Resp) :
    OkWith (fun r => r.1.countP Op.isSettle = settleBit r.2) (run smiMax fuel inp rs) := by
  unfold run
  refine (arrayFromAsync_good smiMax inp ⟨rs, []⟩).bind ?_
  intro st h
  cases st with
  | withCtx x c w =>
    cases x with
    | suspended =>
      simp only
      refine (drive_good smiMax fuel c w h.1 (by simpa [bit, cnt] using h.2)).map ?_
      intro r hr
      simpa [List.countP_reverse, cnt] using hr
    | settled => exact OkWith.ok (by simpa [List.countP_reverse, cnt, bit, settleBit, Exit.toEnd] using h.2)
    | idle => exact OkWith.ok (by simpa [List.countP_reverse, cnt, bit, settleBit, Exit.toEnd] using h.2)
    | exhausted => exact OkWith.ok (by simpa [List.countP_reverse, cnt, bit, settleBit, Exit.toEnd] using h.2)
  | noCtx x w =>
    cases x with
    | suspended => exact absurd rfl h.1
    | settled => exact OkWith.ok (by simpa [List.countP_reverse, cnt, bit, settleBit, Exit.toEnd] using h.2)
    | idle => exact OkWith.ok (by simpa [List.countP_reverse, cnt, bit, settleBit, Exit.toEnd] using h.2)
    | exhausted => exact OkWith.ok (by simpa [List.countP_reverse, cnt, bit, settleBit, Exit.toEnd] using h.2)

theorem run_safe (smiMax fuel : Nat) (inp : Input) (rs : List Resp) :
    ∃ r, run smiMax fuel inp rs = .ok r := by
  obtain ⟨r, h, _⟩ := run_good smiMax fuel inp rs
  exact ⟨r, h⟩

theorem run_settles_at_most_once {smiMax fuel : Nat} {inp : Input} {rs : List Resp}
    {tr : List Op} {e : End} (h : run smiMax fuel inp rs = .ok (tr, e)) :
    tr.countP Op.isSettle = if e = .settled then 1 else 0 := by
  obtain ⟨r, hr, hg⟩ := run_good smiMax fuel inp rs
  rw [h] at hr
  cases hr
  exact hg

theorem run_settle_le_one {smiMax fuel : Nat} {inp : Input} {rs : List Resp} {tr : List Op}
    {e : End} (h : run smiMax fuel inp rs = .ok (tr, e)) : tr.countP Op.isSettle ≤ 1 := by
  rw [run_settles_at_most_once h]
  split <;> omega

end ArrayFromAsync
