import ArrayFromAsync.Spec
import ArrayFromAsync.Safety

namespace ArrayFromAsync

open Torque

def Agrees {α : Type} (P : α → SRes → Prop) (v : Outcome α) (s : SRes) : Prop :=
  s.devs = [] → ∃ a, v = .ok a ∧ P a s

theorem Agrees.dev {α : Type} {P : α → SRes → Prop} {v : Outcome α} (d : Dev) (s : SRes) :
    Agrees P v (s.dev d) := by
  intro h
  simp [SRes.dev] at h

theorem Agrees.ok {α : Type} {P : α → SRes → Prop} {a : α} {s : SRes} (h : P a s) :
    Agrees P (.ok a) s := fun _ => ⟨a, rfl, h⟩

theorem Agrees.perform {α : Type} {P : α → SRes → Prop} {o : Op} {w : W}
    {e1 : W → Outcome α} {k1 : Resp → W → Outcome α} {e2 : W → SRes} {k2 : Resp → W → SRes}
    (h1 : ∀ w', Agrees P (e1 w') (e2 w')) (h2 : ∀ r w', Agrees P (k1 r w') (k2 r w')) :
    Agrees P (ArrayFromAsync.perform o w e1 k1) (ArrayFromAsync.perform o w e2 k2) := by
  unfold ArrayFromAsync.perform
  split
  · exact h1 _
  · exact h2 _ _

theorem Agrees.chk {α : Type} {P : α → SRes → Prop} {t : Ty} {v : JSVal}
    {k : JSVal → Outcome α} {s : SRes} (h : t.holds v = true) (hk : Agrees P (k v) s) :
    Agrees P (ArrayFromAsync.chk t v k) s := by
  rw [chk_true h]
  exact hk

theorem Agrees.bind {α β : Type} {Q : α → SRes → Prop} {P : β → SRes → Prop} {v : Outcome α}
    {f : α → Outcome β} {s : SRes} (h : Agrees Q v s)
    (hf : ∀ a, Q a s → Agrees P (f a) s) : Agrees P (obind v f) s := by
  intro hd
  obtain ⟨a, rfl, ha⟩ := h hd
  exact hf a ha hd

theorem Agrees.map {α β : Type} {Q : α → SRes → Prop} {P : β → SRes → Prop} {v : Outcome α}
    {f : α → β} {s : SRes} (h : Agrees Q v s) (hf : ∀ a, Q a s → P (f a) s) :
    Agrees P (omap f v) s :=
  h.bind fun a ha => Agrees.ok (hf a ha)

theorem omap_perform {α β : Type} (f : α → β) (o : Op) (w : W) (e : W → Outcome α)
    (k : Resp → W → Outcome α) :
    omap f (perform o w e k) = perform o w (fun w => omap f (e w)) (fun r w => omap f (k r w)) := by
  unfold perform
  split <;> rfl

structure IterRel (E : IterRec) (c : IterCtx) : Prop where
  promise : c.promise.isPromise = true
  promiseFunction : c.promiseFunction = .promiseCtor
  onFulfilled : c.onFulfilled.isFunctionOrUndefined = true
  onRejected : c.onRejected.isFunctionOrUndefined = true
  resultArray : c.resultArray = E.A
  arr : E.A.isReceiver = true
  iterator : c.iterator = E.iterator
  iteratorRecv : E.iterator.isReceiver = true
  nextMethod : c.nextMethod = E.next
  mapfn : c.mapfn = E.mapfn
  mapfnOK : MapfnOK E.mapfn
  thisArg : c.thisArg = E.thisArg
  index : c.index.isSmi = true

structure ALRel (smiMax : Nat) (E : ALRec) (c : ALCtx) : Prop where
  promise : c.promise.isPromise = true
  promiseFunction : c.promiseFunction = .promiseCtor
  onFulfilled : c.onFulfilled.isFunctionOrUndefined = true
  onRejected : c.onRejected.isFunctionOrUndefined = true
  resultArray : c.resultArray = E.A
  arr : E.A.isReceiver = true
  arrayLike : c.arrayLike = E.arrayLike
  arrayLikeRecv : E.arrayLike.isReceiver = true
  len : c.len = numberOf smiMax E.len
  mapfn : c.mapfn = E.mapfn
  mapfnOK : MapfnOK E.mapfn
  thisArg : c.thisArg = E.thisArg
  index : c.index.isSmi = true

def SuspRel (smiMax : Nat) : Ctx → Susp → Prop
  | .iter c, .iterNext E k =>
    IterRel E c ∧ c.step = .smi Label.checkIteratorValueAndMapping.code ∧ c.index = .smi k ∧
      k ≤ smiMax
  | .iter c, .iterMapped E k =>
    IterRel E c ∧ c.step = .smi Label.getIteratorValueWithMapping.code ∧ c.index = .smi k ∧
      k ≤ smiMax
  | .iter c, .iterClose E e => IterRel E c ∧ c.step = .smi Label.rejectPromise.code ∧ c.error = e
  | .arrayLike c, .alValue E k =>
    ALRel smiMax E c ∧ c.step = .smi Label.checkArrayLikeValueAndMapping.code ∧ c.index = .smi k ∧
      k < E.len
  | .arrayLike c, .alMapped E k =>
    ALRel smiMax E c ∧ c.step = .smi Label.addArrayLikeValueToTheArray.code ∧ c.index = .smi k ∧
      k < E.len
  | _, _ => False

def ExitRel (smiMax : Nat) (x : Exit) (c : Ctx) (w : W) (s : SRes) : Prop :=
  s.w = w ∧
    match x with
    | .suspended => ∃ st, s.out = .susp st ∧ SuspRel smiMax c st
    | .settled => s.out = .stop .settled
    | .exhausted => s.out = .stop .exhausted
    | .idle => False

def IterLoopRel (smiMax : Nat) (E : IterRec) : Res IterCtx → SRes → Prop
  | .exit x c w, s => ExitRel smiMax x (.iter c) w s
  | .thrown e c w, s => s = asyncIteratorClose E e w ∧ IterRel E c

def ALLoopRel (smiMax : Nat) (E : ALRec) : Res ALCtx → SRes → Prop
  | .exit x c w, s => ExitRel smiMax x (.arrayLike c) w s
  | .thrown e c w, s => s = sReject e w ∧ ALRel smiMax E c

def IterBodyRel (smiMax : Nat) (r : Exit × IterCtx × W) (s : SRes) : Prop :=
  ExitRel smiMax r.1 (.iter r.2.1) r.2.2 s

def ALBodyRel (smiMax : Nat) (r : Exit × ALCtx × W) (s : SRes) : Prop :=
  ExitRel smiMax r.1 (.arrayLike r.2.1) r.2.2 s

theorem iterAwaitPoint_eq {c : IterCtx} (hpf : c.promiseFunction = .promiseCtor)
    (hf : c.onFulfilled.isFunctionOrUndefined = true)
    (hr : c.onRejected.isFunctionOrUndefined = true) (l : Label) (v : JSVal) (w : W) :
    iterAwaitPoint c l v w =
      perform (.await v) w (fun w => .ok (.exhausted { c with step := .smi l.code } w))
        (fun r w =>
          match r with
          | .err e => .ok (.thrown e { c with step := .smi l.code } w)
          | .ok _ => .ok (.registered { c with step := .smi l.code } w)) := by
  unfold iterAwaitPoint
  simp only
  rw [chk_true (by simp [Ty.holds, hpf, JSVal.isReceiver]), chk_true (by simpa [Ty.holds] using hf),
    chk_true (by simpa [Ty.holds] using hr)]
  congr 1
  funext r w
  cases r with
  | err e => rfl
  | ok _ => rw [chk_true (by simpa [Ty.holds, hpf] using promiseResolve_promise v)]

theorem alAwaitPoint_eq {c : ALCtx} (hpf : c.promiseFunction = .promiseCtor)
    (hf : c.onFulfilled.isFunctionOrUndefined = true)
    (hr : c.onRejected.isFunctionOrUndefined = true) (l : Label) (v : JSVal) (w : W) :
    alAwaitPoint c l v w =
      perform (.await v) w (fun w => .ok (.exhausted { c with step := .smi l.code } w))
        (fun r w =>
          match r with
          | .err e => .ok (.thrown e { c with step := .smi l.code } w)
          | .ok _ => .ok (.registered { c with step := .smi l.code } w)) := by
  unfold alAwaitPoint
  simp only
  rw [chk_true (by simp [Ty.holds, hpf, JSVal.isReceiver]), chk_true (by simpa [Ty.holds] using hf),
    chk_true (by simpa [Ty.holds] using hr)]
  congr 1
  funext r w
  cases r with
  | err e => rfl
  | ok _ => rw [chk_true (by simpa [Ty.holds, hpf] using promiseResolve_promise v)]

def CloseRel (E : IterRec) (e : JSVal) : CloseRes IterCtx → SRes → Prop
  | .normal true c w, s =>
    s.w = w ∧ s.out = .susp (.iterClose E e) ∧ IterRel E c ∧ c.step = .smi Label.rejectPromise.code ∧
      c.error = e
  | .normal false _ _, _ => False
  | .rejectPromise c w, s => s = sReject e w ∧ IterRel E c ∧ c.error = e
  | .exhausted _ w, s => s.w = w ∧ s.out = .stop .exhausted

theorem iterClose_agree {E : IterRec} {c : IterCtx} (hc : IterRel E c) {e : JSVal} (he : c.error = e)
    {it : JSVal} (hit : it = E.iterator) (w : W) :
    Agrees (CloseRel E e) (iterClose c it w) (asyncIteratorClose E e w) := by
  subst hit
  unfold iterClose asyncIteratorClose
  apply Agrees.perform
  · intro w'
    exact Agrees.ok ⟨rfl, rfl⟩
  · intro r w'
    cases r with
    | err _ => exact Agrees.dev _ _
    | ok m =>
      simp only
      split
      · exact Agrees.ok ⟨rfl, hc, he⟩
      split
      · apply Agrees.perform
        · intro w''
          exact Agrees.ok ⟨rfl, rfl⟩
        · intro r w''
          cases r with
          | err _ => exact Agrees.dev _ _
          | ok ir =>
            simp only
            rw [iterAwaitPoint_eq hc.promiseFunction hc.onFulfilled hc.onRejected, omap_perform]
            apply Agrees.perform
            · intro w'''
              exact Agrees.ok ⟨rfl, rfl⟩
            · intro r w'''
              cases r with
              | err _ => exact Agrees.dev _ _
              | ok _ => exact Agrees.ok ⟨rfl, rfl, { hc with }, rfl, he⟩
      · exact Agrees.dev _ _

theorem iterHead_agree (smiMax : Nat) (hsmi : smiMax < 2 ^ 53 - 1) {E : IterRec} {c : IterCtx}
    (hc : IterRel E c) {k : Nat} (hidx : c.index = .smi k) (hk : k ≤ smiMax) (fuel : Nat)
    (av mv nv : JSVal) (w : W) :
    Agrees (IterLoopRel smiMax E)
      (iterLoop smiMax E.mapfn E.thisArg E.A (fuel + 1) ⟨some .getIteratorStep, av, k, mv, nv⟩ c w)
      (iterHead E k w) := by
  have hk' : ¬(2 ^ 53 - 1 ≤ k) := by omega
  rw [iterLoop]
  simp only
  unfold iterHead
  rw [ite_eq_right hk']
  refine Agrees.chk (by simpa [Ty.holds, hc.iterator] using hc.iteratorRecv) ?_
  refine Agrees.chk rfl ?_
  rw [hc.nextMethod, hc.iterator]
  by_cases hn : E.next.isCallable = true
  · rw [ite_eq_left hn, ite_eq_left hn]
    apply Agrees.perform
    · intro w'
      exact Agrees.ok ⟨rfl, rfl⟩
    · intro r w'
      cases r with
      | err e => exact Agrees.dev _ _
      | ok v =>
        simp only
        rw [iterAwaitPoint_eq hc.promiseFunction hc.onFulfilled hc.onRejected, omap_perform]
        apply Agrees.perform
        · intro w''
          exact Agrees.ok ⟨rfl, rfl⟩
        · intro r w''
          cases r with
          | err e => exact Agrees.dev _ _
          | ok _ => exact Agrees.ok ⟨rfl, _, rfl, { hc with }, rfl, hidx, hk⟩
  · rw [ite_eq_right hn, ite_eq_right hn]
    exact Agrees.dev _ _

theorem smiInc_of_ne {smiMax k : Nat} (h : k ≠ smiMax) :
    smiInc smiMax (k : Int) = ((k + 1 : Nat) : Int) := by
  unfold smiInc
  rw [ite_eq_right (by omega)]
  omega

theorem iterDefine_agree (smiMax : Nat) (hsmi : smiMax < 2 ^ 53 - 1) {E : IterRec} {c : IterCtx}
    (hc : IterRel E c) {k : Nat} (hk : k ≤ smiMax) (fuel : Nat) (av v nv : JSVal) (w : W) :
    Agrees (IterLoopRel smiMax E)
      (iterLoop smiMax E.mapfn E.thisArg E.A (fuel + 2) ⟨some .addIteratorValueToTheArray, av, k, v, nv⟩ c w)
      (iterDefine smiMax E k v w) := by
  rw [iterLoop]
  simp only
  unfold iterDefine
  apply Agrees.perform
  · intro w1
    exact Agrees.ok ⟨rfl, rfl⟩
  · intro r w1
    cases r with
    | err e => exact Agrees.ok ⟨rfl, hc⟩
    | ok _ =>
      simp only
      by_cases hks : k = smiMax
      · rw [ite_eq_left hks]
        exact Agrees.dev _ _
      · rw [ite_eq_right hks, smiInc_of_ne hks]
        exact iterHead_agree (c := { c with index := .smi ((k + 1 : Nat) : Int) }) smiMax hsmi
          { hc with index := rfl } rfl (by omega) fuel _ _ _ w1

theorem mapfn_callable {f : JSVal} (h : MapfnOK f) (hne : ¬f = .undef) : f.isCallable = true := by
  rcases h with h | h
  · exact absurd h hne
  · exact h

theorem iterAfterNext_agree (smiMax : Nat) (hsmi : smiMax < 2 ^ 53 - 1) {E : IterRec} {c : IterCtx}
    (hc : IterRel E c) {k : Nat} (hidx : c.index = .smi k) (hk : k ≤ smiMax) (fuel : Nat)
    (v mv nv : JSVal) (w : W) :
    Agrees (IterLoopRel smiMax E)
      (iterLoop smiMax E.mapfn E.thisArg E.A (fuel + 3) ⟨some .checkIteratorValueAndMapping, v, k, mv, nv⟩ c w)
      (iterAfterNext smiMax E k v w) := by
  rw [iterLoop]
  simp only
  unfold iterAfterNext
  by_cases hv : v.isReceiver = true
  · rw [ite_eq_left hv, ite_eq_left hv]
    apply Agrees.perform
    · intro w1
      exact Agrees.ok ⟨rfl, rfl⟩
    · intro r w1
      cases r with
      | err e => exact Agrees.dev _ _
      | ok d =>
        simp only
        by_cases hd : d.truthy = true
        · rw [ite_eq_left hd, ite_eq_left hd, iterLoop]
          simp only
          apply Agrees.perform
          · intro w2
            exact Agrees.ok ⟨rfl, rfl⟩
          · intro r w2
            cases r with
            | err e => exact Agrees.dev _ _
            | ok _ =>
              simp only
              refine Agrees.chk (by simpa [Ty.holds] using hc.promise) ?_
              exact Agrees.ok ⟨rfl, rfl⟩
        · rw [ite_eq_right hd, ite_eq_right hd]
          apply Agrees.perform
          · intro w2
            exact Agrees.ok ⟨rfl, rfl⟩
          · intro r w2
            cases r with
            | err e => exact Agrees.dev _ _
            | ok x =>
              simp only
              by_cases hm : E.mapfn = .undef
              · rw [ite_eq_left hm, ite_eq_left hm]
                exact iterDefine_agree smiMax hsmi hc hk fuel _ _ _ w2
              · rw [ite_eq_right hm, ite_eq_right hm, iterLoop]
                simp only
                refine Agrees.chk (by simpa [Ty.holds] using mapfn_callable hc.mapfnOK hm) ?_
                apply Agrees.perform
                · intro w3
                  exact Agrees.ok ⟨rfl, rfl⟩
                · intro r w3
                  cases r with
                  | err e => exact Agrees.ok ⟨rfl, hc⟩
                  | ok m =>
                    simp only
                    rw [iterAwaitPoint_eq hc.promiseFunction hc.onFulfilled hc.onRejected, omap_perform]
                    apply Agrees.perform
                    · intro w4
                      exact Agrees.ok ⟨rfl, rfl⟩
                    · intro r w4
                      cases r with
                      | err e => exact Agrees.ok ⟨rfl, { hc with }⟩
                      | ok _ => exact Agrees.ok ⟨rfl, _, rfl, { hc with }, rfl, hidx, hk⟩
  · rw [ite_eq_right hv, ite_eq_right hv]
    exact Agrees.dev _ _

theorem iterCloseStep_agree (smiMax : Nat) {E : IterRec} {c : IterCtx} (hc : IterRel E c) {e : JSVal}
    (he : c.error = e) (fuel : Nat) (av : JSVal) (ix : Int) (mv nv : JSVal) (w : W) :
    Agrees (IterLoopRel smiMax E)
      (iterLoop smiMax E.mapfn E.thisArg E.A (fuel + 2) ⟨some .closeAsyncIterator, av, ix, mv, nv⟩ c w)
      (asyncIteratorClose E e w) := by
  rw [iterLoop]
  simp only
  refine Agrees.chk (by simpa [Ty.holds, hc.iterator] using hc.iteratorRecv) ?_
  refine Agrees.chk rfl ?_
  refine (iterClose_agree hc he hc.iterator w).bind ?_
  intro a ha
  cases a with
  | normal reg c' w' =>
    cases reg with
    | true =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := ha
      exact Agrees.ok ⟨h1, _, h2, h3, h4, h5⟩
    | false => exact absurd ha id
  | rejectPromise c' w' =>
    obtain ⟨hs, h1, h2⟩ := ha
    simp only
    rw [iterLoop]
    simp only
    refine Agrees.chk rfl ?_
    refine Agrees.chk (by simpa [Ty.holds] using h1.promise) ?_
    rw [hs, h2]
    exact Agrees.ok ⟨rfl, rfl⟩
  | exhausted c' w' => exact Agrees.ok ha

theorem iterCatch_agree (smiMax : Nat) {E : IterRec} {c : IterCtx} (hc : IterRel E c) (e : JSVal)
    (w : W) : Agrees (IterBodyRel smiMax) (iterCatch c e w) (asyncIteratorClose E e w) := by
  have hc' : IterRel E { c with error := e } := { hc with }
  unfold iterCatch
  simp only
  refine Agrees.chk (by simpa [Ty.holds, hc.iterator] using hc.iteratorRecv) ?_
  refine Agrees.chk rfl ?_
  refine (iterClose_agree (e := e) hc' rfl hc.iterator w).bind ?_
  intro a ha
  cases a with
  | normal reg c' w' =>
    cases reg with
    | true =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := ha
      exact Agrees.ok ⟨h1, _, h2, h3, h4, h5⟩
    | false => exact absurd ha id
  | rejectPromise c' w' =>
    obtain ⟨hs, h1, h2⟩ := ha
    unfold iterRejectFromSlots
    refine Agrees.chk rfl ?_
    refine Agrees.chk (by simpa [Ty.holds] using h1.promise) ?_
    rw [hs, h2]
    exact Agrees.ok ⟨rfl, rfl⟩
  | exhausted c' w' => exact Agrees.ok ha

theorem iterHandler_agree (smiMax : Nat) {E : IterRec} {v : Outcome (Res IterCtx)} {s : SRes}
    (h : Agrees (IterLoopRel smiMax E) v s) : Agrees (IterBodyRel smiMax) (obind v iterHandler) s := by
  refine h.bind ?_
  intro a ha
  cases a with
  | exit x c w => exact Agrees.ok ha
  | thrown e c w =>
    rw [ha.1]
    exact iterCatch_agree smiMax ha.2 e w

theorem iterTry_eq (smiMax : Nat) {E : IterRec} {c : IterCtx} (hc : IterRel E c) {l : Label}
    (hl : c.step = .smi l.code) {i : Int} (hi : c.index = .smi i) (w : W) :
    iterTry smiMax c w =
      iterLoop smiMax E.mapfn E.thisArg E.A 8 ⟨some l, c.awaitedValue, i, .undef, .undef⟩ c w := by
  unfold iterTry
  rw [chk_any, chk_any, chk_true (by simpa [Ty.holds, hc.resultArray] using hc.arr),
    chk_true (by simp [Ty.holds, hl, JSVal.isSmi]), chk_any,
    chk_true (by simp [Ty.holds, hi, JSVal.isSmi])]
  simp [hl, hi, JSVal.num, Label.decode_code, hc.mapfn, hc.thisArg, hc.resultArray]

def CtxBodyRel (smiMax : Nat) (r : Exit × Ctx × W) (s : SRes) : Prop :=
  ExitRel smiMax r.1 r.2.1 r.2.2 s

theorem index_smi {v : JSVal} (h : v.isSmi = true) : ∃ i, v = .smi i := by
  cases v <;> simp_all [JSVal.isSmi]

theorem iterReact_agree (smiMax : Nat) (hsmi : smiMax < 2 ^ 53 - 1) {c : IterCtx} {st : Susp}
    (hr : SuspRel smiMax (.iter c) st) (r : Resp) (w : W) :
    Agrees (CtxBodyRel smiMax) (react smiMax (.iter c) (Event.ofResp r) w) (resume smiMax st r w) := by
  cases st with
  | iterNext E k =>
    obtain ⟨hc, hstep, hidx, hk⟩ := hr
    cases r with
    | ok v =>
      simp only [react, Event.ofResp, resume, iterOnFulfilled, iterBody]
      have hc' : IterRel E { c with awaitedValue := v } := { hc with }
      rw [iterTry_eq smiMax hc' hstep hidx]
      exact Agrees.map
        (iterHandler_agree smiMax (iterAfterNext_agree smiMax hsmi hc' hidx hk 5 v .undef .undef w))
        fun a ha => ha
    | err e => exact Agrees.dev _ _
  | iterMapped E k =>
    obtain ⟨hc, hstep, hidx, hk⟩ := hr
    cases r with
    | ok m =>
      simp only [react, Event.ofResp, resume, iterOnFulfilled, iterBody]
      have hc' : IterRel E { c with awaitedValue := m } := { hc with }
      rw [iterTry_eq smiMax hc' hstep hidx, iterLoop]
      simp only
      exact Agrees.map (iterHandler_agree smiMax (iterDefine_agree smiMax hsmi hc' hk 5 m m .undef w))
        fun a ha => ha
    | err e =>
      simp only [react, Event.ofResp, resume, iterOnRejected, iterBody]
      have hc' : IterRel E { c with step := .smi Label.closeAsyncIterator.code, error := e } :=
        { hc with }
      rw [iterTry_eq smiMax hc' rfl hidx]
      exact Agrees.map
        (iterHandler_agree smiMax (iterCloseStep_agree smiMax hc' rfl 6 c.awaitedValue k .undef .undef w))
        fun a ha => ha
  | iterClose E e =>
    obtain ⟨hc, hstep, herr⟩ := hr
    obtain ⟨i, hi⟩ := index_smi hc.index
    cases r with
    | ok v =>
      simp only [react, Event.ofResp, resume, iterOnFulfilled, iterBody]
      have hc' : IterRel E { c with awaitedValue := v } := { hc with }
      rw [iterTry_eq smiMax hc' hstep hi, iterLoop]
      simp only
      refine Agrees.map (iterHandler_agree (E := E) smiMax ?_) fun a ha => ha
      refine Agrees.chk rfl ?_
      refine Agrees.chk (by simpa [Ty.holds] using hc.promise) ?_
      rw [herr]
      exact Agrees.ok ⟨rfl, rfl⟩
    | err e' => exact Agrees.dev _ _
  | alValue E k => exact absurd hr id
  | alMapped E k => exact absurd hr id

theorem numberOf_num (smiMax n : Nat) : (numberOf smiMax n).num = n := by
  unfold numberOf
  split <;> rfl

theorem alHead_agree (smiMax : Nat) {E : ALRec} {c : ALCtx} (hc : ALRel smiMax E c) {k : Nat}
    (hidx : c.index = .smi k) (hk : k ≤ E.len) (fuel : Nat) (av : JSVal) (w : W) :
    Agrees (ALLoopRel smiMax E)
      (alLoop smiMax E.mapfn E.thisArg E.A (fuel + 2) ⟨some .getArrayLikeValue, av, numberOf smiMax E.len, k⟩ c w)
      (alHead E k w) := by
  rw [alLoop]
  simp only
  unfold alHead
  refine Agrees.chk (by simpa [Ty.holds, hc.arrayLike] using hc.arrayLikeRecv) ?_
  rw [hc.arrayLike, numberOf_num]
  by_cases hlt : k < E.len
  · rw [ite_eq_left (by omega : (k : Int) < (E.len : Int)), ite_eq_left hlt]
    apply Agrees.perform
    · intro w1
      exact Agrees.ok ⟨rfl, rfl⟩
    · intro r w1
      cases r with
      | err e => exact Agrees.ok ⟨rfl, hc⟩
      | ok v =>
        simp only
        rw [alAwaitPoint_eq hc.promiseFunction hc.onFulfilled hc.onRejected, omap_perform]
        apply Agrees.perform
        · intro w2
          exact Agrees.ok ⟨rfl, rfl⟩
        · intro r w2
          cases r with
          | err e => exact Agrees.ok ⟨rfl, { hc with }⟩
          | ok _ => exact Agrees.ok ⟨rfl, _, rfl, { hc with }, rfl, hidx, hlt⟩
  · rw [ite_eq_right (by omega : ¬(k : Int) < (E.len : Int)), ite_eq_right hlt, alLoop]
    simp only
    have hkl : k = E.len := by omega
    rw [hkl]
    apply Agrees.perform
    · intro w1
      exact Agrees.ok ⟨rfl, rfl⟩
    · intro r w1
      cases r with
      | err e => exact Agrees.ok ⟨rfl, hc⟩
      | ok _ =>
        simp only
        refine Agrees.chk (by simpa [Ty.holds] using hc.promise) ?_
        exact Agrees.ok ⟨rfl, rfl⟩

theorem alDefine_agree (smiMax : Nat) {E : ALRec} {c : ALCtx} (hc : ALRel smiMax E c) {k : Nat}
    (hk : k < E.len) (fuel : Nat) (v : JSVal) (w : W) :
    Agrees (ALLoopRel smiMax E)
      (alLoop smiMax E.mapfn E.thisArg E.A (fuel + 3) ⟨some .addArrayLikeValueToTheArray, v, numberOf smiMax E.len, k⟩ c w)
      (alDefine smiMax E k v w) := by
  rw [alLoop]
  simp only
  unfold alDefine
  apply Agrees.perform
  · intro w1
    exact Agrees.ok ⟨rfl, rfl⟩
  · intro r w1
    cases r with
    | err e => exact Agrees.ok ⟨rfl, hc⟩
    | ok _ =>
      simp only
      by_cases hks : k = smiMax
      · rw [ite_eq_left hks]
        exact Agrees.dev _ _
      · rw [ite_eq_right hks, smiInc_of_ne hks]
        exact alHead_agree (c := { c with index := .smi ((k + 1 : Nat) : Int) }) smiMax
          { hc with index := rfl } rfl (by omega) fuel _ w1

theorem alAfterValue_agree (smiMax : Nat) {E : ALRec} {c : ALCtx} (hc : ALRel smiMax E c) {k : Nat}
    (hidx : c.index = .smi k) (hk : k < E.len) (fuel : Nat) (v : JSVal) (w : W) :
    Agrees (ALLoopRel smiMax E)
      (alLoop smiMax E.mapfn E.thisArg E.A (fuel + 4) ⟨some .checkArrayLikeValueAndMapping, v, numberOf smiMax E.len, k⟩ c w)
      (alAfterValue smiMax E k v w) := by
  rw [alLoop]
  simp only
  unfold alAfterValue
  by_cases hm : E.mapfn = .undef
  · rw [ite_eq_left hm, ite_eq_left hm]
    exact alDefine_agree smiMax hc hk fuel v w
  · rw [ite_eq_right hm, ite_eq_right hm, alLoop]
    simp only
    refine Agrees.chk (by simpa [Ty.holds] using mapfn_callable hc.mapfnOK hm) ?_
    apply Agrees.perform
    · intro w1
      exact Agrees.ok ⟨rfl, rfl⟩
    · intro r w1
      cases r with
      | err e => exact Agrees.ok ⟨rfl, hc⟩
      | ok m =>
        simp only
        rw [alAwaitPoint_eq hc.promiseFunction hc.onFulfilled hc.onRejected, omap_perform]
        apply Agrees.perform
        · intro w2
          exact Agrees.ok ⟨rfl, rfl⟩
        · intro r w2
          cases r with
          | err e => exact Agrees.ok ⟨rfl, { hc with }⟩
          | ok _ => exact Agrees.ok ⟨rfl, _, rfl, { hc with }, rfl, hidx, hk⟩

theorem alHandler_agree (smiMax : Nat) {E : ALRec} {v : Outcome (Res ALCtx)} {s : SRes}
    (h : Agrees (ALLoopRel smiMax E) v s) : Agrees (ALBodyRel smiMax) (obind v alHandler) s := by
  refine h.bind ?_
  intro a ha
  cases a with
  | exit x c w => exact Agrees.ok ha
  | thrown e c w =>
    obtain ⟨hs, hc⟩ := ha
    rw [hs]
    unfold alHandler alCatch
    simp only
    refine Agrees.chk rfl ?_
    refine Agrees.chk (by simpa [Ty.holds] using hc.promise) ?_
    exact Agrees.ok ⟨rfl, rfl⟩

theorem alTry_eq (smiMax : Nat) {E : ALRec} {c : ALCtx} (hc : ALRel smiMax E c) {l : Label}
    (hl : c.step = .smi l.code) {i : Int} (hi : c.index = .smi i) (w : W) :
    alTry smiMax c w =
      alLoop smiMax E.mapfn E.thisArg E.A 8 ⟨some l, c.awaitedValue, numberOf smiMax E.len, i⟩ c w := by
  unfold alTry
  rw [chk_any, chk_any, chk_true (by simpa [Ty.holds, hc.resultArray] using hc.arr),
    chk_true (by simp [Ty.holds, hl, JSVal.isSmi]), chk_any,
    chk_true (by simpa [Ty.holds, hc.len] using numberOf_isNumber smiMax E.len),
    chk_true (by simp [Ty.holds, hi, JSVal.isSmi])]
  simp [hl, hi, JSVal.num, Label.decode_code, hc.mapfn, hc.thisArg, hc.resultArray, hc.len]

theorem alRejectStep_agree (smiMax : Nat) {E : ALRec} {c : ALCtx} (hc : ALRel smiMax E c) {e : JSVal}
    (he : c.error = e) (fuel : Nat) (av : JSVal) (ix : Int) (w : W) :
    Agrees (ALLoopRel smiMax E)
      (alLoop smiMax E.mapfn E.thisArg E.A (fuel + 1) ⟨some .rejectPromise, av, numberOf smiMax E.len, ix⟩ c w)
      (sReject e w) := by
  rw [alLoop]
  simp only
  refine Agrees.chk rfl ?_
  refine Agrees.chk (by simpa [Ty.holds] using hc.promise) ?_
  rw [he]
  exact Agrees.ok ⟨rfl, rfl⟩

theorem alReact_agree (smiMax : Nat) {c : ALCtx} {st : Susp} (hr : SuspRel smiMax (.arrayLike c) st)
    (r : Resp) (w : W) :
    Agrees (CtxBodyRel smiMax) (react smiMax (.arrayLike c) (Event.ofResp r) w) (resume smiMax st r w) := by
  cases st with
  | alValue E k =>
    obtain ⟨hc, hstep, hidx, hk⟩ := hr
    cases r with
    | ok v =>
      simp only [react, Event.ofResp, resume, alOnFulfilled, alBody]
      have hc' : ALRel smiMax E { c with awaitedValue := v } := { hc with }
      rw [alTry_eq smiMax hc' hstep hidx]
      exact Agrees.map (alHandler_agree smiMax (alAfterValue_agree smiMax hc' hidx hk 4 v w))
        fun a ha => ha
    | err e =>
      simp only [react, Event.ofResp, resume, alOnRejected, alBody]
      have hc' : ALRel smiMax E { c with step := .smi Label.rejectPromise.code, error := e } :=
        { hc with }
      rw [alTry_eq smiMax hc' rfl hidx]
      exact Agrees.map (alHandler_agree smiMax (alRejectStep_agree smiMax hc' rfl 7 c.awaitedValue k w))
        fun a ha => ha
  | alMapped E k =>
    obtain ⟨hc, hstep, hidx, hk⟩ := hr
    cases r with
    | ok m =>
      simp only [react, Event.ofResp, resume, alOnFulfilled, alBody]
      have hc' : ALRel smiMax E { c with awaitedValue := m } := { hc with }
      rw [alTry_eq smiMax hc' hstep hidx]
      exact Agrees.map (alHandler_agree smiMax (alDefine_agree smiMax hc' hk 5 m w)) fun a ha => ha
    | err e =>
      simp only [react, Event.ofResp, resume, alOnRejected, alBody]
      have hc' : ALRel smiMax E { c with step := .smi Label.rejectPromise.code, error := e } :=
        { hc with }
      rw [alTry_eq smiMax hc' rfl hidx]
      exact Agrees.map (alHandler_agree smiMax (alRejectStep_agree smiMax hc' rfl 7 c.awaitedValue k w))
        fun a ha => ha
  | iterNext E k => exact absurd hr id
  | iterMapped E k => exact absurd hr id
  | iterClose E e => exact absurd hr id

theorem react_agree (smiMax : Nat) (hsmi : smiMax < 2 ^ 53 - 1) {c : Ctx} {st : Susp}
    (hr : SuspRel smiMax c st) (r : Resp) (w : W) :
    Agrees (CtxBodyRel smiMax) (react smiMax c (Event.ofResp r) w) (resume smiMax st r w) := by
  cases c with
  | iter c => exact iterReact_agree smiMax hsmi hr r w
  | arrayLike c => exact alReact_agree smiMax hr r w

theorem drive_agree (smiMax : Nat) (hsmi : smiMax < 2 ^ 53 - 1) :
    ∀ (n : Nat) (c : Ctx) (st : Susp) (w : W), SuspRel smiMax c st →
      (specDrive smiMax n st w).2.2 = [] →
        drive smiMax n c w = .ok ((specDrive smiMax n st w).1, (specDrive smiMax n st w).2.1)
  | 0, _, _, _, _, _ => rfl
  | n + 1, c, st, w, hr, hd => by
    obtain ⟨rs, tr⟩ := w
    cases rs with
    | nil => rfl
    | cons r rs =>
      simp only [drive, specDrive] at hd ⊢
      generalize hres : resume smiMax st r ⟨rs, tr⟩ = res at hd ⊢
      have hdevs : res.devs = [] := by
        revert hd
        cases res.out with
        | susp s' => intro hd; exact (List.append_eq_nil_iff.mp hd).1
        | stop x => intro hd; exact hd
      have hag := react_agree smiMax hsmi hr r ⟨rs, tr⟩
      rw [hres] at hag
      obtain ⟨a, ha, hrel⟩ := hag hdevs
      rw [ha, obind_ok]
      obtain ⟨x, c', w'⟩ := a
      obtain ⟨hw, hx⟩ := hrel
      simp only at hw hx ⊢
      cases x with
      | suspended =>
        obtain ⟨st', hout, hst'⟩ := hx
        rw [hout] at hd ⊢
        simp only at hd ⊢
        rw [← hw]
        have hd' : (specDrive smiMax n st' res.w).2.2 = [] := (List.append_eq_nil_iff.mp hd).2
        exact drive_agree smiMax hsmi n c' st' res.w hst' hd'
      | settled =>
        rw [hx]
        simp [hw, Exit.toEnd]
      | exhausted =>
        rw [hx]
        simp [hw, Exit.toEnd]
      | idle => exact absurd hx id

def StartRel (smiMax : Nat) : Start → SRes → Prop
  | .withCtx x c w, s => ExitRel smiMax x c w s
  | .noCtx x w, s => s.w = w ∧ s.out = .stop x ∧ x ≠ .suspended

theorem startReject_agree (smiMax : Nat) (e : JSVal) (w : W) :
    Agrees (StartRel smiMax) (startReject e w) (sReject e w) :=
  Agrees.ok ⟨rfl, rfl, by simp⟩

theorem startExh_agree (smiMax : Nat) (w : W) : Agrees (StartRel smiMax) (startExh w) (sExh w) :=
  Agrees.ok ⟨rfl, rfl, by simp⟩

theorem getIterator_agree (smiMax : Nat) {items m : JSVal} {w : W}
    {k1 : JSVal → JSVal → W → Outcome Start} {k2 : JSVal → JSVal → W → SRes}
    (hk : ∀ it nx w', it.isReceiver = true → Agrees (StartRel smiMax) (k1 it nx w') (k2 it nx w')) :
    Agrees (StartRel smiMax) (getIterator items m w k1) (getIteratorFromMethod items m w k2) := by
  unfold getIterator getIteratorFromMethod
  apply Agrees.perform
  · intro w1
    exact startExh_agree smiMax w1
  · intro r w1
    cases r with
    | err e => exact startReject_agree smiMax e w1
    | ok it =>
      simp only
      by_cases hit : it.isReceiver = true
      · rw [ite_eq_left hit, ite_eq_left hit]
        apply Agrees.perform
        · intro w2
          exact startExh_agree smiMax w2
        · intro r w2
          cases r with
          | err e => exact startReject_agree smiMax e w2
          | ok nx => exact hk it nx w2 hit
      · rw [ite_eq_right hit, ite_eq_right hit]
        exact startReject_agree smiMax _ w1

theorem startIter_agree (smiMax : Nat) (hsmi : smiMax < 2 ^ 53 - 1) {inp : Input}
    (hm : MapfnOK inp.mapfn) {it nx arr : JSVal} (hit : it.isReceiver = true)
    (harr : arr.isReceiver = true) (w : W) :
    Agrees (StartRel smiMax) (startIter smiMax inp it nx arr w)
      (iterHead ⟨arr, it, nx, inp.mapfn, inp.thisArg⟩ 0 w) := by
  have hc : IterRel ⟨arr, it, nx, inp.mapfn, inp.thisArg⟩ (initIterCtx inp it nx arr) :=
    ⟨rfl, rfl, rfl, rfl, rfl, harr, rfl, hit, rfl, rfl, hm, rfl, rfl⟩
  unfold startIter iterBody
  rw [iterTry_eq smiMax hc rfl rfl]
  exact Agrees.map (iterHandler_agree smiMax (iterHead_agree smiMax hsmi hc rfl (Nat.zero_le _) 7 _ _ _ w))
    fun a ha => ha

theorem startAL_agree (smiMax : Nat) {inp : Input} (hm : MapfnOK inp.mapfn) {al arr : JSVal}
    {len : Nat} (hal : al.isReceiver = true) (harr : arr.isReceiver = true) (w : W) :
    Agrees (StartRel smiMax) (startAL smiMax inp al len arr w)
      (alHead ⟨arr, al, len, inp.mapfn, inp.thisArg⟩ 0 w) := by
  have hc : ALRel smiMax ⟨arr, al, len, inp.mapfn, inp.thisArg⟩ (initALCtx smiMax inp al len arr) :=
    ⟨rfl, rfl, rfl, rfl, rfl, harr, rfl, hal, rfl, rfl, hm, rfl, rfl⟩
  unfold startAL alBody
  rw [alTry_eq smiMax hc rfl rfl]
  exact Agrees.map (alHandler_agree smiMax (alHead_agree smiMax hc rfl (Nat.zero_le _) 6 _ w))
    fun a ha => ha

theorem iterable_agree (smiMax : Nat) (hsmi : smiMax < 2 ^ 53 - 1) {inp : Input}
    (hm : MapfnOK inp.mapfn) {it nx : JSVal} (hit : it.isReceiver = true) (w : W) :
    Agrees (StartRel smiMax)
      (createArray inp.receiver none w fun arr w => startIter smiMax inp it nx arr w)
      (iterableBranch inp it nx w) := by
  unfold createArray iterableBranch
  by_cases hcn : inp.receiver.isConstructor = true
  · rw [ite_eq_left hcn, ite_eq_left hcn]
    apply Agrees.perform
    · intro w1
      exact startExh_agree smiMax w1
    · intro r w1
      cases r with
      | err e => exact startReject_agree smiMax e w1
      | ok a => exact startIter_agree smiMax hsmi hm hit (toReceiver_isReceiver a) w1
  · rw [ite_eq_right hcn, ite_eq_right hcn]
    apply Agrees.perform
    · intro w1
      exact startExh_agree smiMax w1
    · intro r w1
      cases r with
      | err e => exact startReject_agree smiMax e w1
      | ok a => exact startIter_agree smiMax hsmi hm hit (toReceiver_isReceiver a) w1

theorem arrayLike_agree (smiMax : Nat) {inp : Input} (hm : MapfnOK inp.mapfn) (w : W) :
    Agrees (StartRel smiMax)
      (perform (.getLength inp.items.toReceiver) w startExh fun r w =>
        match r with
        | .err e => startReject e w
        | .ok lv =>
          createArray inp.receiver (some lv.lengthOf) w fun arr w =>
            startAL smiMax inp inp.items.toReceiver lv.lengthOf arr w)
      (arrayLikeBranch inp w) := by
  unfold arrayLikeBranch
  apply Agrees.perform
  · intro w1
    exact startExh_agree smiMax w1
  · intro r w1
    cases r with
    | err e => exact startReject_agree smiMax e w1
    | ok lv =>
      simp only
      unfold createArray
      by_cases hcn : inp.receiver.isConstructor = true
      · rw [ite_eq_left hcn, ite_eq_left hcn]
        apply Agrees.perform
        · intro w2
          exact startExh_agree smiMax w2
        · intro r w2
          cases r with
          | err e => exact startReject_agree smiMax e w2
          | ok a => exact startAL_agree smiMax hm (toReceiver_isReceiver _) (toReceiver_isReceiver a) w2
      · rw [ite_eq_right hcn, ite_eq_right hcn]
        simp only [Option.getD]
        apply Agrees.perform
        · intro w2
          exact startExh_agree smiMax w2
        · intro r w2
          cases r with
          | err e => exact startReject_agree smiMax e w2
          | ok a => exact startAL_agree smiMax hm (toReceiver_isReceiver _) (toReceiver_isReceiver a) w2

theorem arrayFromAsync_agree (smiMax : Nat) (hsmi : smiMax < 2 ^ 53 - 1) (inp : Input) (w : W) :
    Agrees (StartRel smiMax) (arrayFromAsync smiMax inp w) (fromAsync inp w) := by
  unfold arrayFromAsync fromAsync
  by_cases hmap : inp.mapfn ≠ .undef ∧ inp.mapfn.isCallable = false
  · rw [ite_eq_left hmap, ite_eq_left hmap]
    exact startReject_agree smiMax _ w
  · rw [ite_eq_right hmap, ite_eq_right hmap]
    have hm := mapfnOK_of hmap
    apply Agrees.perform
    · intro w1
      exact startExh_agree smiMax w1
    · intro r w1
      cases r with
      | err e => exact startReject_agree smiMax e w1
      | ok m =>
        simp only
        by_cases hn : m.isNullish = true
        · rw [ite_eq_left hn, ite_eq_left hn]
          apply Agrees.perform
          · intro w2
            exact startExh_agree smiMax w2
          · intro r w2
            cases r with
            | err e => exact startReject_agree smiMax e w2
            | ok m' =>
              simp only
              by_cases hn' : m'.isNullish = true
              · rw [ite_eq_left hn', ite_eq_left hn']
                exact arrayLike_agree smiMax hm w2
              · rw [ite_eq_right hn', ite_eq_right hn']
                by_cases hc' : m'.isCallable = true
                · rw [ite_eq_left hc', ite_eq_left hc']
                  refine getIterator_agree smiMax ?_
                  intro it nx w3 _
                  exact Agrees.dev _ _
                · rw [ite_eq_right hc', ite_eq_right hc']
                  exact startReject_agree smiMax _ w2
        · rw [ite_eq_right hn, ite_eq_right hn]
          by_cases hc : m.isCallable = true
          · rw [ite_eq_left hc, ite_eq_left hc]
            refine getIterator_agree smiMax ?_
            intro it nx w2 hit
            exact iterable_agree smiMax hsmi hm hit w2
          · rw [ite_eq_right hc, ite_eq_right hc]
            exact startReject_agree smiMax _ w1

theorem spec_agreement {smiMax fuel : Nat} {inp : Input} {rs : List Resp}
    (hsmi : smiMax < 2 ^ 53 - 1) (hdev : (specRun smiMax fuel inp rs).2.2 = []) :
    run smiMax fuel inp rs = .ok ((specRun smiMax fuel inp rs).1, (specRun smiMax fuel inp rs).2.1) := by
  unfold run specRun at *
  simp only at hdev ⊢
  generalize hres : fromAsync inp ⟨rs, []⟩ = res at hdev ⊢
  have hdevs : res.devs = [] := by
    revert hdev
    cases res.out with
    | susp s => intro hd; exact (List.append_eq_nil_iff.mp hd).1
    | stop x => intro hd; exact hd
  have hag := arrayFromAsync_agree smiMax hsmi inp ⟨rs, []⟩
  rw [hres] at hag
  obtain ⟨st, hst, hrel⟩ := hag hdevs
  rw [hst, obind_ok]
  cases st with
  | withCtx x c w =>
    obtain ⟨hw, hx⟩ := hrel
    cases x with
    | suspended =>
      obtain ⟨s, hout, hs⟩ := hx
      rw [hout] at hdev ⊢
      simp only at hdev ⊢
      rw [← hw]
      rw [drive_agree smiMax hsmi fuel c s res.w hs (List.append_eq_nil_iff.mp hdev).2, omap_ok]
    | settled =>
      rw [hx]
      simp [hw, Exit.toEnd]
    | exhausted =>
      rw [hx]
      simp [hw, Exit.toEnd]
    | idle => exact absurd hx id
  | noCtx x w =>
    obtain ⟨hw, hout, hx⟩ := hrel
    rw [hout]
    cases x with
    | suspended => exact absurd rfl hx
    | settled => simp [hw]
    | exhausted => simp [hw]
    | idle => simp [hw]

theorem perform_cons {β : Type} (o : Op) (r : Resp) (rs : List Resp) (tr : List Op) (exh : W → β)
    (k : Resp → W → β) : perform o ⟨r :: rs, tr⟩ exh k = k r ⟨rs, o :: tr⟩ := rfl

def ALClean (smiMax : Nat) : Susp → Prop
  | .alValue E k => k < E.len ∧ E.len ≤ smiMax
  | .alMapped E k => k < E.len ∧ E.len ≤ smiMax
  | _ => False

def Clean (smiMax : Nat) (s : SRes) : Prop := s.devs = [] ∧ ∀ st, s.out = .susp st → ALClean smiMax st

theorem clean_reject (smiMax : Nat) (e : JSVal) (w : W) : Clean smiMax (sReject e w) :=
  ⟨rfl, fun _ h => nomatch h⟩

theorem clean_resolve (smiMax : Nat) (a : JSVal) (w : W) : Clean smiMax (sResolve a w) :=
  ⟨rfl, fun _ h => nomatch h⟩

theorem clean_exh (smiMax : Nat) (w : W) : Clean smiMax (sExh w) := ⟨rfl, fun _ h => nomatch h⟩

theorem alHead_clean (smiMax : Nat) {E : ALRec} (k : Nat) (hl : E.len ≤ smiMax) (w : W) :
    Clean smiMax (alHead E k w) := by
  unfold alHead
  split
  · rename_i hlt
    apply perform_ind
    · intro w1 _
      exact clean_exh smiMax w1
    · intro r w1 _
      cases r with
      | err e => exact clean_reject smiMax e w1
      | ok v =>
        apply perform_ind
        · intro w2 _
          exact clean_exh smiMax w2
        · intro r w2 _
          cases r with
          | err e => exact clean_reject smiMax e w2
          | ok _ =>
            refine ⟨rfl, fun st h => ?_⟩
            cases h
            exact ⟨hlt, hl⟩
  · apply perform_ind
    · intro w1 _
      exact clean_exh smiMax w1
    · intro r w1 _
      cases r with
      | err e => exact clean_reject smiMax e w1
      | ok _ => exact clean_resolve smiMax _ w1

theorem alDefine_clean (smiMax : Nat) {E : ALRec} {k : Nat} (hk : k < E.len) (hl : E.len ≤ smiMax)
    (v : JSVal) (w : W) : Clean smiMax (alDefine smiMax E k v w) := by
  unfold alDefine
  apply perform_ind
  · intro w1 _
    exact clean_exh smiMax w1
  · intro r w1 _
    cases r with
    | err e => exact clean_reject smiMax e w1
    | ok _ =>
      simp only
      rw [ite_eq_right (by omega)]
      exact alHead_clean smiMax (k + 1) hl w1

theorem alAfterValue_clean (smiMax : Nat) {E : ALRec} {k : Nat} (hk : k < E.len)
    (hl : E.len ≤ smiMax) (v : JSVal) (w : W) : Clean smiMax (alAfterValue smiMax E k v w) := by
  unfold alAfterValue
  split
  · exact alDefine_clean smiMax hk hl v w
  · apply perform_ind
    · intro w1 _
      exact clean_exh smiMax w1
    · intro r w1 _
      cases r with
      | err e => exact clean_reject smiMax e w1
      | ok m =>
        apply perform_ind
        · intro w2 _
          exact clean_exh smiMax w2
        · intro r w2 _
          cases r with
          | err e => exact clean_reject smiMax e w2
          | ok _ =>
            refine ⟨rfl, fun st h => ?_⟩
            cases h
            exact ⟨hk, hl⟩

theorem resume_clean (smiMax : Nat) {st : Susp} (h : ALClean smiMax st) (r : Resp) (w : W) :
    Clean smiMax (resume smiMax st r w) := by
  cases st with
  | alValue E k =>
    cases r with
    | ok v => exact alAfterValue_clean smiMax h.1 h.2 v w
    | err e => exact clean_reject smiMax e w
  | alMapped E k =>
    cases r with
    | ok m => exact alDefine_clean smiMax h.1 h.2 m w
    | err e => exact clean_reject smiMax e w
  | iterNext E k => exact absurd h id
  | iterMapped E k => exact absurd h id
  | iterClose E e => exact absurd h id

theorem specDrive_clean (smiMax : Nat) :
    ∀ (n : Nat) (st : Susp) (w : W), ALClean smiMax st → (specDrive smiMax n st w).2.2 = []
  | 0, _, _, _ => rfl
  | n + 1, st, w, h => by
    obtain ⟨rs, tr⟩ := w
    cases rs with
    | nil => rfl
    | cons r rs =>
      simp only [specDrive]
      obtain ⟨hd, hs⟩ := resume_clean smiMax h r ⟨rs, tr⟩
      generalize resume smiMax st r ⟨rs, tr⟩ = res at hd hs ⊢
      cases hout : res.out with
      | susp st' =>
        simp only [hd, List.nil_append]
        exact specDrive_clean smiMax n st' res.w (hs st' hout)
      | stop x => exact hd

theorem arrayLikeBranch_clean (smiMax : Nat) (inp : Input) (lv : JSVal) (rest : List Resp)
    (tr : List Op) (hl : lv.lengthOf ≤ smiMax) :
    Clean smiMax (arrayLikeBranch inp ⟨.ok lv :: rest, tr⟩) := by
  unfold arrayLikeBranch
  rw [perform_cons]
  simp only
  split
  · apply perform_ind
    · intro w1 _
      exact clean_exh smiMax w1
    · intro r w1 _
      cases r with
      | err e => exact clean_reject smiMax e w1
      | ok a => exact alHead_clean smiMax 0 hl w1
  · apply perform_ind
    · intro w1 _
      exact clean_exh smiMax w1
    · intro r w1 _
      cases r with
      | err e => exact clean_reject smiMax e w1
      | ok a => exact alHead_clean smiMax 0 hl w1

theorem fromAsync_arrayLike_clean (smiMax : Nat) (inp : Input) {m m' lv : JSVal}
    (hm : m.isNullish = true) (hm' : m'.isNullish = true) (hl : lv.lengthOf ≤ smiMax)
    (rest : List Resp) : Clean smiMax (fromAsync inp ⟨.ok m :: .ok m' :: .ok lv :: rest, []⟩) := by
  unfold fromAsync
  split
  · exact clean_reject smiMax _ _
  · rw [perform_cons]
    simp only
    rw [ite_eq_left hm, perform_cons]
    simp only
    rw [ite_eq_left hm']
    exact arrayLikeBranch_clean smiMax inp lv rest _ hl

theorem spec_agreement_arrayLike {smiMax fuel : Nat} {inp : Input} {m m' lv : JSVal}
    {rest : List Resp} (hsmi : smiMax < 2 ^ 53 - 1) (hm : m.isNullish = true)
    (hm' : m'.isNullish = true) (hl : lv.lengthOf ≤ smiMax) :
    run smiMax fuel inp (.ok m :: .ok m' :: .ok lv :: rest) =
      .ok ((specRun smiMax fuel inp (.ok m :: .ok m' :: .ok lv :: rest)).1,
        (specRun smiMax fuel inp (.ok m :: .ok m' :: .ok lv :: rest)).2.1) := by
  apply spec_agreement hsmi
  obtain ⟨hd, hs⟩ := fromAsync_arrayLike_clean smiMax inp hm hm' hl rest
  unfold specRun
  simp only
  generalize fromAsync inp ⟨.ok m :: .ok m' :: .ok lv :: rest, []⟩ = res at hd hs ⊢
  cases hout : res.out with
  | susp st =>
    simp only [hd, List.nil_append]
    exact specDrive_clean smiMax fuel st res.w (hs st hout)
  | stop x => exact hd

end ArrayFromAsync
