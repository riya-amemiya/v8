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

end ArrayFromAsync
