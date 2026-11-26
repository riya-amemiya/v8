import ArrayBuild.StoreSafety

namespace ArrayBuild

open Torque

inductive LoopResult where
  | done (a : JSArr)
  | ub
  | fatal
  deriving Repr

def createLoop (env : StoreEnv) (rt : JSArr → Nat → Val → JSArr) :
    JSArr → Nat → List Val → LoopResult
  | a, _, [] => .done a
  | a, k, v :: vs =>
    match fastCreateDataProperty env a k v with
    | .done a' => createLoop env rt a' (k + 1) vs
    | .slow b => createLoop env rt (rt b k v) (k + 1) vs
    | .ub => .ub
    | .fatal => .fatal

def RuntimeOK (rt : JSArr → Nat → Val → JSArr) : Prop :=
  ∀ b k v, b.WF → b.SlackHoles → k ≤ b.length → CreatesData b k v (rt b k v)

theorem setElem_split {pre : List Val} {rest : List (Option Val)} {v : Val} :
    setElem (pre.map some ++ rest) pre.length v = (pre ++ [v]).map some ++ rest.drop 1 := by
  unfold setElem
  cases rest with
  | nil =>
    rw [ite_eq_right (by simp)]
    simp
  | cons x rest =>
    rw [ite_eq_left (by simp)]
    rw [List.set_append_right _ _ (by simp)]
    simp

theorem createLoop_spec {env : StoreEnv} {rt : JSArr → Nat → Val → JSArr} (hrt : RuntimeOK rt) :
    ∀ (vs pre : List Val) (rest : List (Option Val)) (a : JSArr),
      a.WF → a.SlackHoles → a.elems = pre.map some ++ rest →
      ∃ a', createLoop env rt a pre.length vs = .done a' ∧ a'.WF ∧ a'.SlackHoles ∧
        a'.elems = (pre ++ vs).map some ++ rest.drop vs.length ∧
        a'.length = max a.length (pre.length + vs.length)
  | [], pre, rest, a, hw, hsl, he => by
    refine ⟨a, rfl, hw, hsl, by simp [he], ?_⟩
    have := JSArr.elems_length hw
    rw [he, List.length_append, List.length_map] at this
    simp only [List.length_nil, Nat.add_zero]
    omega
  | v :: vs, pre, rest, a, hw, hsl, he => by
    have hlen := JSArr.elems_length hw
    have hk : pre.length ≤ a.length := by
      rw [← hlen, he]
      simp
    have hstep : ∃ a1, (createLoop env rt a pre.length (v :: vs) =
        createLoop env rt a1 (pre.length + 1) vs) ∧ a1.WF ∧ a1.SlackHoles ∧
        a1.elems = setElem a.elems pre.length v ∧ a1.length = max a.length (pre.length + 1) := by
      rcases fastCreateDataProperty_spec (env := env) (i := pre.length) (v := v) hw with
        ⟨a', hd, hw', he', hl', hsl', _⟩ | ⟨b, hs, hbw, hbsl, hsame⟩
      · exact ⟨a', by simp only [createLoop, hd], hw', hsl' hsl, he', hl'⟩
      · have hc := hrt b pre.length v hbw (hbsl hsl) (by rw [hsame.length]; exact hk)
        refine ⟨rt b pre.length v, by simp only [createLoop, hs], hc.wf, hc.slack, ?_, ?_⟩
        · rw [hc.elems, hsame.elems]
        · rw [hc.length, hsame.length]
    obtain ⟨a1, heq, hw1, hsl1, he1, hl1⟩ := hstep
    have he1' : a1.elems = (pre ++ [v]).map some ++ rest.drop 1 := by
      rw [he1, he, setElem_split]
    obtain ⟨a', hrun, hw', hsl', he', hl'⟩ :=
      createLoop_spec hrt vs (pre ++ [v]) (rest.drop 1) a1 hw1 hsl1 he1'
    refine ⟨a', ?_, hw', hsl', ?_, ?_⟩
    · rw [heq]
      simpa using hrun
    · rw [he']
      simp
    · rw [hl', hl1]
      simp
      omega

theorem createLoop_ne {env : StoreEnv} {rt : JSArr → Nat → Val → JSArr} (hrt : RuntimeOK rt)
    {vs : List Val} {a : JSArr} (hw : a.WF) (hsl : a.SlackHoles) (hz : a.length = 0) :
    ∃ a', createLoop env rt a 0 vs = .done a' ∧ a'.WF ∧ a'.SlackHoles ∧
      a'.elems = vs.map some ∧ a'.length = vs.length := by
  have he : a.elems = ([] : List Val).map some ++ [] := by
    rw [← List.length_eq_zero_iff.mp (by rw [JSArr.elems_length hw, hz] : a.elems.length = 0)]
    rfl
  obtain ⟨a', h, hw', hsl', he', hl'⟩ := createLoop_spec (env := env) hrt vs [] [] a hw hsl he
  refine ⟨a', h, hw', hsl', by simpa using he', ?_⟩
  rw [hl', hz]
  simp

end ArrayBuild
