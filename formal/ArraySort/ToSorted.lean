import ArraySort.Tail

namespace ArraySort

open Torque

section

variable {ε : Type}

theorem fillUndef_good {len : Nat} {e : ε} {c : Core} :
    ∀ d i (copy : List (Option Val)), len - i = d → i ≤ len → copy.length = len →
      ((fillUndef len i copy) e c).Good (fun r e' c' => e' = e ∧ c' = c ∧
        r = copy.take i ++ List.replicate (len - i) (some .undef))
  | 0, i, copy, hd, hi, hl => by
    rw [fillUndef, dite_eq_right (by omega), good_pure]
    refine ⟨rfl, rfl, ?_⟩
    rw [show len - i = 0 by omega, show i = copy.length by omega]
    simp
  | d + 1, i, copy, hd, hi, hl => by
    rw [fillUndef, dite_eq_left (by omega), good_ite, ite_eq_left (by omega)]
    refine (fillUndef_good d (i + 1) (copy.set i (some .undef)) (by omega) (by omega) (by simp [hl])).mono ?_
    rintro r e' c' ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [h3, ← seg_zero, seg_set_snoc (Nat.zero_le _) (by omega), seg_zero, List.append_assoc,
      show len - i = (len - (i + 1)) + 1 by omega, List.replicate_succ]
    rfl

theorem copyToNewFast_good {cfg : Cfg} {kind : Kind} {n nu sortLength : Nat} {e : ε} {c : Core}
    (hk : kind = .packedSmi ∨ kind = .packedElem) (hs : sortLength = n + nu) (hm : sortLength ≤ cfg.maxFast)
    (hn : n ≤ c.work.length) (hk2 : nu = 0 ∨ kind = .packedElem) :
    ((copyToNewFast cfg kind n nu sortLength) e c).Good (fun a _ _ =>
      a.store = c.work.take n ++ List.replicate nu (some .undef) ∧ a.length = sortLength) := by
  unfold copyToNewFast
  simp only [good_bind, good_dcheck, good_getCore]
  refine ⟨hk, hs, hm, ⟨by omega, hn⟩, hk2, ?_⟩
  refine (fillUndef_good (sortLength - n) n (c.work.take n ++ List.replicate (sortLength - n) none)
    rfl (by omega) (by simp; omega)).mono ?_
  rintro r e' c' ⟨-, -, h3⟩
  rw [good_pure]
  have hlen : (c.work.take n).length = n := by simp; omega
  refine ⟨?_, ?_⟩
  · simp only [newArray]
    rw [h3, List.take_append_of_le_length (by omega), List.take_take, Nat.min_self,
      show sortLength - n = nu by omega]
  · simp only [newArray]
    rw [h3]
    simp
    omega

theorem smiScan_good {n : Nat} {e : ε} {c : Core} (hv : Vals c.work 0 n) :
    ∀ d i, n - i = d → ((smiScan n i) e c).Good (fun _ e' c' => e' = e ∧ c' = c)
  | 0, i, hd => by
    rw [smiScan, dite_eq_right (by omega), good_pure]
    exact ⟨rfl, rfl⟩
  | d + 1, i, hd => by
    rw [smiScan, dite_eq_left (by omega)]
    simp only [good_bind, good_ld, Core.get_work]
    obtain ⟨v, hv'⟩ := hv.2 i (Nat.zero_le _) (by omega)
    refine ⟨⟨by omega, by have := hv.1; omega⟩, ?_⟩
    simp only [Int.toNat_natCast, hv', good_jsAny]
    refine ⟨_, rfl, ?_⟩
    rw [good_ite]
    split
    · exact smiScan_good hv d (i + 1) (by omega)
    · rw [good_pure]
      exact ⟨rfl, rfl⟩

theorem slowCopy_good {n : Nat} {e : ε} {c : Core} (hv : Vals c.work 0 n) :
    ∀ d i (acc : List (Option Val)), n - i = d → i ≤ n →
      ((slowCopy n i acc) e c).Good (fun r e' c' => e' = e ∧ c' = c ∧ r = acc ++ seg c.work i n)
  | 0, i, acc, hd, hi => by
    rw [slowCopy, dite_eq_right (by omega), good_pure]
    refine ⟨rfl, rfl, ?_⟩
    rw [show i = n by omega, seg_self, List.append_nil]
  | d + 1, i, acc, hd, hi => by
    rw [slowCopy, dite_eq_left (by omega)]
    simp only [good_bind, good_ld, Core.get_work]
    obtain ⟨v, hv'⟩ := hv.2 i (Nat.zero_le _) (by omega)
    refine ⟨⟨by omega, by have := hv.1; omega⟩, ?_⟩
    simp only [Int.toNat_natCast, hv', good_jsAny]
    refine ⟨_, rfl, ?_⟩
    refine (slowCopy_good hv d (i + 1) (acc ++ [some v]) (by omega) (by omega)).mono ?_
    rintro r e' c' ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [h3, seg_cons_getD (l := c.work) (lo := i) (hi := n) (by omega) (by have := hv.1; omega), hv']
    simp

end

theorem perm_facts {l l' : List (Option Val)} {vs : List Val} {n : Nat} (hw : seg l 0 n = vs.map some)
    (hp : PermOn l l' 0 n) :
    seg l' 0 n = ((seg l' 0 n).filterMap id).map some ∧ ((seg l' 0 n).filterMap id).Perm vs := by
  have hperm : (seg l' 0 n).Perm (vs.map some) := hw ▸ hp.perm
  have hall : ∀ x ∈ seg l' 0 n, x ≠ none := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 (hperm.mem_iff.1 hx)
    simp
  refine ⟨(map_some_filterMap_id _ hall).symm, ?_⟩
  have := hperm.filterMap id
  simpa using this

theorem intoCopy_good {cfg : Cfg} {env : Env} {user : Bool} {n nu sortLength : Nat} {vs : List Val}
    {e : Ext} {c : Core} (hsm : cfg.smiMax < 2 ^ 31) (hn : n ≤ cfg.smiMax)
    (hnl : n ≤ c.work.length) (hw : seg c.work 0 n = vs.map some) (hsz : c.size = 0)
    (hs : sortLength = n + nu) :
    ((intoCopy cfg env user n nu sortLength) e c).Good (fun a _ _ => ∃ vs' : List Val, vs'.Perm vs ∧
      a.store = vs'.map some ++ List.replicate nu (some .undef) ∧ a.length = sortLength) := by
  have hv : Vals c.work 0 n := ⟨hnl, fun i _ hi => ⟨_, getD_seg_map hnl hw hi⟩⟩
  unfold intoCopy
  rw [good_bind]
  refine (sortCore_good (sortCompare env user) cfg.smiMax hn hsm (e := e) hv hsz).mono ?_
  rintro _ e2 c2 hp
  obtain ⟨hw2, hvp⟩ := perm_facts hw hp
  have hnl2 : n ≤ c2.work.length := by rw [hp.len]; exact hnl
  have htake : c2.work.take n = ((seg c2.work 0 n).filterMap id).map some := by
    rw [← seg_zero]
    exact hw2
  have hv2 : Vals c2.work 0 n := hv.of_permOn hp
  rw [good_ite]
  split
  · next hm =>
    rw [good_ite]
    split
    · refine (copyToNewFast_good (Or.inr rfl) hs hm hnl2 (Or.inr rfl)).mono ?_
      rintro a e' c' ⟨h3, h4⟩
      exact ⟨_, hvp, by rw [h3, htake], h4⟩
    · next hnu =>
      simp only [good_bind, good_getCore, good_dcheck]
      refine ⟨hnl2, ?_⟩
      refine (smiScan_good hv2 (n - 0) 0 rfl).mono ?_
      rintro allSmi e' c' ⟨he', hc'⟩
      subst e'
      subst c'
      refine (copyToNewFast_good ?_ hs hm hnl2 (Or.inl (by simpa using hnu))).mono ?_
      · cases allSmi <;> simp
      · rintro a e'' c'' ⟨h3, h4⟩
        exact ⟨_, hvp, by rw [h3, htake], h4⟩
  · rw [good_bind]
    refine (slowCopy_good hv2 (n - 0) 0 [] rfl (Nat.zero_le _)).mono ?_
    rintro r e' c' ⟨-, -, h3⟩
    rw [good_pure]
    refine ⟨_, hvp, ?_, rfl⟩
    simp only
    rw [h3, List.nil_append, show sortLength - n = nu by omega, ← hw2]

end ArraySort
