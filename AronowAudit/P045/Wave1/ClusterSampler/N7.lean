import AronowAudit.P045.Wave1.ClusterSamplerBlueprint
import Mathlib.Data.List.OfFn

/-! Length-indexed terminal-centre sums for the net `{0,3}`. -/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.ClusterSampler

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

private theorem n7_pair_support (hc : TraceClassification) (cs : List (Fin 4))
    (hs : cs.toFinset = ({0, 3} : Finset (Fin 4)))
    (hm : traceMass (pathDistance (n := 4)) 3 true cs ≠ 0) :
    cs = [3, 0] ∨ ∃ r : ℕ, cs = List.replicate (r + 1) 0 ++ [3] := by
  classical
  have hzero : (0 : Fin 4) ∈ cs.toFinset := by rw [hs]; simp
  rcases hc cs hm with h | h | h | ⟨r, j, hj, h⟩
  · norm_num [h] at hzero
  · norm_num [h] at hzero
  · exact Or.inl h
  · have hjmem : j ∈ cs.toFinset := by rw [h]; simp
    have hjcases : j = 0 ∨ j = 3 := by
      simpa only [hs, Finset.mem_insert, Finset.mem_singleton] using hjmem
    have hj3 : j = 3 := hjcases.resolve_left hj
    right
    refine ⟨r, ?_⟩
    simpa only [hj3] using h

private theorem n7_short_sum (hc : TraceClassification) (t : ℕ) (ht : t < 2) :
    (∑ z : Fin t → Fin 4, if (List.ofFn z).toFinset = ({0, 3} : Finset (Fin 4)) then
      traceMass (pathDistance (n := 4)) 3 true (List.ofFn z) else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro z _
  by_cases hs : (List.ofFn z).toFinset = ({0, 3} : Finset (Fin 4))
  · rw [if_pos hs]
    by_contra hm
    rcases n7_pair_support hc (List.ofFn z) hs hm with h | ⟨r, h⟩
    · have hlen : t = 2 := by
        simpa only [List.length_ofFn, List.length_cons, List.length_nil] using
          congrArg List.length h
      omega
    · have hlen : t = r + 2 := by
        simpa only [List.length_ofFn, List.length_append, List.length_replicate,
          List.length_cons, List.length_nil] using congrArg List.length h
      omega
  · exact if_neg hs

theorem n7_proof : N7 := by
  classical
  intro h4 hc t
  by_cases ht : t < 2
  · rw [n7_short_sum hc t ht]
    simp only [if_neg (show t ≠ 2 by omega), if_neg (show ¬ 2 ≤ t by omega), add_zero]
  · have ht2 : 2 ≤ t := by omega
    obtain ⟨r, rfl⟩ : ∃ r : ℕ, t = r + 2 := ⟨t - 2, by omega⟩
    let f : (Fin (r + 2) → Fin 4) → ℝ := fun z =>
      if (List.ofFn z).toFinset = ({0, 3} : Finset (Fin 4)) then
        traceMass (pathDistance (n := 4)) 3 true (List.ofFn z) else 0
    change (∑ z, f z) = _
    let retry : Fin (r + 2) → Fin 4 :=
      Fin.append (m := r + 1) (n := 1)
        (fun _ : Fin (r + 1) => 0) (fun _ : Fin 1 => 3)
    have hretry : List.ofFn retry = List.replicate (r + 1) 0 ++ [3] := by
      simpa only [retry, List.ofFn_const, List.replicate_one] using
        (List.ofFn_fin_append (fun _ : Fin (r + 1) => (0 : Fin 4))
          (fun _ : Fin 1 => (3 : Fin 4)))
    have hretryset : (List.replicate (r + 1) (0 : Fin 4) ++ [3]).toFinset = {0, 3} := by
      simp [List.toFinset_append,
        List.toFinset_replicate_of_ne_zero (by omega : r + 1 ≠ 0)]
    have hretryval : f retry = (1 / 4 : ℝ) ^ (r + 2) := by
      dsimp only [f]
      rw [hretry, if_pos hretryset, four_path_repeat_trace_mass r 3 (by decide)]
    have hvanish : ∀ z : Fin (r + 2) → Fin 4,
        z ≠ retry → List.ofFn z ≠ [3, 0] → f z = 0 := by
      intro z hz h30
      dsimp only [f]
      by_cases hs : (List.ofFn z).toFinset = ({0, 3} : Finset (Fin 4))
      · rw [if_pos hs]
        by_contra hm
        rcases n7_pair_support hc (List.ofFn z) hs hm with h | ⟨s, h⟩
        · exact h30 h
        · have hlen : r + 2 = s + 2 := by
            simpa only [List.length_ofFn, List.length_append, List.length_replicate,
              List.length_cons, List.length_nil] using congrArg List.length h
          have hsr : s = r := by omega
          subst s
          exact hz (List.ofFn_injective (h.trans hretry.symm))
      · exact if_neg hs
    by_cases hr : r = 0
    · subst r
      let z30 : Fin 2 → Fin 4 := fun i => if i.val = 0 then 3 else 0
      have hz30 : List.ofFn z30 = [3, 0] := by simp [z30, List.ofFn_succ]
      have hne : z30 ≠ retry := by
        intro heq
        have hlist := congrArg List.ofFn heq
        rw [hz30, hretry] at hlist
        norm_num [List.replicate_succ] at hlist
      have hz30val : f z30 = 1 / 4 := by
        have hs30 : ([3, 0] : List (Fin 4)).toFinset = {0, 3} := by decide
        dsimp only [f]
        rw [hz30, if_pos hs30, h4.2.2]
      have hoff : ∀ z : Fin 2 → Fin 4, z ≠ z30 ∧ z ≠ retry → f z = 0 := by
        intro z hz
        apply hvanish z hz.2
        intro hlist
        exact hz.1 (List.ofFn_injective (hlist.trans hz30.symm))
      have hsum : (∑ z, f z) = f z30 + f retry :=
        Fintype.sum_eq_add z30 retry hne hoff
      rw [hsum, hz30val, hretryval]
      norm_num
    · have hoff : ∀ z : Fin (r + 2) → Fin 4, z ≠ retry → f z = 0 := by
        intro z hz
        apply hvanish z hz
        intro hlist
        have hlen : r + 2 = 2 := by
          simpa only [List.length_ofFn, List.length_cons, List.length_nil] using
            congrArg List.length hlist
        exact hr (by omega)
      have hsum : (∑ z, f z) = f retry := Fintype.sum_eq_single retry hoff
      rw [hsum, hretryval]
      simp only [if_neg (show r + 2 ≠ 2 by omega),
        if_pos (show 2 ≤ r + 2 by omega), zero_add]

end

end AronowAudit.P045.Wave1.ClusterSampler
