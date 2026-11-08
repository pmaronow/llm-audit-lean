import SAP.P004b.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W3.P.T28_L3

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical Topology

private lemma armCount_pos_iff {N : ℕ} (z : SAP.P004b.Assignment N) (a : Bool) :
    0 < SAP.P004b.armCount z a ↔ ∃ i : Fin N, z i = a := by
  unfold SAP.P004b.armCount
  constructor
  · intro h
    by_contra hn
    have hz : ∀ i : Fin N, z i ≠ a := fun i hi => hn ⟨i, hi⟩
    have : (∑ i : Fin N, if z i = a then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hz i]
    linarith
  · rintro ⟨i, hi⟩
    have hle : (1 : ℝ) ≤ ∑ j : Fin N, if z j = a then (1 : ℝ) else 0 := by
      simpa [hi] using
        (Finset.single_le_sum (f := fun j : Fin N => if z j = a then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i))
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hle

private lemma empty_arms_iff {N : ℕ} (z : SAP.P004b.Assignment N) :
    ¬ SAP.P004b.ValidArms z ↔ z = (fun _ : Fin N => true) ∨ z = (fun _ => false) := by
  rw [SAP.P004b.ValidArms, armCount_pos_iff, armCount_pos_iff, not_and_or]
  constructor
  · intro h
    rcases h with h | h
    · right
      funext i
      have hi : z i ≠ true := by
        intro hz
        exact h ⟨i, hz⟩
      cases hz : z i <;> simp_all
    · left
      funext i
      have hi : z i ≠ false := by
        intro hz
        exact h ⟨i, hz⟩
      cases hz : z i <;> simp_all
  · rintro (h | h)
    · right
      intro hex
      rcases hex with ⟨i, hi⟩
      rw [h] at hi
      simp at hi
    · left
      intro hex
      rcases hex with ⟨i, hi⟩
      rw [h] at hi
      simp at hi

private lemma empty_arms_probability {N : ℕ} (hN : 0 < N) (p : ℝ) :
    SAP.P004b.prob (fun _ : Fin N => p) (fun z : SAP.P004b.Assignment N => ¬ SAP.P004b.ValidArms z) =
      p^N + (1-p)^N := by
  classical
  let t : SAP.P004b.Assignment N := fun _ => true
  let c : SAP.P004b.Assignment N := fun _ => false
  have htc : t ≠ c := by
    intro h
    have i : Fin N := ⟨0, by omega⟩
    have hi := congrFun h i
    cases hi
  have hindicator (z : SAP.P004b.Assignment N) :
      @ite ℝ (¬ SAP.P004b.ValidArms z)
        (Classical.propDecidable (¬ SAP.P004b.ValidArms z)) 1 0 =
        (if z = t then 1 else 0) + (if z = c then 1 else 0) := by
    have hevent := empty_arms_iff z
    by_cases ht : z = t
    · have he : ¬ SAP.P004b.ValidArms z := hevent.mpr (Or.inl ht)
      rw [if_pos he, if_pos ht]
      have hzc : z ≠ c := fun h => htc (ht.symm.trans h)
      rw [if_neg hzc]
      norm_num
    · by_cases hc : z = c
      · have he : ¬ SAP.P004b.ValidArms z := hevent.mpr (Or.inr hc)
        rw [if_pos he, if_neg ht, if_pos hc]
        norm_num
      · have hv : SAP.P004b.ValidArms z := by
          by_contra hh
          rcases hevent.mp hh with h | h
          · exact ht h
          · exact hc h
        simp [hv, ht, hc]
  simp only [SAP.P004b.prob, SAP.P004b.expect]
  simp_rw [hindicator, mul_add]
  rw [Finset.sum_add_distrib]
  simp [SAP.P004b.designWeight, SAP.P004b.coin, t, c]

end SAP.P004b.WH.W3.P.T28_L3

theorem SAP.P004b.WH.W3.T28_L3_proof : SAP.P004b.WH.W3.T28_L3 := by
  intro p hp
  constructor
  · intro N hN
    exact SAP.P004b.WH.W3.P.T28_L3.empty_arms_probability hN p
  · have hp0 : 0 ≤ p := hp.1.le
    have hp1 : p < 1 := hp.2
    have hq0 : 0 ≤ 1-p := by linarith
    have hq1 : 1-p < 1 := by linarith
    have hpowp : Filter.Tendsto (fun N : ℕ => p^N) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hp0 hp1
    have hpowq : Filter.Tendsto (fun N : ℕ => (1-p)^N) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    have hsum : Filter.Tendsto (fun N : ℕ => p^N + (1-p)^N) Filter.atTop (nhds 0) := by
      simpa using hpowp.add hpowq
    apply Filter.Tendsto.congr' ?_ hsum
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with N hN
    exact (SAP.P004b.WH.W3.P.T28_L3.empty_arms_probability hN p).symm
