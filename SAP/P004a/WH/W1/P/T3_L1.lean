import SAP.P004a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T3_L1

open MeasureTheory Set
open scoped BigOperators Classical

noncomputable section

private abbrev center (N : ℕ) (i : Fin N) : EuclideanSpace ℝ (Fin 2) :=
  SAP.P004a.planePoint (10 * (i : ℝ)) 0

private theorem center_distance (N : ℕ) (i j : Fin N) :
    dist (center N i) (center N j) = |(10 * (i : ℝ)) - (10 * (j : ℝ))| := by
  rw [EuclideanSpace.dist_eq]
  simp [center, SAP.P004a.planePoint, Fin.sum_univ_two, Real.dist_eq, Real.sqrt_sq_eq_abs]

private theorem centers_separated {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    10 ≤ dist (center N i) (center N j) := by
  have hval : i.val ≠ j.val := by
    intro he
    exact hij (Fin.ext he)
  have hgap : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
    rcases lt_or_gt_of_ne hval with hij' | hji'
    · have hle : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij'.le
      have hc : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hij')
      rw [abs_of_nonpos (show (i : ℝ) - (j : ℝ) ≤ 0 by linarith)]
      linarith
    · have hle : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hji'.le
      have hc : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hji')
      rw [abs_of_nonneg (show 0 ≤ (i : ℝ) - (j : ℝ) by linarith)]
      linarith
  rw [center_distance]
  rw [← mul_sub, abs_mul]
  norm_num
  nlinarith

private theorem disk_index_unique {N : ℕ} {x : EuclideanSpace ℝ (Fin 2)}
    (i j : Fin N) (hi : dist x (center N i) ≤ 1) (hj : dist x (center N j) ≤ 1) :
    i = j := by
  by_contra hij
  have hs := centers_separated i j hij
  have ht : dist (center N i) (center N j) ≤ 2 := by
    calc
      dist (center N i) (center N j) ≤ dist (center N i) x + dist x (center N j) :=
        dist_triangle _ _ _
      _ ≤ 1 + 1 := add_le_add (by simpa only [dist_comm] using hi) hj
      _ = 2 := by norm_num
  linarith

private theorem disk_outcome_at_center (N : ℕ) (j : Fin N) (z : Assignment N) :
    (w1ActiveDiskPopulation N).outcome (center N j) z = activeTable N j z := by
  classical
  change (∑ i : Fin N, if dist (center N j) (center N i) ≤ 1 then
    w1ActiveSign N i * bit (z i) else 0) = activeTable N j z
  rw [Finset.sum_eq_single j]
  · simp [center, activeTable, w1ActiveSign]
  · intro i _ hij
    have hs := centers_separated j i hij.symm
    have hnot : ¬ dist (center N j) (center N i) ≤ 1 := by linarith
    simp [hnot]
  · simp

private theorem active_outcome_at_center (N : ℕ) (j : Fin N) (z : Assignment N) :
    (activePopulation N).outcome (center N j) z = activeTable N j z := by
  classical
  change (∑ i : Fin N, if center N j = center N i then activeTable N i z else 0) = _
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have hneq : center N j ≠ center N i := by
      intro he
      have hd : dist (center N j) (center N i) = 0 := dist_eq_zero.mpr he
      have hs := centers_separated j i hij.symm
      linarith
    simp [hneq]
  · simp

private theorem disk_outcome_on_disk (N : ℕ) (i : Fin N) (x : EuclideanSpace ℝ (Fin 2))
    (z : Assignment N) (hi : dist x (center N i) ≤ 1) :
    (w1ActiveDiskPopulation N).outcome x z = w1ActiveSign N i * bit (z i) := by
  classical
  change (∑ j : Fin N, if dist x (center N j) ≤ 1 then
    w1ActiveSign N j * bit (z j) else 0) = _
  rw [Finset.sum_eq_single i]
  · simp only [if_pos hi]
  · intro j _ hji
    have hnot : ¬ dist x (center N j) ≤ 1 := by
      intro hj
      have hu : j = i := disk_index_unique j i hj hi
      exact hji hu
    simp [hnot]
  · simp

private theorem disk_outcome_outside (N : ℕ) (x : EuclideanSpace ℝ (Fin 2))
    (z : Assignment N) (hout : ∀ i : Fin N, 1 < dist x (center N i)) :
    (w1ActiveDiskPopulation N).outcome x z = 0 := by
  classical
  change (∑ i : Fin N, if dist x (center N i) ≤ 1 then
    w1ActiveSign N i * bit (z i) else 0) = 0
  apply Finset.sum_eq_zero
  intro i _
  have hnot : ¬ dist x (center N i) ≤ 1 := not_le_of_gt (hout i)
  simp [hnot]

private theorem disk_outcome_bound (N : ℕ) (x : EuclideanSpace ℝ (Fin 2))
    (z : Assignment N) : |(w1ActiveDiskPopulation N).outcome x z| < 2 := by
  classical
  by_cases hx : ∃ i : Fin N, dist x (center N i) ≤ 1
  · obtain ⟨i, hi⟩ := hx
    rw [disk_outcome_on_disk N i x z hi]
    have hs : |w1ActiveSign N i| ≤ 1 := by
      unfold w1ActiveSign
      split_ifs <;> norm_num
    have hb : |bit (z i)| ≤ 1 := by
      cases z i <;> norm_num [bit]
    have hm : |w1ActiveSign N i * bit (z i)| ≤ 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg (w1ActiveSign N i), abs_nonneg (bit (z i))]
    linarith
  · have hout : ∀ i : Fin N, 1 < dist x (center N i) := by
      intro i
      have hnot : ¬ dist x (center N i) ≤ 1 := fun h => hx ⟨i, h⟩
      exact lt_of_not_ge hnot
    rw [disk_outcome_outside N x z hout]
    norm_num

private theorem region_measurable (N : ℕ) (d : ℝ) (i : Fin N) :
    MeasurableSet (region (activePopulation N) i d) := by
  simp only [region, nodeDistance, activePopulation, linePopulation, Metric.infDist_singleton]
  exact measurableSet_Icc.preimage (measurable_id.dist measurable_const)

private theorem center_mem_region (N : ℕ) (d : ℝ) (i : Fin N) (hd : 0 ≤ d) :
    center N i ∈ region (activePopulation N) i d := by
  simp [region, nodeDistance, activePopulation, linePopulation, center,
    Metric.infDist_singleton, hd]

private theorem region_mass_formula (N : ℕ) (d : ℝ) (i : Fin N) :
    (activePopulation N).zeta (region (activePopulation N) i d) =
      ∑ j : Fin N, if center N j ∈ region (activePopulation N) i d then (1 : ENNReal) else 0 := by
  classical
  change (∑ j : Fin N, Measure.dirac (center N j)) (region (activePopulation N) i d) = _
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.dirac_apply]
  change (if center N j ∈ region (activePopulation N) i d then (1 : ENNReal) else 0) = _
  rfl

private theorem region_mass_pos (N : ℕ) (d : ℝ) (i : Fin N) (hd : 0 ≤ d) :
    0 < (activePopulation N).zeta (region (activePopulation N) i d) := by
  rw [region_mass_formula]
  have hle : (1 : ENNReal) ≤
      ∑ j : Fin N, if center N j ∈ region (activePopulation N) i d then (1 : ENNReal) else 0 := by
    calc
      1 = (if center N i ∈ region (activePopulation N) i d then (1 : ENNReal) else 0) := by
        simp [center_mem_region N d i hd]
      _ ≤ ∑ j : Fin N, if center N j ∈ region (activePopulation N) i d then (1 : ENNReal) else 0 :=
        Finset.single_le_sum (f := fun j : Fin N =>
          if center N j ∈ region (activePopulation N) i d then (1 : ENNReal) else 0)
          (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ i)
  exact lt_of_lt_of_le (by norm_num) hle

private theorem region_mass_lt_top (N : ℕ) (d : ℝ) (i : Fin N) :
    (activePopulation N).zeta (region (activePopulation N) i d) < ⊤ := by
  have htotal : (activePopulation N).zeta Set.univ < ⊤ := by
    change (∑ j : Fin N, Measure.dirac (center N j)) Set.univ < ⊤
    rw [Measure.finsetSum_apply]
    simp
  exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) htotal

private theorem disk_integral_eq (N : ℕ) (d : ℝ) (i : Fin N) (z : Assignment N) :
    (∫ x in region (activePopulation N) i d,
      (w1ActiveDiskPopulation N).outcome x z ∂(activePopulation N).zeta) =
    (∫ x in region (activePopulation N) i d,
      (activePopulation N).outcome x z ∂(activePopulation N).zeta) := by
  classical
  let S := region (activePopulation N) i d
  have hnew : ∀ j : Fin N, Integrable
      (fun x => (w1ActiveDiskPopulation N).outcome x z)
      ((Measure.dirac (center N j)).restrict S) := by
    intro j
    exact (integrable_dirac (by simp)).restrict
  have hold : ∀ j : Fin N, Integrable
      (fun x => (activePopulation N).outcome x z)
      ((Measure.dirac (center N j)).restrict S) := by
    intro j
    exact (integrable_dirac (by simp)).restrict
  have hr : ((∑ j : Fin N, Measure.dirac (center N j)).restrict S) =
      ∑ j : Fin N, (Measure.dirac (center N j)).restrict S := by
    simpa only [Measure.restrictₗ_apply] using
      map_sum (Measure.restrictₗ S) (fun j : Fin N => Measure.dirac (center N j)) Finset.univ
  change (∫ x, (w1ActiveDiskPopulation N).outcome x z
      ∂((∑ j : Fin N, Measure.dirac (center N j)).restrict S)) =
    (∫ x, (activePopulation N).outcome x z
      ∂((∑ j : Fin N, Measure.dirac (center N j)).restrict S))
  rw [hr, integral_finsetSum_measure (fun j _ => hnew j),
    integral_finsetSum_measure (fun j _ => hold j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [setIntegral_dirac, setIntegral_dirac]
  by_cases hj : center N j ∈ S
  · simp [hj, disk_outcome_at_center, active_outcome_at_center]
  · simp [hj]

end

end SAP.P004a.WH.W1.P.T3_L1

open MeasureTheory
open SAP.P004a
open SAP.P004a.WH.W1.P.T3_L1

theorem SAP.P004a.WH.W1.T3_L1_proof : SAP.P004a.WH.W1.T3_L1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro N x z
    exact disk_outcome_bound N x z
  · intro N i x z hi
    exact disk_outcome_on_disk N i x z hi
  · intro N x z hout
    exact disk_outcome_outside N x z hout
  · intro N d hd i
    refine ⟨region_measurable N d i, region_mass_pos N d i hd,
      region_mass_lt_top N d i, ?_⟩
    intro z
    have hi : MeasureTheory.Integrable
        (fun x => (SAP.P004a.w1ActiveDiskPopulation N).outcome x z)
        (SAP.P004a.activePopulation N).zeta := by
      change MeasureTheory.Integrable
        (fun x => (SAP.P004a.w1ActiveDiskPopulation N).outcome x z)
        (∑ j : Fin N, Measure.dirac (center N j))
      rw [MeasureTheory.integrable_finsetSum_measure]
      intro j hj
      exact integrable_dirac (by simp)
    exact hi.integrableOn
  · intro N d
    funext i z
    unfold SAP.P004a.circleAverage
    change (∫ x in region (SAP.P004a.activePopulation N) i d,
        (SAP.P004a.w1ActiveDiskPopulation N).outcome x z ∂
          (SAP.P004a.activePopulation N).zeta) /
        ((SAP.P004a.activePopulation N).zeta
          (region (SAP.P004a.activePopulation N) i d)).toReal =
      (∫ x in region (SAP.P004a.activePopulation N) i d,
        (SAP.P004a.activePopulation N).outcome x z ∂
          (SAP.P004a.activePopulation N).zeta) /
        ((SAP.P004a.activePopulation N).zeta
          (region (SAP.P004a.activePopulation N) i d)).toReal
    rw [disk_integral_eq]
