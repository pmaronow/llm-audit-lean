import AronowAudit.P004.Wave1.LinePopulation.N1

namespace AronowAudit.P004.Wave1.LinePopulation

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- A support atom belongs to a region exactly when its node belongs to the ball. -/
theorem line_atom_mem_region_iff {N : ℕ} (R : CircleTable N) (d : ℝ) (i j : Fin N) :
    planePoint (10 * (j : ℝ)) 0 ∈ region (linePopulation R) i d ↔
      nodeSeparation (linePopulation R) i j ≤ d := by
  change (Metric.infDist (planePoint (10 * (j : ℝ)) 0)
    {planePoint (10 * (i : ℝ)) 0} ∈ Set.Icc 0 d) ↔ _
  rw [Metric.infDist_singleton, line_separation_eq_dist]
  rw [dist_comm (planePoint (10 * (j : ℝ)) 0) (planePoint (10 * (i : ℝ)) 0)]
  simp only [Set.mem_Icc, dist_nonneg, true_and]

theorem line_region_measurable {N : ℕ} (R : CircleTable N) (d : ℝ) (i : Fin N) :
    MeasurableSet (region (linePopulation R) i d) := by
  simp only [region, nodeDistance, linePopulation, Metric.infDist_singleton]
  exact measurableSet_Icc.preimage (measurable_id.dist measurable_const)

/-- At each atom the outcome sum contains precisely its own entry. -/
theorem line_outcome_at_atom {N : ℕ} (R : CircleTable N) (j : Fin N) (z : Assignment N) :
    (linePopulation R).outcome (planePoint (10 * (j : ℝ)) 0) z = R j z := by
  classical
  change (∑ k : Fin N, if planePoint (10 * (j : ℝ)) 0 =
    planePoint (10 * (k : ℝ)) 0 then R k z else 0) = R j z
  simp only [line_point_injective.eq_iff]
  simp

/-- The measure of a line region is the number of its support atoms. -/
theorem line_spatial_mass {N : ℕ} (R : CircleTable N) (d : ℝ) (i : Fin N) :
    (linePopulation R).zeta (region (linePopulation R) i d) =
      ((ball (nodeSeparation (linePopulation R)) i d).card : ENNReal) := by
  classical
  change (∑ j : Fin N, Measure.dirac (planePoint (10 * (j : ℝ)) 0))
    (region (linePopulation R) i d) = _
  rw [Measure.finsetSum_apply]
  calc
    (∑ j : Fin N, Measure.dirac (planePoint (10 * (j : ℝ)) 0)
        (region (linePopulation R) i d)) =
        ∑ j : Fin N, if nodeSeparation (linePopulation R) i j ≤ d
          then (1 : ENNReal) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Measure.dirac_apply]
      change (if planePoint (10 * (j : ℝ)) 0 ∈ region (linePopulation R) i d
        then (1 : ENNReal) else 0) = _
      rw [line_atom_mem_region_iff]
    _ = ((ball (nodeSeparation (linePopulation R)) i d).card : ENNReal) := by
      simp [ball]

/-- Numerator calculation for a general (not necessarily nonnegative) band label. -/
theorem line_spatial_integral {N : ℕ} (R : CircleTable N) (d : ℝ)
    (i : Fin N) (z : Assignment N) :
    (∫ x in region (linePopulation R) i d, (linePopulation R).outcome x z
      ∂(linePopulation R).zeta) =
      ∑ j ∈ ball (nodeSeparation (linePopulation R)) i d, R j z := by
  classical
  have hi : ∀ j : Fin N, Integrable (fun x => (linePopulation R).outcome x z)
      ((Measure.dirac (planePoint (10 * (j : ℝ)) 0)).restrict
        (region (linePopulation R) i d)) := by
    intro j
    exact (integrable_dirac (by simp)).restrict
  have hr : ((∑ j : Fin N, Measure.dirac (planePoint (10 * (j : ℝ)) 0)).restrict
      (region (linePopulation R) i d)) =
      ∑ j : Fin N, (Measure.dirac (planePoint (10 * (j : ℝ)) 0)).restrict
        (region (linePopulation R) i d) := by
    simpa only [Measure.restrictₗ_apply] using
      map_sum (Measure.restrictₗ (region (linePopulation R) i d))
        (fun j : Fin N => Measure.dirac (planePoint (10 * (j : ℝ)) 0)) Finset.univ
  change (∫ x, (linePopulation R).outcome x z
    ∂((∑ j : Fin N, Measure.dirac (planePoint (10 * (j : ℝ)) 0)).restrict
      (region (linePopulation R) i d))) = _
  rw [hr, integral_finsetSum_measure (fun j _ => hi j)]
  simp_rw [setIntegral_dirac, line_atom_mem_region_iff, line_outcome_at_atom]
  rw [ball, Finset.sum_filter]

theorem n2_proof : N2 := by
  intro N R d _hd i z
  unfold circleAverage
  rw [line_spatial_integral, line_spatial_mass, ENNReal.toReal_natCast]

end
end AronowAudit.P004.Wave1.LinePopulation
