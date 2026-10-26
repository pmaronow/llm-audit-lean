import AronowAudit.P004.Wave1.AreaSum

/-! P004-T5: the spatial counterexample using Euclidean area integrals for all assignments. -/

namespace AronowAudit.P004.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- The actual disk/annulus area averages give the negative six-bin sum
and the positive whole-region effect. -/
theorem spatial_area_sum_counterexample_proof :
    (∀ x z, areaBinaryPopulation.outcome x z = 0 ∨ areaBinaryPopulation.outcome x z = 1) ∧
    (∀ j : Fin 6, WellDefined areaBinaryPopulation j) ∧
    WellDefined areaBinaryPopulation 6 ∧
    (∀ i (j : Fin 6), (volume (region areaBinaryPopulation i j)).toReal =
      Real.pi*(2*(j : ℝ)+1)) ∧
    (∑ j : Fin 6, hajek (circleAverage areaBinaryPopulation j) areaWitnessAssignment) = -(17/500 : ℝ) ∧
    (∑ j : Fin 6, ame (fun _ => 1/2) (circleAverage areaBinaryPopulation j)) = -(17/500 : ℝ) ∧
    ame (fun _ => 1/2) (circleAverage areaBinaryPopulation 6) = (121/18000 : ℝ) ∧
    (0 : ℝ) < 121/18000 ∧ -(17/500 : ℝ) ≠ 121/18000 := by
  exact area_sum_spatial_caseB.2.2.2

end
end AronowAudit.P004.Wave1
