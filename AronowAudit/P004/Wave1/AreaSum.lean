import AronowAudit.P004.Wave1.AreaSumBlueprint
import AronowAudit.P004.Wave1.AreaSum.A1
import AronowAudit.P004.Wave1.AreaSum.A2
import AronowAudit.P004.Wave1.AreaSum.A3
import AronowAudit.P004.Wave1.AreaSum.A4
import AronowAudit.P004.Wave1.AreaSum.A5
import AronowAudit.P004.Wave1.AreaSum.A6
import AronowAudit.P004.Wave1.AreaSum.A7
import AronowAudit.P004.Wave1.AreaSum.A8
import AronowAudit.P004.Wave1.AreaSum.A9
import AronowAudit.P004.Wave1.AreaSum.A10
import AronowAudit.P004.Wave1.AreaSum.A11

/-! The actual Euclidean area-integral case-B bridge for P004-T5. -/

namespace AronowAudit.P004.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

theorem area_sum_spatial_caseB :
    (∀ j : Fin 6, circleAverage areaBinaryPopulation (j : ℝ) = areaWitnessTable j) ∧
    (∀ i : Fin 2, region areaBinaryPopulation i 6 =
      ⋃ j : Fin 6, region areaBinaryPopulation i (j : ℝ)) ∧
    (∀ i : Fin 2, Pairwise (fun j k : Fin 6 =>
      Disjoint (region areaBinaryPopulation i (j : ℝ))
        (region areaBinaryPopulation i (k : ℝ)))) ∧
    (∀ x z, areaBinaryPopulation.outcome x z = 0 ∨ areaBinaryPopulation.outcome x z = 1) ∧
    (∀ j : Fin 6, WellDefined areaBinaryPopulation j) ∧
    WellDefined areaBinaryPopulation 6 ∧
    (∀ i (j : Fin 6), (volume (region areaBinaryPopulation i j)).toReal =
      Real.pi * (2 * (j : ℝ) + 1)) ∧
    (∑ j : Fin 6, hajek (circleAverage areaBinaryPopulation j) areaWitnessAssignment) =
      -(17 / 500 : ℝ) ∧
    (∑ j : Fin 6, ame (fun _ => 1 / 2) (circleAverage areaBinaryPopulation j)) =
      -(17 / 500 : ℝ) ∧
    ame (fun _ => 1 / 2) (circleAverage areaBinaryPopulation 6) = (121 / 18000 : ℝ) ∧
    (0 : ℝ) < 121 / 18000 ∧ -(17 / 500 : ℝ) ≠ 121 / 18000 := by
  exact AronowAudit.P004.Wave1.AreaSum.assemble
    AreaSum.a2_proof AreaSum.a3_proof AreaSum.a6_proof AreaSum.a7_proof
    AreaSum.a8_proof AreaSum.a9_proof AreaSum.a10_proof AreaSum.a11_proof
    (AreaSum.volumes AreaSum.a2_proof AreaSum.a5_proof)

end
end AronowAudit.P004.Wave1
