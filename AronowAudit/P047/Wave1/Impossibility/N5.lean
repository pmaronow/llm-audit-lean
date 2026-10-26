import AronowAudit.P047.Wave1.ImpossibilityBlueprint
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

/-- Integrate by the finite pushforward of the cell label. -/
theorem n5_proof : N5 := by
  classical
  intro s1 M family σ
  let ν : Measure (Fin (M + 1)) := uniform01.map (cellLabel M)
  have hmass (j : Fin (M + 1)) : ν.real {j} = 1 / (M + 1 : ℝ) := by
    rw [measureReal_def]
    change (uniform01.map (cellLabel M) {j}).toReal = _
    rw [Measure.map_apply (measurable_cellLabel M) (measurableSet_singleton j)]
    change (uniform01 {w | cellLabel M w = j}).toReal = _
    rw [s1 M j, ENNReal.toReal_ofReal (by positivity)]
  have hm : Measurable (fun j : Fin (M + 1) => cellMean family (σ j)) :=
    measurable_of_countable _
  change (∫ w, (fun j : Fin (M + 1) => cellMean family (σ j)) (cellLabel M w)
    ∂uniform01) = _
  rw [← integral_map (measurable_cellLabel M).aemeasurable hm.aestronglyMeasurable]
  change (∫ j, cellMean family (σ j) ∂ν) = _
  rw [integral_fintype (Integrable.of_finite :
    Integrable (fun j : Fin (M + 1) => cellMean family (σ j)) ν)]
  simp only [hmass, smul_eq_mul]
  rw [familyEffect_eq_cell_average family (by omega : 1 ≤ M + 1) σ]
  rw [← Finset.mul_sum]
  push_cast
  ring

end

end AronowAudit.P047.Wave1.Impossibility
