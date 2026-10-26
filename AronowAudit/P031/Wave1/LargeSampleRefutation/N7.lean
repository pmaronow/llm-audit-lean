import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Order.DenselyOrdered

/-! Portmanteau for the closed half-line, whose boundary has zero
mass under the nondegenerate standard Gaussian. -/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem n7_proof : N7 := by
  intro hCLT x
  let X : ℕ → (ℕ → Fin 2) → ℝ := fun m ω =>
    (Real.sqrt m)⁻¹ * ∑ j ∈ Finset.range m, sgn2 (ω j)
  change TendstoInDistribution X atTop (fun z : ℝ => z)
    (fun _ => coinMeasure) (ProbabilityTheory.gaussianReal 0 1) at hCLT
  letI : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal one_ne_zero
  have hboundary :
      ((ProbabilityTheory.gaussianReal 0 1).map (fun z : ℝ => z))
        (frontier (Set.Iic x)) = 0 := by
    simp only [Measure.map_id', frontier_Iic, measure_singleton]
  have hsets :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      hCLT.tendsto hboundary
  have hmap (m : ℕ) :
      coinMeasure.map (X m) (Set.Iic x) = coinMeasure {ω | X m ω ≤ x} := by
    rw [Measure.map_apply_of_aemeasurable (hCLT.forall_aemeasurable m)
      measurableSet_Iic]
    rfl
  have hmass : Tendsto (fun m => coinMeasure {ω | X m ω ≤ x}) atTop
      (nhds ((ProbabilityTheory.gaussianReal 0 1) (Set.Iic x))) := by
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id', hmap] using hsets
  have hreal :=
    (ENNReal.tendsto_toReal
      (measure_ne_top (ProbabilityTheory.gaussianReal 0 1) (Set.Iic x))).comp hmass
  simpa only [Function.comp_def, X, normalCDF, ProbabilityTheory.cdf_eq_real, measureReal_def] using hreal

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
