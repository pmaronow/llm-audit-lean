import AronowAudit.P042.Wave1.PrintedPoolingVarianceBlueprint
import AronowAudit.P042.Wave1.SixAtomic.N1
import AronowAudit.P042.Wave1.SixAtomic.N2
import AronowAudit.P042.Wave1.PrintedPoolingVariance.N3

/-! Refutation of the unrestricted pooling-variance assertion (P042-T5). -/

set_option autoImplicit false

namespace AronowAudit.P042.Wave1

open AronowAudit.P042 MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

theorem printed_pooling_variance_refuted :
    ¬ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {J : ℕ},
      0 < J → ∀ (D : Fin J → Ω → ℝ), (∀ j, MemLp (D j) 2 μ) →
        (∀ j, 0 < variance (D j) μ) →
        variance (pooled (normalizedWeight (fun j => variance (D j) μ)) D) μ =
          (totalWeight (fun j => variance (D j) μ))⁻¹ := by
  exact PrintedPoolingVariance.assemble
    SixAtomic.n1_proof SixAtomic.n2_proof PrintedPoolingVariance.n3_proof

end

end AronowAudit.P042.Wave1
