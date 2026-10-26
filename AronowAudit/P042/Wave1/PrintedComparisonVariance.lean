import AronowAudit.P042.Wave1.PrintedComparisonVarianceBlueprint
import AronowAudit.P042.Wave1.SixAtomic.N1
import AronowAudit.P042.Wave1.SixAtomic.N2
import AronowAudit.P042.Wave1.PrintedComparisonVariance.N3

/-! Refutation of the unrestricted comparison-variance assertion (P042-T5). -/

set_option autoImplicit false

namespace AronowAudit.P042.Wave1

open AronowAudit.P042 MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

theorem printed_comparison_variance_refuted :
    ¬ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ι : Type) [Fintype ι] [DecidableEq ι] (N A : Finset ι),
      N.Nonempty → A.Nonempty → Disjoint N A →
      ∀ (D : ι → Ω → ℝ), (∀ j, MemLp (D j) 2 μ) → (∀ j, 0 < variance (D j) μ) →
        let v := fun j => variance (D j) μ
        variance (fun ω => pooled (subsetWeight N v) D ω - pooled (subsetWeight A v) D ω) μ =
          (∑ j ∈ N, (v j)⁻¹)⁻¹ + (∑ j ∈ A, (v j)⁻¹)⁻¹ := by
  exact PrintedComparisonVariance.assemble
    SixAtomic.n1_proof SixAtomic.n2_proof PrintedComparisonVariance.n3_proof

end

end AronowAudit.P042.Wave1
