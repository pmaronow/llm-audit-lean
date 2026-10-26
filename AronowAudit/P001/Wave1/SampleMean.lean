import AronowAudit.P001.Wave1.SampleMeanBlueprint
import AronowAudit.P001.Wave1.SampleMean.N1

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

theorem sample_mean_paper_contract :
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), IID μ X → Integrable (X 0) μ → ∀ (n : ℕ), 0 < n →
    mean μ (sampleMean X n) = mean μ (X 0) ∧
    (MemLp (X 0) 2 μ →
      var μ (sampleMean X n) = var μ (X 0) / (n : ℝ) ∧
      (0 < var μ (X 0) → ∀ ε : ℝ, 0 < ε →
        prob μ {ω | ε ≤ |sampleMean X n ω - mean μ (X 0)|} ≤
          var μ (X 0) / (ε ^ 2 * (n : ℝ)))) :=
  SampleMean.assemble SampleMean.n1_proof

end

end AronowAudit.P001.Wave1
