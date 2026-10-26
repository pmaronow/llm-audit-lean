import AronowAudit.P001.Wave1.McarMeanBlueprint
import AronowAudit.P001.Wave1.McarMean.N1

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem mcar_paper_support_mean :
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y R : Ω → ℝ), Measurable Y → Measurable R → Integrable Y μ →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < prob μ {ω | R ω = 0} → 0 < prob μ {ω | R ω = 1} → IndepFun Y R μ →
    mean μ Y = conditionalMeanAt μ R (fun ω => censored (Y ω) (R ω)) 1 :=
  McarMean.assemble McarMean.n1_proof

end

end AronowAudit.P001.Wave1
