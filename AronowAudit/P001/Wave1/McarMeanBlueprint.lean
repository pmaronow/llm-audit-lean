import AronowAudit.P001.P001_Foundations

/-!
# Expected value under MCAR with exact binary support (P001-T111)

Theorem 6.1.6 and Definition 6.1.5 (p. 213), with an a.e. binary response
indicator and both `P(R=0) > 0` and `P(R=1) > 0`.
The respondent conditional mean is
`conditionalMeanAt μ R Y* 1 = ∫_{R=1} Y* / P(R=1)`.
Independence and equality of the censored and original outcomes on `{R = 1}`
give equality of the population and respondent means.
-/

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.McarMean

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section


def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y R : Ω → ℝ), Measurable Y → Measurable R → Integrable Y μ →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < prob μ {ω | R ω = 0} → 0 < prob μ {ω | R ω = 1} → IndepFun Y R μ →
    mean μ Y = conditionalMeanAt μ R (fun ω => censored (Y ω) (R ω)) 1

/-- The MCAR mean identity, expressed as `Target`. -/
def N1 : Prop := Target.{u}

/-- The MCAR mean identity follows from `N1`. -/
theorem assemble (h1 : N1.{u}) : Target.{u} := h1

end

end AronowAudit.P001.Wave1.McarMean
