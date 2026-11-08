import SAP.P039.Bridge.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.Bridge
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory

/-- Literal signed-order maxima and both voter-centered witnesses. -/
theorem T5_correspondence : T5Statement := by
  refine ⟨AronowAudit.P039.voter_centered_1980_counterexample,
    AronowAudit.P039.literal_largest_value_counterexample,
    AronowAudit.P039.signed_extremism_maxima, ?_⟩
  intro j
  fin_cases j <;> norm_num [depositedExtremism, signedWinner, signedMaximumScore]

/-- The magnitude rule with its signed product, both samples and worked example. -/
theorem T6_correspondence : T6Statement := by
  refine ⟨AronowAudit.P039.corrected_extremism_selections,
    AronowAudit.P039.corrected_extremism_margins,
    AronowAudit.P039.maximum_effect_samples,
    AronowAudit.P039.maximum_effect_contribution,
    AronowAudit.P039.maximum_effect_sign,
    AronowAudit.P039.maximum_effect_worked_example, ?_⟩
  intro j
  fin_cases j <;> norm_num [depositedExtremism, magnitudeWinner, magnitudeMaximumScore]

end SAP.P039.Bridge
