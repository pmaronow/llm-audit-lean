import SAP.P039.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.Bridge
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory

/-- Assemble the missing-quarter identities and both published-audit witnesses. -/
theorem T1_correspondence : T1Statement := by
  refine ⟨?_, AronowAudit.P039.income_counterexample_half,
    AronowAudit.P039.income_counterexample_nine_tenths, by norm_num⟩
  intro decay hd
  obtain ⟨_, hp, hq⟩ := AronowAudit.P039.income_denominators_positive decay hd
  refine ⟨hp, hq, ?_, ?_, ?_⟩
  · intro h h' heq
    exact AronowAudit.P039.income_ignores_quarter_one decay h h' heq
  · intro h
    have hmissing := AronowAudit.P039.missing_quarter_numerator decay h
    change describedNumerator decay h = incomeNumerator decay h + decay^15*h 1 at hmissing
    linarith
  · have hmissing := AronowAudit.P039.missing_quarter_denominator decay
    change describedDenominator decay = incomeDenominator decay + decay^15 at hmissing
    linarith

/-- Assemble the corrected definition, exact difference, equality criterion and endpoints. -/
theorem T2_correspondence : T2Statement := by
  refine ⟨?_, AronowAudit.P039.income_endpoint_values⟩
  intro decay h hd
  obtain ⟨hl, hp, hq⟩ := AronowAudit.P039.income_denominators_positive decay hd
  exact ⟨hl, hp, hq, (fun h' heq => AronowAudit.P039.income_ignores_quarter_one decay h h' heq),
    AronowAudit.P039.missing_quarter_numerator decay h,
    AronowAudit.P039.missing_quarter_denominator decay,
    AronowAudit.P039.income_growth_difference decay h hd,
    AronowAudit.P039.income_growth_equality_iff decay h hd⟩

end SAP.P039.Bridge
