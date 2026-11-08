import SAP.P046.Bridge.Part1
import AronowAudit.P046.Wave1.Gap.GP046B1
import AronowAudit.P046.Wave1.Gap.GP046B2
import AronowAudit.P046.Wave1.Gap.RepairT4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.Bridge

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

/-- Transport the certified continuous-population counterexample. -/
theorem target1 : T1Statement := by
  obtain ⟨hv, hm, hp, h119, _, hc⟩ := AronowAudit.P046.Wave1.counterexample_proof
  exact ⟨valid_from hv, AronowAudit.P046.IntervalExample.covariate_law,
    hm, hp, AronowAudit.P046.IntervalExample.certified_mass_exact, h119, by norm_num, hc⟩

/-- Transport the positive-event conditional counterexample and its numeric facts. -/
theorem target2 : T2Statement := by
  obtain ⟨hv, hm, he, ht⟩ := AronowAudit.P046.ConditionalExample.counterexample
  refine ⟨valid_from hv, AronowAudit.P046.ConditionalExample.covariate_law, hm, he,
    AronowAudit.P046.ConditionalExample.covariate_event_positive,
    AronowAudit.P046.ConditionalExample.xi_value, ?_,
    AronowAudit.P046.ConditionalExample.radius_sq_lt,
    AronowAudit.P046.ConditionalExample.radius_lt_half,
    AronowAudit.P046.ConditionalExample.printed_rhs, ht⟩
  intro a
  unfold printedRadius
  rw [show xi ConditionalExample.study a = 100/81 from
    AronowAudit.P046.ConditionalExample.xi_value a]
  congr 1
  norm_num
  ring

/-- The coverage and width statements agree definitionally after adapting the record. -/
theorem target3 : T3Statement := by
  intro M hM
  have hv := valid_to hM
  constructor
  · intro alpha ha
    have hw := AronowAudit.P046.corrected_width (toStudy M) hv alpha ha
    exact ⟨fun n hn => AronowAudit.P046.Wave1.proposition3_corrected_proof
      (toStudy M) hv n hn alpha ha, hw.1, hw.2⟩
  · intro b hb hbound n hn alpha ha
    exact AronowAudit.P046.proposition3_known_bound (toStudy M) hv b hb hbound n hn alpha ha

/-- Transport the actual balanced cross-fitted witness, preserving both Gaussian variances. -/
theorem target4 : T4Statement := by
  obtain ⟨hv, hm, hb, hl, hf, hn, hht, hadj, hlt, hw, hr0, hrg⟩ :=
    AronowAudit.P046.Wave1.regression_counterexample_proof
  exact ⟨valid_from hv, AronowAudit.P046.RegressionExample.covariate_law,
    hm, hb, hl, hf, hn, AronowAudit.P046.RegressionExample.fits_adjusted,
    normal_from (by norm_num) hht, normal_from (by norm_num) hadj,
    hlt, by norm_num, by norm_num, hw, hr0, hrg⟩

end
end SAP.P046.Bridge
