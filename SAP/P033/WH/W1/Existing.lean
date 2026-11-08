import SAP.P033.Defs.WholeW1
import SAP.P033.Bridge
import AronowAudit.P010.Wave1.Gap.GP010P033B1b
import AronowAudit.P033.P033_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace SAP.P033.WH.W1

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

theorem existing_T1 : SAP.P033.T1Statement := by
  have h := AronowAudit.P033.Wave1.diagnostic_counterexample_proof
  refine ⟨SAP.P033.Bridge.T1_correspondence.mpr h,
    SAP.P033.Bridge.M1Certificate_correspondence.mpr
      AronowAudit.P033.m1_exact_certificate,
    SAP.P033.Bridge.M1WLSCertificate_correspondence.mpr AronowAudit.P033.m1_wls_rows,
    ?_, ?_, ?_, by norm_num⟩
  · funext i
    fin_cases i <;> norm_num [SAP.P033.m1Bias, SAP.P033.m1BiasMoment, SAP.P033.m1Curvature]
  · funext i
    fin_cases i <;> norm_num [SAP.P033.m1Corrected, SAP.P033.m1Linear,
      SAP.P033.m1Bias, SAP.P033.m1BiasMoment, SAP.P033.m1Curvature]
  · change variance (AronowAudit.P033.rdEstimator AronowAudit.P033.m1Corrected)
      (AronowAudit.P033.rdConditionalLaw AronowAudit.P033.m1Treated AronowAudit.P033.m1Control) /
    variance (AronowAudit.P033.rdEstimator AronowAudit.P033.m1Linear)
      (AronowAudit.P033.rdConditionalLaw AronowAudit.P033.m1Treated AronowAudit.P033.m1Control) = 410/83
    rw [h.2.2.2.2.2.1, h.2.2.2.2.2.2.1]
    norm_num

theorem existing_T2 : SAP.P033.T2Statement := by
  have h := SAP.P033.Bridge.T2_correspondence.mpr
    (@AronowAudit.P033.Wave1.diagnostic_correction_proof)
  have he := AronowAudit.P033.m2_conditional_law_eq
  refine ⟨h, SAP.P033.Bridge.M2Certificate_correspondence.mpr
    AronowAudit.P033.m2_polynomial_certificate,
    AronowAudit.P033.Wave1.diagnostic_counterexample_proof.1,
    AronowAudit.P033.Wave1.diagnostic_counterexample_proof.2.1, ?_, ?_, ?_, ?_, by norm_num⟩
  · change (∫ Y, AronowAudit.P033.rdEstimator AronowAudit.P033.m1Linear Y
      ∂AronowAudit.P033.rdConditionalLaw AronowAudit.P033.m2Treated AronowAudit.P033.m1Control) = 4
    rw [he]
    exact AronowAudit.P033.m1_probability_moments.1
  · change HasLaw _ _ (AronowAudit.P033.rdConditionalLaw
      AronowAudit.P033.m2Treated AronowAudit.P033.m1Control)
    rw [he]
    exact AronowAudit.P033.Wave1.GP010P033B1b_t1_m1_pivots.1
  · simpa only [show (5 : ℝ)^2 = 25 by norm_num] using
      AronowAudit.P033.Wave1.GP010P033B1b_t2_standard_tail 5 (by norm_num)
  · intro N hN S E _ F _hF
    exact congrArg (fun μ => μ.map F) ((h.2.2.2.2.2.2.2.2.2.2.2.2.1 N hN).1 S)


end SAP.P033.WH.W1
