import SAP.P005a.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.Bridge
open SAP.P005a

/-- These concrete witness statements agree by reduction of the SAP definitions. -/
theorem T1_correspondence :
    (type_of% @AronowAudit.P005.covariance_counterexample) ↔ T1Statement := Iff.rfl

theorem T3_correspondence :
    (type_of% @AronowAudit.P005.Wave1.leverage_variance_counterexample_proof) ↔
      T3Statement := Iff.rfl

theorem T5_correspondence :
    (type_of% @AronowAudit.P005.interacted_sign_counterexample) ↔ T5Statement := Iff.rfl

theorem T7_correspondence :
    ((type_of% @AronowAudit.P005.Wave1.univariate_endpoint_counterexample_proof) ∧
      (∀ n : ℕ, 6 ≤ n → 0 < AronowAudit.P005.spikeQ n) ∧
      (∀ n : ℕ, 6 ≤ n → AronowAudit.P005.kappa (AronowAudit.P005.spikePopulation n) *
        Real.log (1 : ℝ) = 0)) ↔ T7Statement := Iff.rfl

theorem T9_correspondence :
    ((type_of% @AronowAudit.P005.repaired_log_bounds) ∧
      (type_of% @AronowAudit.P005.repaired_log_conditions)) ↔ T9Statement := Iff.rfl

theorem T10_correspondence :
    (type_of% @AronowAudit.P005.interacted_weight_counterexample) ↔ T10Statement := Iff.rfl

theorem T12_correspondence :
    (type_of% @AronowAudit.P005.interacted_inverse_counterexample) ↔ T12Statement := Iff.rfl

end SAP.P005a.Bridge
