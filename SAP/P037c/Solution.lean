import SAP.P037c.WH.W1.Proofs.T35
import SAP.P037c.WH.W1.Proofs.T27
import SAP.P037c.WH.W1.Proofs.T33
import SAP.P037c.WH.W1.Proofs.T34
import SAP.P037c.WH.W1.Proofs.T43
import SAP.P037c.Defs
import SAP.P037c.Bridge
import AronowAudit.P037.P037_Network
import AronowAudit.P037.P037_Regression
import AronowAudit.P037.P037_Review
import AronowAudit.P037.Wave1.Gap.GLP037B4
import AronowAudit.P037.Wave1.Gap.GP037B4
import AronowAudit.P037.Wave1.Gap.GLP037B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The supported direct-effect counterexample. -/
theorem T35 : SAP.P037c.T35WholeStatement :=
  SAP.P037c.WH.W1.T35_whole

/-- Exact sharp-null validity and the direct-effect term. -/
theorem T36 {Ω I : Type*} [Fintype Ω] [Fintype I] : T36Statement Ω I := by
  have cert := Bridge.paired_certificate
  refine ⟨Bridge.sharp_null, Bridge.direct_effect, Bridge.pair_statistic,
    Bridge.own_assignment_only, ?_, ?_, cert.2.2.2.2.1, cert.2.2.2.2.2.2.2.2⟩
  · intro h
    have halt : pairedAlternative∈pairedSupport := by
      norm_num [pairedSupport, pairedAlternative]
    have he := h pairedObserved cert.2.1 pairedAlternative halt (0,false)
    norm_num [directOnly, pairedObserved, pairedAlternative] at he
  · rw [Bridge.pair_statistic pairedObserved cert.2.1]
    exact cert.2.2.1

/-- The actual hierarchical witness and the fitted contrasts. -/
theorem T27 : SAP.P037c.T27WholeStatement :=
  SAP.P037c.WH.W1.T27_whole

/-- General WLS mean identities and exact one-covariate formulas. -/
theorem T28 {I : Type*} [Fintype I] : T28Statement I := by
  refine ⟨Bridge.regression_means, Bridge.one_covariate,
    AronowAudit.P037.separate_pooled_prediction_difference, Bridge.prediction_mean, ?_,
    by norm_num⟩
  intro yb bk beta xb xbar
  rw [← sub_eq_zero, AronowAudit.P037.separate_pooled_prediction_difference]
  simp only [mul_eq_zero, sub_eq_zero]

set_option maxRecDepth 4096 in
/-- The actual finite-design variances disagree when the controls are collapsed. -/
theorem T33 : SAP.P037c.T33WholeStatement :=
  SAP.P037c.WH.W1.T33_whole

/-- Refits retaining the fixed controls reproduce the constant shifts. -/
theorem T34 : SAP.P037c.T34WholeStatement :=
  SAP.P037c.WH.W1.T34_whole

/-- The expected normal equations give the moderation bias and common-intercept corollary. -/
theorem T43 : SAP.P037c.T43WholeStatement :=
  SAP.P037c.WH.W1.T43_whole

end SAP.P037c
