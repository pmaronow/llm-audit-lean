import SAP.P046.Defs
import AronowAudit.P046.P046_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.Bridge

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

/-- The project and SAP records store the same population data. -/
def toStudy (M : Study) : AronowAudit.P046.Study := ⟨M.law, M.pi, M.m, M.delta⟩

def fromStudy (M : AronowAudit.P046.Study) : Study := ⟨M.law, M.pi, M.m, M.delta⟩

def toFit {n : ℕ} (F : CrossFit n) : AronowAudit.P046.CrossFit n :=
  ⟨F.fold, F.g, F.measurable_g, F.opposite_fold⟩

def fromFit {n : ℕ} (F : AronowAudit.P046.CrossFit n) : CrossFit n :=
  ⟨F.fold, F.g, F.measurable_g, F.opposite_fold⟩

theorem study_roundtrip (M : AronowAudit.P046.Study) : toStudy (fromStudy M) = M := rfl

theorem fit_roundtrip {n : ℕ} (F : AronowAudit.P046.CrossFit n) : toFit (fromFit F) = F := rfl

theorem valid_to {M : Study} (h : ValidStudy M) : AronowAudit.P046.ValidStudy (toStudy M) :=
  ⟨h.probability, h.continuous, h.measurable_pi, h.measurable_m, h.delta_pos,
    h.positivity, h.propensity, h.regression, h.regression_range, h.unconfounded0, h.unconfounded1⟩

theorem valid_from {M : AronowAudit.P046.Study} (h : AronowAudit.P046.ValidStudy M) :
    ValidStudy (fromStudy M) :=
  ⟨h.probability, h.continuous, h.measurable_pi, h.measurable_m, h.delta_pos,
    h.positivity, h.propensity, h.regression, h.regression_range, h.unconfounded0, h.unconfounded1⟩

/-- Every statistical function is unchanged by the structural adapter. -/
theorem ht_agrees (M : Study) {n : ℕ} (a : Sample n) :
    AronowAudit.P046.ht (toStudy M) a = ht M a := rfl

theorem adjusted_agrees (M : Study) {n : ℕ} (F : CrossFit n) (a : Sample n) :
    AronowAudit.P046.adjusted (toStudy M) (toFit F) a = adjusted M F a := rfl

theorem interval_study : toStudy IntervalExample.study = AronowAudit.P046.IntervalExample.study := rfl

theorem conditional_study : toStudy ConditionalExample.study = AronowAudit.P046.ConditionalExample.study := rfl

theorem regression_study : toStudy RegressionExample.study = AronowAudit.P046.RegressionExample.study := rfl

theorem regression_fits (n : ℕ) : toFit (RegressionExample.fits n) = AronowAudit.P046.RegressionExample.fits n := rfl

/-- The SAP convergence predicate also records nonnegativity of its variance. -/
theorem normal_from {M : Study} {est : ∀ n, Sample n → ℝ} {v : ℝ} (hv : 0 ≤ v)
    (h : AronowAudit.P046.NormalLimit (toStudy M) est v) : NormalLimit M est v :=
  ⟨hv, h⟩

end
end SAP.P046.Bridge
