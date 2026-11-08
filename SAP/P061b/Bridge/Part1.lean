import SAP.P061b.Defs
import AronowAudit.P061.P061_PaperDomains

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061b.Bridge
open scoped BigOperators Classical

/-- Field-for-field adapter; no change to feasible assignments or their masses. -/
def toAudit {Ω : Type} (D : AtomicDesign Ω) : AronowAudit.P061.Design Ω where
  p := D.p
  nonneg := D.nonneg
  summable := D.summable
  total := D.total

def fromAudit {Ω : Type} (D : AronowAudit.P061.Design Ω) : AtomicDesign Ω where
  p := D.p
  nonneg := D.nonneg
  summable := D.summable
  total := D.total

theorem to_from {Ω : Type} (D : AronowAudit.P061.Design Ω) : toAudit (fromAudit D) = D := rfl

theorem from_to {Ω : Type} (D : AtomicDesign Ω) : fromAudit (toAudit D) = D := rfl

theorem probability_correspondence {Ω : Type} (D : AtomicDesign Ω) (A : Ω → Prop) :
    eventProbability D A = AronowAudit.P061.probability (toAudit D) A := rfl

theorem mean_correspondence {Ω : Type} (D : AtomicDesign Ω) (X : Ω → ℝ) :
    designMean D X = AronowAudit.P061.expectation (toAudit D) X := rfl

theorem moment_correspondence {Ω : Type} (D : AtomicDesign Ω) (X : Ω → ℝ) :
    HasFirstMoment D X ↔ AronowAudit.P061.Integrable (toAudit D) X := Iff.rfl

theorem exposure_correspondence {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (i : Fin N) (d : ℝ) :
    exposureMean D g y i d = AronowAudit.P061.epo (toAudit D) g y i d := rfl

theorem ht_correspondence {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d : ℝ) :
    htMean D g y d = AronowAudit.P061.ht (toAudit D) g y d := rfl

theorem support_stability_correspondence {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) :
    SupportStable D g y ↔ AronowAudit.P061.NURVA (toAudit D) g y := Iff.rfl

theorem global_stability_correspondence {Ω : Type} {N : ℕ} (g y : Schedule Ω N) :
    GloballyStable g y ↔ AronowAudit.P061.SUTVA g y := Iff.rfl

theorem covariance_sum_correspondence {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d e : ℝ) :
    covarianceSum D g y d e = AronowAudit.P061.htCovarianceExpression (toAudit D) g y d e := rfl

theorem ht_variance_estimate_correspondence {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d : ℝ) :
    htVarianceEstimate D g y d = AronowAudit.P061.htVarianceEstimator (toAudit D) g y d := rfl

theorem conservative_estimate_correspondence {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d : ℝ) : conservativeVarianceEstimate D g y d =
    AronowAudit.P061.conservativeVarianceEstimator (toAudit D) g y d := rfl

theorem adjusted_correspondence {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y F : Schedule Ω N) (d : ℝ) :
    adjustedMean D g y F d = AronowAudit.P061.regressionEstimator (toAudit D) g y F d := rfl

theorem one_treated_correspondence : toAudit oneTreated = AronowAudit.P061.oppositeDesign := rfl

theorem both_or_neither_correspondence :
    toAudit bothOrNeither = AronowAudit.P061.sameDesign := rfl

theorem independent_household_correspondence :
    toAudit independentHousehold = AronowAudit.P061.uniformDesign Household := rfl

theorem version_design_correspondence (v : Fin 3) (hv : v = 1 ∨ v = 2) :
    toAudit (oneVersionTreated v hv) = AronowAudit.P061.versionDesign v hv := rfl

end SAP.P061b.Bridge
