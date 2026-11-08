import SAP.P027a.Defs
import AronowAudit.P027.P027_Audit
import AronowAudit.P027.Wave1.Gap.GLP027P016P031B1
import AronowAudit.P027.Wave1.Gap.T2Conjunction
import AronowAudit.P027.Wave1.AePartition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a.Bridge

noncomputable section
open scoped BigOperators

variable {U Ω : Type} [Fintype U] [Fintype Ω]

/-- Add the normalization certificate to the shared sample data. -/
def toAudit (D : SAP.P027a.Design U Ω) (hD : SAP.P027a.Valid D) :
    AronowAudit.P027.Design U Ω where
  weight := D.weight
  nonneg := hD.1
  total := hD.2
  selected := D.selected

/-- Forget only proof fields; all sample data are retained. -/
def fromAudit (D : AronowAudit.P027.Design U Ω) : SAP.P027a.Design U Ω where
  weight := D.weight
  selected := D.selected

theorem valid_fromAudit (D : AronowAudit.P027.Design U Ω) :
    SAP.P027a.Valid (fromAudit D) := ⟨D.nonneg, D.total⟩

theorem expect_eq (D : SAP.P027a.Design U Ω) (hD : SAP.P027a.Valid D) (f : Ω → ℝ) :
    SAP.P027a.expect D f = AronowAudit.P027.expect (toAudit D hD) f := rfl

theorem pi_eq (D : SAP.P027a.Design U Ω) (hD : SAP.P027a.Valid D) (k : U) :
    SAP.P027a.pi D k = AronowAudit.P027.pi (toAudit D hD) k := rfl

theorem joint_eq (D : SAP.P027a.Design U Ω) (hD : SAP.P027a.Valid D) (k l : U) :
    SAP.P027a.joint D k l = AronowAudit.P027.joint (toAudit D hD) k l := rfl

theorem total_eq (D : SAP.P027a.Design U Ω) (hD : SAP.P027a.Valid D) (y : U → ℝ) :
    SAP.P027a.htTotal D y = AronowAudit.P027.htTotal (toAudit D hD) y := rfl

theorem variance_eq (D : SAP.P027a.Design U Ω) (hD : SAP.P027a.Valid D) (f : Ω → ℝ) :
    SAP.P027a.variance D f = AronowAudit.P027.variance (toAudit D hD) f := rfl

theorem estimator_eq (D : SAP.P027a.Design U Ω) (hD : SAP.P027a.Valid D) (y : U → ℝ) :
    SAP.P027a.htVarianceEstimator D y =
      AronowAudit.P027.htVarianceEstimator (toAudit D hD) y := rfl

theorem bias_eq (D : SAP.P027a.Design U Ω) (hD : SAP.P027a.Valid D) (y : U → ℝ) :
    SAP.P027a.biasA D y = AronowAudit.P027.biasA (toAudit D hD) y := rfl

theorem correction_eq (D : SAP.P027a.Design U Ω) (hD : SAP.P027a.Valid D) (y : U → ℝ) :
    SAP.P027a.quadraticCorrection D y =
      AronowAudit.P027.quadraticCorrection (toAudit D hD) y := rfl

theorem c2_eq (D : SAP.P027a.Design U Ω) (hD : SAP.P027a.Valid D) (y : U → ℝ) :
    SAP.P027a.c2Estimator D y = AronowAudit.P027.c2Estimator (toAudit D hD) y := rfl

theorem periodic8_eq : SAP.P027a.periodic8 = fromAudit AronowAudit.P027.periodic8 := rfl

theorem random8_eq : SAP.P027a.random8 = fromAudit AronowAudit.P027.random8 := rfl

theorem grouped_eq (r : ℕ) (hr : 0 < r) :
    SAP.P027a.phaseGrouped r hr = fromAudit (AronowAudit.P027.phaseGrouped r hr) := rfl

theorem original_eq (r m : ℕ) (hr : 0 < r) :
    SAP.P027a.phaseOriginal r m hr =
      fromAudit (AronowAudit.P027.phaseOriginal r m hr) := rfl

theorem calibrated_eq : @SAP.P027a.calibratedMeanBias =
    @AronowAudit.P027.calibratedMeanBias := rfl

/-- The SAP finite phase law has exactly the audit's sample data. -/
theorem periodic_inclusions : SAP.P027a.PeriodicInclusions := by
  intro r m hr
  have h := AronowAudit.P027.phase_inclusions r m hr
  exact ⟨valid_fromAudit (AronowAudit.P027.phaseOriginal r m hr),
    AronowAudit.P027.phaseOriginal_positive r m hr,
    h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end
end SAP.P027a.Bridge
