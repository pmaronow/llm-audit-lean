import SAP.P028.Defs
import AronowAudit.P028.P028_Results
import AronowAudit.P028.P028_MissingOutcomes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028.Bridge
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Copies the same data and evidence; every scalar quantity agrees by reduction. -/
def toAudit (M : CausalModel Ω) : AronowAudit.P028.CausalModel Ω where
  μ := M.μ
  probability := M.probability
  S := M.S
  Y := M.Y
  Z := M.Z
  measurableS := M.measurableS
  measurableY := M.measurableY
  integrableY := M.integrableY
  measurableZ := M.measurableZ
  randomAssignment := M.randomAssignment
  armPositive := M.armPositive
  nonzeroFirstStage := M.nonzeroFirstStage

def fromAudit (M : AronowAudit.P028.CausalModel Ω) : CausalModel Ω where
  μ := M.μ
  probability := M.probability
  S := M.S
  Y := M.Y
  Z := M.Z
  measurableS := M.measurableS
  measurableY := M.measurableY
  integrableY := M.integrableY
  measurableZ := M.measurableZ
  randomAssignment := M.randomAssignment
  armPositive := M.armPositive
  nonzeroFirstStage := M.nonzeroFirstStage

def toAuditResponse (T : Response Ω) : AronowAudit.P028.Response Ω where
  R := T.R
  measurableR := T.measurableR

theorem model_roundtrip (M : CausalModel Ω) : fromAudit (toAudit M) = M := rfl

theorem complier_probability (M : CausalModel Ω) :
    AronowAudit.P028.complierProbability (toAudit M) = complierProbability M := rfl

theorem arm_mean (M : CausalModel Ω) (z : Bool) :
    AronowAudit.P028.armMean (toAudit M) z = armMean M z := rfl

theorem complier_mean (M : CausalModel Ω) (d : Bool) :
    AronowAudit.P028.complierMean (toAudit M) d = complierMean M d := rfl

theorem product_moment (M : CausalModel Ω) (d z : Bool) :
    AronowAudit.P028.jointOutcomeMoment (toAudit M) d z = jointOutcomeMoment M d z := rfl

theorem response_mean (M : CausalModel Ω) (T : Response Ω) (z : Bool) :
    AronowAudit.P028.responseArmMean (toAudit M) (toAuditResponse T) z =
      responseArmMean M T z := rfl

def toAuditAtom (a : BinaryAtom) : AronowAudit.P028.BinaryAtom :=
  ⟨a.d0, a.d1, a.y0, a.y1, a.r0, a.r1⟩

def fromAuditAtom (a : AronowAudit.P028.BinaryAtom) : BinaryAtom :=
  ⟨a.d0, a.d1, a.y0, a.y1, a.r0, a.r1⟩

def toAuditLaw (M : BinaryLaw) : AronowAudit.P028.BinaryLaw :=
  ⟨fun i => toAuditAtom (M.atom i), M.mass⟩

def fromAuditLaw (M : AronowAudit.P028.BinaryLaw) : BinaryLaw :=
  ⟨fun i => fromAuditAtom (M.atom i), M.mass⟩

theorem lower_law : toAuditLaw lowerLaw = AronowAudit.P028.lowerLaw := by
  unfold toAuditLaw AronowAudit.P028.lowerLaw
  congr 1
  funext i
  fin_cases i <;> rfl

theorem upper_law : toAuditLaw upperLaw = AronowAudit.P028.upperLaw := by
  unfold toAuditLaw AronowAudit.P028.upperLaw
  congr 1
  funext i
  fin_cases i <;> rfl

theorem finite_observed_law (M : BinaryLaw) :
    AronowAudit.P028.observedLaw (toAuditLaw M) = observedLaw M := rfl

theorem finite_complier_mean (M : BinaryLaw) (d : Bool) :
    AronowAudit.P028.fcy (toAuditLaw M) d = fcy M d := rfl

theorem lower_mean_domain : finiteMeanDomain lowerLaw := by
  constructor
  · intro z; cases z <;>
      norm_num [fprob, lowerLaw, fr, Fin.sum_univ_succ]
  constructor
  · intro d z; cases d <;> cases z <;>
      norm_num [fprob, lowerLaw, fd, Fin.sum_univ_succ]
  · intro d z; cases d <;> cases z <;>
      norm_num [fprob, lowerLaw, fd, fr, Fin.sum_univ_succ]

theorem upper_mean_domain : finiteMeanDomain upperLaw := by
  constructor
  · intro z; cases z <;>
      norm_num [fprob, upperLaw, fr, Fin.sum_univ_succ]
  constructor
  · intro d z; cases d <;> cases z <;>
      norm_num [fprob, upperLaw, fd, Fin.sum_univ_succ]
  · intro d z; cases d <;> cases z <;>
      norm_num [fprob, upperLaw, fd, fr, Fin.sum_univ_succ]

end
end SAP.P028.Bridge
