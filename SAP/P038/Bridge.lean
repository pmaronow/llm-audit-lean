import SAP.P038.Defs
import AronowAudit.P038.P038_EmpiricalNullCorrection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P038.Bridge

theorem referenceWeeks_eq (m : ℕ) :
    SAP.P038.referenceWeeks m = AronowAudit.P038.referenceWeeks m := rfl

theorem moreExtreme_eq (R x : ℝ) :
    SAP.P038.moreExtreme R x = AronowAudit.P038.moreExtreme R x := rfl

theorem tailWeeks_eq (R : ℝ) (r : ℤ → ℝ) (m : ℕ) :
    SAP.P038.tailWeeks R r m = AronowAudit.P038.tailWeeks R r m := rfl

theorem tailCount_eq (R : ℝ) (r : ℤ → ℝ) (m : ℕ) :
    SAP.P038.tailCount R r m = AronowAudit.P038.tailCount R r m := rfl

theorem empiricalP_eq (R : ℝ) (r : ℤ → ℝ) (m : ℕ) :
    SAP.P038.empiricalP R r m = AronowAudit.P038.empiricalP R r m := rfl

theorem roundsTo_eq (x v : ℝ) :
    SAP.P038.roundsTo x v = AronowAudit.P038.roundsTo x v := rfl

theorem electionDayAdjustedP_eq (R : ℝ) (r : ℤ → ℝ) (m : ℕ) :
    SAP.P038.electionDayAdjustedP R r m =
      AronowAudit.P038.electionDayAdjustedP R r m := rfl

end SAP.P038.Bridge
