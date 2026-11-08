import AronowAudit.P006.P006_CounterfactualMetrics

open scoped BigOperators
open Filter
noncomputable section
attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace AronowAudit.P006.ConfidenceFollowup02

/-- The exact conditional reporting contract fails on satisfiable source inputs. -/
theorem T28_printed_beneficiary_report_refuted :
    ¬ (∀ vH bH vS bS : ℝ,
      293907/2000000 ≤ vH → vH ≤ 293909/2000000 → bH = vH*(255/62) →
      50371/2000000 ≤ vS → vS ≤ 50373/2000000 → bS = vS*(7264/1360) →
      293/2000 ≤ bH ∧ bH < 295/2000 ∧ 49/2000 ≤ bS ∧ bS < 51/2000) := by
  intro h
  have hh := h (293908/2000000) ((293908/2000000)*(255/62))
    (50372/2000000) ((50372/2000000)*(7264/1360))
    (by norm_num) (by norm_num) rfl (by norm_num) (by norm_num) rfl
  norm_num at hh

end AronowAudit.P006.ConfidenceFollowup02

#print axioms AronowAudit.P006.ConfidenceFollowup02.T28_printed_beneficiary_report_refuted
