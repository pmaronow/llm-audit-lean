import SAP.P029b.Defs
import AronowAudit.P029.P029_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.Bridge

open scoped BigOperators

/-- The supplied arrays have exactly the same empirical RMSE in both formulations. -/
theorem empiricalRMSE_eq {R : ℕ} (t b : Fin R → ℝ) :
    empiricalRMSE t b = AronowAudit.P029.rmse t b := rfl

/-- The credited row records the scoring rule with the benchmark supplied as five. -/
theorem homogeneous_rmse_rule (t : Fin 2500 → ℝ) :
    empiricalRMSE t (fun _ => 5) =
      Real.sqrt ((∑ r, (t r - 5) ^ 2) / (2500 : ℝ)) := by
  rw [empiricalRMSE_eq]
  exact AronowAudit.P029.homogeneous_rmse_rule t

end SAP.P029b.Bridge
