import SAP.P020.Defs.WholeW2
import AronowAudit.P020.P020_Logistic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P020.WH.W2

/-- All analytic clauses already have project proofs. Assemble those proofs and
restore the scalar instance, using rational arithmetic to identify its treated
predictor with -1/2. No new mathematical leaves are needed. -/
theorem T3_assembly : T3WholeStatement_W2 := by
  refine ⟨AronowAudit.P020.logistic_strictMono,
    AronowAudit.P020.printed_contrast_bound,
    AronowAudit.P020.printed_model_unit_negative,
    AronowAudit.P020.printed_model_average_negative,
    AronowAudit.P020.printed_model_average_ne_reported, ?_⟩
  obtain ⟨hcontrol, htreated, _⟩ := AronowAudit.P020.logistic_concrete_counterexample
  refine ⟨hcontrol, ?_, htreated⟩
  congr 1
  norm_num

end SAP.P020.WH.W2
