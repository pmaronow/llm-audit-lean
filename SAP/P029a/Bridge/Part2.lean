import SAP.P029a.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace SAP.P029a.Bridge

open SAP.P029a MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology

noncomputable section

theorem proveFivePerArmBiasFacts : FivePerArmBiasFacts := by
  exact @AronowAudit.P029.five_per_arm_bias_counterexample

theorem proveSaturatedBiasWitnessFacts : SaturatedBiasWitnessFacts := by
  exact @AronowAudit.P029.saturated_ml_bias_full_counterexample

theorem proveSaturatedScoreBiasFacts : SaturatedScoreBiasFacts := by
  exact @AronowAudit.P029.saturated_unbiasedness_counterexample

end
end SAP.P029a.Bridge
