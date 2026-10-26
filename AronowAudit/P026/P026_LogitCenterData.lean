import AronowAudit.P026.P026_FiniteDesign
import AronowAudit.P026.P026_LogitCertificates
/-! Rational center predictions and literal cluster residuals for the actual Table1 population. -/
namespace AronowAudit.P026.LogitCompletion
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 4000
/-- Rational lower centers for the actual opposite-block logistic predictions.
The coordinatewise approximation tolerance for the exact rational-center sigmoid is 1e-12. -/
def logitApproxPrediction : Fin 16 → ℚ := ![47388535877/62500000000,245991334313/1000000000000,47388535877/62500000000,91213999621/250000000000,47388535877/62500000000,502852358951/1000000000000,440210663973/500000000000,787905836173/1000000000000,823519114231/1000000000000,225605980343/250000000000,440210663973/500000000000,787905836173/1000000000000,440210663973/500000000000,823519114231/1000000000000,823519114231/1000000000000,170851719779/200000000000]

/-- Literal cluster sums of printed outcomes minus the rational center predictions. -/
def logitApproxResidual : Fin 10 → ℚ := ![199158418331/200000000000,219231856871/250000000000,15111464123/62500000000,-502852358951/1000000000000,-9836925567/20000000000,108577375341/500000000000,331672835881/1000000000000,-823519114231/1000000000000,-823519114231/1000000000000,-170851719779/200000000000]

lemma logitApproxResidual_aggregation : ∀ k,
    clusterTotal tableCluster (fun i=>tableY i-logitApproxPrediction i) k=logitApproxResidual k := by
  decide +kernel


lemma logitApproxResidual_bound : ∀ k, |logitApproxResidual k|≤(999/1000:ℚ) := by
  decide +kernel

end AronowAudit.P026.LogitCompletion
