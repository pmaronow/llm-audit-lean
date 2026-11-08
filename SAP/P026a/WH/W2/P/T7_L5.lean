import SAP.P026a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a.WH.W2.P.T7_L5

open Finset
open scoped BigOperators

/-- The checked equation [35] value at each of the ninety allocations. -/
def htVarianceCertificate (w : SAP.P026a.W2Allocation) : ℚ :=
  if (w.1.val = 0 ∨ w.1.val = 5) then
    if (w.2.val = 0 ∨ w.2.val = 1 ∨ w.2.val = 5 ∨
        w.2.val = 12 ∨ w.2.val = 13 ∨ w.2.val = 14) then 33/256 else 13/64
  else
    if (w.2.val = 0 ∨ w.2.val = 1 ∨ w.2.val = 5 ∨
        w.2.val = 12 ∨ w.2.val = 13 ∨ w.2.val = 14) then 37/256 else 7/32

theorem ht_variance_certificate : ∀ w, SAP.P026a.w2HTVariance w = htVarianceCertificate w := by
  change ∀ w, AronowAudit.P026.printedVariance AronowAudit.P026.tableDesign 16
    AronowAudit.P026.tableClusterY AronowAudit.P026.tableClusterY w = htVarianceCertificate w
  simp only [AronowAudit.P026.printedVariance, AronowAudit.P026.estimatedPair,
    AronowAudit.P026.zeroSum, AronowAudit.P026.table_marginal,
    AronowAudit.P026.table_joint, AronowAudit.P026.observed, ite_self,
    htVarianceCertificate]
  decide +kernel

end SAP.P026a.WH.W2.P.T7_L5

theorem SAP.P026a.WH.W2.T7_L5_proof : SAP.P026a.WH.W2.T7_L5 := by
  unfold SAP.P026a.WH.W2.T7_L5 SAP.P026a.designVariance
    SAP.P026a.designCovariance SAP.P026a.mean
  simp_rw [SAP.P026a.WH.W2.P.T7_L5.ht_variance_certificate]
  simp only [SAP.P026a.WH.W2.P.T7_L5.htVarianceCertificate,
    SAP.P026a.paperTableDesign]
  decide +kernel
