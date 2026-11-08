import SAP.P026a.WH.W2.Leaves
import AronowAudit.P026.P026_FiniteDesign

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open Finset
open scoped BigOperators
open SAP.P026a
open SAP.P026a.WH.W2

namespace SAP.P026a.WH.W2.P.T7_L6

lemma prior_joint (a b : Bool) (i j : Fin 10) :
    jointInclusion paperTableDesign a b i j = AronowAudit.P026.tableJoint a b i j := by
  change AronowAudit.P026.joint AronowAudit.P026.tableDesign a b i j =
    AronowAudit.P026.tableJoint a b i j
  exact AronowAudit.P026.table_joint a b i j

end SAP.P026a.WH.W2.P.T7_L6

open SAP.P026a.WH.W2.P.T7_L6

theorem SAP.P026a.WH.W2.T7_L6_proof : SAP.P026a.WH.W2.T7_L6 := by
  unfold SAP.P026a.WH.W2.T7_L6
  unfold designVariance designCovariance mean w2PriorVariance printedVarianceEstimate
  unfold estimatedPairTerm unavailablePairSum
  simp_rw [cluster_marginal, prior_joint]
  decide +kernel
