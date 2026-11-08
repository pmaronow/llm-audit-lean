import SAP.P026a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000

open Finset
open scoped BigOperators

namespace SAP.P026a.WH.W2.P.T7_L7

open SAP.P026a
open SAP.P026a.WH.W2

/-- The exact IPW contrast on each of the ninety allocations. -/
def ipwCache : Fin 6 → Fin 15 → ℚ := ![
  ![10/23, 10/23, 11/130, 11/130, 11/130, 8/13, 134/493, 134/493, 134/493, 134/493, 134/493, 134/493, -13/112, -13/112, -13/112],
  ![64/189, 64/189, 0, 0, 0, 8/15, 32/165, 32/165, 32/165, 32/165, 32/165, 32/165, -2/9, -2/9, -2/9],
  ![2/21, 2/21, -11/45, -11/45, -11/45, 13/45, -2/33, -2/33, -2/33, -2/33, -2/33, -2/33, -1/2, -1/2, -1/2],
  ![64/189, 64/189, 0, 0, 0, 8/15, 32/165, 32/165, 32/165, 32/165, 32/165, 32/165, -2/9, -2/9, -2/9],
  ![2/21, 2/21, -11/45, -11/45, -11/45, 13/45, -2/33, -2/33, -2/33, -2/33, -2/33, -2/33, -1/2, -1/2, -1/2],
  ![16/589, 16/589, -11/34, -11/34, -11/34, 31/136, -68/481, -68/481, -68/481, -68/481, -68/481, -68/481, -13/20, -13/20, -13/20]
]

theorem ipwCache_correct : ∀ w : W2Allocation, w2IPWEstimate w = ipwCache w.1 w.2 := by
  intro w
  rcases w with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem ipw_mean_exact : mean paperTableDesign w2IPWEstimate =
    -62426957416097/4371489373960800 := by
  simp only [mean, paperTableDesign]
  simp_rw [ipwCache_correct]
  decide +kernel

theorem ipw_variance_exact : designVariance paperTableDesign w2IPWEstimate =
    13596002132077280844902048265137/177869249303454972322974794880000 := by
  unfold designVariance designCovariance
  simp only [mean, paperTableDesign]
  simp_rw [ipwCache_correct]
  decide +kernel

end SAP.P026a.WH.W2.P.T7_L7

theorem SAP.P026a.WH.W2.T7_L7_proof : SAP.P026a.WH.W2.T7_L7 := by
  unfold SAP.P026a.WH.W2.T7_L7 SAP.P026a.w2ATECertificate
  rw [SAP.P026a.WH.W2.P.T7_L7.ipw_mean_exact,
    SAP.P026a.WH.W2.P.T7_L7.ipw_variance_exact]
  norm_num [SAP.P026a.roundsToThree, SAP.P026a.sdRoundsToThree]
