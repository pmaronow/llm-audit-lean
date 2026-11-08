import SAP.P026a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P026a.WH.W1.P.T1_L2

open Finset
open scoped BigOperators

def marginalTable (a : Bool) (i : Fin 6) : ℚ :=
  if a then (![2/7, 5/7, 1/2, 1/2, 1/2, 1/2] : Fin 6 → ℚ) i
  else (![5/7, 2/7, 1/2, 1/2, 1/2, 1/2] : Fin 6 → ℚ) i

def jointTable (a b : Bool) (i j : Fin 6) : ℚ :=
  if a then
    if b then
      (![![4/14,4/14,1/14,1/14,1/14,1/14],
          ![4/14,10/14,4/14,4/14,4/14,4/14],
          ![1/14,4/14,7/14,3/14,3/14,3/14],
          ![1/14,4/14,3/14,7/14,3/14,3/14],
          ![1/14,4/14,3/14,3/14,7/14,3/14],
          ![1/14,4/14,3/14,3/14,3/14,7/14]] : Fin 6 → Fin 6 → ℚ) i j
    else
      (![![0,0,3/14,3/14,3/14,3/14],
          ![6/14,0,6/14,6/14,6/14,6/14],
          ![6/14,3/14,0,4/14,4/14,4/14],
          ![6/14,3/14,4/14,0,4/14,4/14],
          ![6/14,3/14,4/14,4/14,0,4/14],
          ![6/14,3/14,4/14,4/14,4/14,0]] : Fin 6 → Fin 6 → ℚ) i j
  else if b then
    (![![0,6/14,6/14,6/14,6/14,6/14],
        ![0,0,3/14,3/14,3/14,3/14],
        ![3/14,6/14,0,4/14,4/14,4/14],
        ![3/14,6/14,4/14,0,4/14,4/14],
        ![3/14,6/14,4/14,4/14,0,4/14],
        ![3/14,6/14,4/14,4/14,4/14,0]] : Fin 6 → Fin 6 → ℚ) i j
  else
    (![![10/14,4/14,4/14,4/14,4/14,4/14],
        ![4/14,4/14,1/14,1/14,1/14,1/14],
        ![4/14,1/14,7/14,3/14,3/14,3/14],
        ![4/14,1/14,3/14,7/14,3/14,3/14],
        ![4/14,1/14,3/14,3/14,7/14,3/14],
        ![4/14,1/14,3/14,3/14,3/14,7/14]] : Fin 6 → Fin 6 → ℚ) i j

theorem marginal_cached (a : Bool) (i : Fin 6) :
    inclusion asymmetricSixLaw a i = marginalTable a i := by
  cases a <;> fin_cases i <;> decide +kernel

theorem joint_cached (a b : Bool) (i j : Fin 6) :
    jointInclusion asymmetricSixLaw a b i j = jointTable a b i j := by
  cases a <;> cases b <;> fin_cases i <;> fin_cases j <;> decide +kernel

theorem ht_values (w : Fin 14) :
    htContrast asymmetricSixLaw 6 (fun _ => 1) (fun _ => 1) w =
      (![-3/20,0,3/20] : Fin 3 → ℚ) (w1SixGroup w) := by
  fin_cases w <;>
    simp only [htContrast, htSum, armIndicator, marginal_cached] <;>
    simp only [asymmetricSixLaw, SAP.P026a.w1SixGroup] <;>
    decide +kernel

theorem variance_values (w : Fin 14) :
    printedVarianceEstimate asymmetricSixLaw 6 (fun _ => 1) (fun _ => 1) w =
      (![-619/3600,7/54,-619/3600] : Fin 3 → ℚ) (w1SixGroup w) := by
  fin_cases w <;>
    simp only [printedVarianceEstimate, estimatedPairTerm, zeroAdjustment,
      orderedOffDiagonalSum, unavailablePairSum, armIndicator, response,
      marginal_cached, joint_cached] <;>
    simp only [asymmetricSixLaw, SAP.P026a.w1SixGroup] <;>
    decide +kernel

end SAP.P026a.WH.W1.P.T1_L2

theorem SAP.P026a.WH.W1.T1_L2_proof : SAP.P026a.WH.W1.T1_L2 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · intro w
    exact ⟨SAP.P026a.WH.W1.P.T1_L2.ht_values w,
      SAP.P026a.WH.W1.P.T1_L2.variance_values w⟩
  · unfold SAP.P026a.mean
    simp_rw [SAP.P026a.WH.W1.P.T1_L2.ht_values]
    simp only [SAP.P026a.asymmetricSixLaw, SAP.P026a.w1SixGroup]
    decide +kernel
