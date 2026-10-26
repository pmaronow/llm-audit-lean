import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint
import Mathlib.Tactic.FinCases

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- Check all 16 ordered label pairs, with the unit pair fixed before reduction. -/
theorem n3_proof : N3 := by
  change ∀ (i j : Fin 12) (a b : Exposure),
    jointCount cliqueF i j a b =
      cliqueJointTable (decide (i = j)) (decide (i.val / 4 = j.val / 4)) a b
  intro i j
  -- Each fixed unit pair includes all 16 exposure-label pairs.
  -- The 144 checks include the diagonal and every zero entry of the table.
  fin_cases i <;> fin_cases j <;> decide +kernel

end

end AronowAudit.P044.Wave1.SimulatedVariance
