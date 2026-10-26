import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint
import Mathlib.Tactic.FinCases

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Each finite check counts a single exposure at a single unit in 66 profiles. -/
theorem n2_proof : N2 := by
  change ∀ (i : Fin 12) (a : Exposure),
    exposureCount cliqueF i a = cliqueFullCount a
  intro i a
  -- These finite checks use computational decidability.
  fin_cases i <;> cases a <;> decide +kernel

end

end AronowAudit.P044.Wave1.SimulatedVariance
