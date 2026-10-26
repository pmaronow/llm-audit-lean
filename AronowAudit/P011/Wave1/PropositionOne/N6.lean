import AronowAudit.P011.Wave1.PropositionOneBlueprint
import AronowAudit.P011.P011_StarCompletion

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PropositionOne

open AronowAudit.P011 MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

theorem n6_proof : N6 := by
  classical
  intro k i
  change Fin (3 * (k + 1)) at i
  change (degree (blockGraph (by decide) pathGraph (k + 1)) i : ℝ) ≤ 2
  rw [StarCompletion.block_degree]
  have hdegree : ∀ r : Fin 3, degree pathGraph r ≤ 2 := by decide
  exact_mod_cast hdegree (localIndex (by decide : 0 < 3) i)

end

end AronowAudit.P011.Wave1.PropositionOne
