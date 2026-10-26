import AronowAudit.P011.Wave1.CorollaryOneBlueprint
import AronowAudit.P011.P011_StarCompletion

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.CorollaryOne

open AronowAudit.P011 AronowAudit.P011.Wave1.PropositionOne MeasureTheory ProbabilityTheory
  Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- All forced path edges already exhaust the supplied degree caps. -/
theorem n1_proof : N1 := by
  intro k B
  have hd : (PF.model k).d = degree (PF.model k).G := by
    funext i
    exact (StarCompletion.block_degree (by decide) pathGraph i).symm
  have hR : (PF.model k).R = (PF.model k).G := rfl
  rw [hR, hd]
  exact saturated_graph_singleton (PF.model k).G B

end

end AronowAudit.P011.Wave1.CorollaryOne
