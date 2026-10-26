import AronowAudit.P011.Wave1.PropositionOneBlueprint
import AronowAudit.P011.Wave1.PropositionOne.N1
import AronowAudit.P011.Wave1.PropositionOne.N2
import AronowAudit.P011.Wave1.PropositionOne.N3
import AronowAudit.P011.Wave1.PropositionOne.N4
import AronowAudit.P011.Wave1.PropositionOne.N5
import AronowAudit.P011.Wave1.PropositionOne.N6
import AronowAudit.P011.Wave1.PropositionOne.N7
import AronowAudit.P011.Wave1.PropositionOne.N8
import AronowAudit.P011.Wave1.PropositionOne.N9
import AronowAudit.P011.Wave1.PropositionOne.N10
import AronowAudit.P011.Wave1.PropositionOne.N11

set_option autoImplicit false

namespace AronowAudit.P011.Wave1

open AronowAudit.P011 MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

theorem printed_proposition_one_refuted :
    ¬ ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 →
      InProbability F (scaledOracle F) (scaledTrue F) :=
  PropositionOne.assemble PropositionOne.n1_proof PropositionOne.n2_proof
    PropositionOne.n3_proof PropositionOne.n4_proof PropositionOne.n5_proof
    PropositionOne.n6_proof PropositionOne.n7_proof PropositionOne.n8_proof
    PropositionOne.n9_proof PropositionOne.n10_proof PropositionOne.n11_proof


end

end AronowAudit.P011.Wave1
