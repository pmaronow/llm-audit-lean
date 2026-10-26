import AronowAudit.P011.Wave1.CorollaryOneBlueprint
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
import AronowAudit.P011.Wave1.CorollaryOne.N1
import AronowAudit.P011.Wave1.CorollaryOne.N2
import AronowAudit.P011.Wave1.CorollaryOne.N3

set_option autoImplicit false

namespace AronowAudit.P011.Wave1

open AronowAudit.P011 AronowAudit.P011.Wave1.PropositionOne MeasureTheory ProbabilityTheory
  Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- Refutation of printed Corollary 1 (P011-T32). -/
theorem printed_corollary_one_refuted :
  ¬ ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 → Valid F →
      ∀ (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)),
        (∀ k y, Maximizes (F.model k).R (F.model k).d
          (fun B => V1 B (weighted (F.model k) y)) (A k y)) →
        Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)) ∧
          ((∀ k, Homoskedastic (F.model k)) →
            Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y))) := by
  exact AronowAudit.P011.Wave1.CorollaryOne.assemble
    AronowAudit.P011.Wave1.PropositionOne.n1_proof
    AronowAudit.P011.Wave1.PropositionOne.n2_proof
    AronowAudit.P011.Wave1.PropositionOne.n3_proof
    AronowAudit.P011.Wave1.PropositionOne.n4_proof
    AronowAudit.P011.Wave1.PropositionOne.n5_proof
    AronowAudit.P011.Wave1.PropositionOne.n6_proof
    AronowAudit.P011.Wave1.PropositionOne.n7_proof
    AronowAudit.P011.Wave1.PropositionOne.n8_proof
    AronowAudit.P011.Wave1.PropositionOne.n9_proof
    AronowAudit.P011.Wave1.PropositionOne.n10_proof
    AronowAudit.P011.Wave1.CorollaryOne.n1_proof
    AronowAudit.P011.Wave1.CorollaryOne.n2_proof
    AronowAudit.P011.Wave1.CorollaryOne.n3_proof

end

end AronowAudit.P011.Wave1
