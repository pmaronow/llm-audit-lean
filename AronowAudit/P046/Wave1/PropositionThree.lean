import AronowAudit.P046.Wave1.PropositionThreeBlueprint
import AronowAudit.P046.Wave1.PropositionThree.N1
import AronowAudit.P046.Wave1.PropositionThree.N2
import AronowAudit.P046.Wave1.PropositionThree.N3
import AronowAudit.P046.Wave1.PropositionThree.N4
import AronowAudit.P046.Wave1.PropositionThree.N5
import AronowAudit.P046.Wave1.PropositionThree.N6
import AronowAudit.P046.Wave1.PropositionThree.N7

set_option autoImplicit false

namespace AronowAudit.P046.Wave1

open AronowAudit.P046 AronowAudit.P046.IntervalExample MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

noncomputable section

theorem proposition3_printed_refuted :
    ¬ ∀ (M : Study) (_hM : ValidStudy M) (n : ℕ) (_hn : 0 < n) (alpha : ℝ)
      (_ha : 0 < alpha ∧ alpha < 1),
      tailProb M (ht M) (printedRadius M alpha (n := n)) ≤ alpha :=
  PropositionThree.assemble PropositionThree.n1_proof PropositionThree.n2_proof
    PropositionThree.n3_proof PropositionThree.n4_proof PropositionThree.n5_proof
    PropositionThree.n6_proof PropositionThree.n7_proof

end

end AronowAudit.P046.Wave1
