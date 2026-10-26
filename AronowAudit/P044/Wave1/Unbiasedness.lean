import AronowAudit.P044.Wave1.UnbiasednessBlueprint
import AronowAudit.P044.Wave1.Unbiasedness.N1
import AronowAudit.P044.Wave1.Unbiasedness.N2

namespace AronowAudit.P044.Wave1

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- The printed unbiasedness proposition fails on the four-unit star. -/
theorem printed_unbiasedness_claim_refuted : ¬ PrintedUnbiasedness :=
  AronowAudit.P044.Wave1.Unbiasedness.assemble
    AronowAudit.P044.Wave1.Unbiasedness.n1_proof
    AronowAudit.P044.Wave1.Unbiasedness.n2_proof

end

end AronowAudit.P044.Wave1
