import AronowAudit.P022.Wave1.PrintedLemma2Blueprint
import AronowAudit.P022.Wave1.PrintedLemma2.N1

set_option autoImplicit false

namespace AronowAudit.P022.Wave1
open AronowAudit.P022

theorem lemma2_as_printed_refuted :
    ¬ ∀ (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ),
      Conditions123 S H θ ρ → Lemma2Conclusions S H θ ρ :=
  PrintedLemma2.n1_proof

end AronowAudit.P022.Wave1
