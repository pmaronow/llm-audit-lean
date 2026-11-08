import AronowAudit.P022.Wave1.PrintedLemma2Blueprint

/-!
# P022-T18, node N1 (trivial; written by the blueprint architect)

Specialize the universal printed contract to the proved reciprocal witness and contradict
the final conjunct of `AronowAudit.P022.lemma2_counterexample`.
-/

set_option autoImplicit false

namespace AronowAudit.P022.Wave1.PrintedLemma2

open AronowAudit.P022

theorem n1_proof : N1 := fun h =>
  lemma2_counterexample.2.2.2.2 (h _ _ _ _ lemma2_counterexample.1)

end AronowAudit.P022.Wave1.PrintedLemma2
