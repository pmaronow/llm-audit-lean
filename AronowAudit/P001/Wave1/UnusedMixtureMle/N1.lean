import AronowAudit.P001.Wave1.UnusedMixtureMleBlueprint

/-!
# Node UnusedMixtureMle.N1 (proved by the blueprint author; one term)

Chooses, for every sample size and sample, a likelihood maximizer on the compact box given
by the proved `finite_mixture_compact_attainment` (P001_Foundations.lean:7241).
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.UnusedMixtureMle

open AronowAudit.P001

theorem n1_proof : N1 :=
  ⟨fun n y => (finite_mixture_compact_attainment.2.2.2 n y).2.choose,
    fun n y => (finite_mixture_compact_attainment.2.2.2 n y).2.choose_spec⟩

end AronowAudit.P001.Wave1.UnusedMixtureMle
