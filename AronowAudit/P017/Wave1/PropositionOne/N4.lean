import AronowAudit.P017.Wave1.PropositionOne.N1

set_option autoImplicit false

namespace AronowAudit.P017.Wave1.PropositionOne

open AronowAudit.P017 MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

theorem n4_proof : N4 := by
  have hmap : ∀ᵐ u ∂ipwPopulation.map Prod.fst, u < (1 : ℝ) := by
    rw [fst_law]
    exact uniform_mem.mono fun u hu => hu.2
  have hf : ∀ᵐ ω ∂ipwPopulation, ω.1 < (1 : ℝ) :=
    ae_of_ae_map measurable_fst.aemeasurable hmap
  change ∀ᵐ ω ∂ipwPopulation, ipwEffect ω < 1
  simpa only [effect_eq_fst] using hf

end

end AronowAudit.P017.Wave1.PropositionOne
