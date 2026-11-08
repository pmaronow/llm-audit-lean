import AronowAudit.P017.Wave1.PropositionOneBlueprint

set_option autoImplicit false

namespace AronowAudit.P017.Wave1.PropositionOne

open AronowAudit.P017 MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

theorem n7_proof : N7 := by
  intro h1 h3 n hn s hs
  have hμ : populationMean ipwPopulation ipwEffect = 1 / 2 := h1.2.2
  have hx : sampleMean ipwSummand n s = 2 := by
    simpa using ipw_bad_event_estimator (-1) n hn s hs
  change 1 ≤ clipTarget (populationMean ipwPopulation ipwEffect)
    (effectRadius ipwPopulation ipwEffect) (sampleMean ipwSummand n s)
  rw [hμ, hx]
  by_cases hc : effectRadius ipwPopulation ipwEffect = ⊤
  · norm_num [clipTarget, hc]
  · have hcR : (1 / 2 : ℝ) ≤ (effectRadius ipwPopulation ipwEffect).toReal := by
      simpa using ENNReal.toReal_mono hc h3
    simp only [clipTarget, hc, ↓reduceIte, clipReal, le_min_iff]
    exact ⟨by linarith, (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_right _ _)⟩

end

end AronowAudit.P017.Wave1.PropositionOne
