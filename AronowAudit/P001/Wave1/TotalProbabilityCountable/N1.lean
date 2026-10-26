import AronowAudit.P001.Wave1.TotalProbabilityCountableBlueprint

/-! P001-T24:
binary complement additivity `P(B) = P(B ∩ C) + P(B ∩ Cᶜ)` for measurable `C`. -/

namespace AronowAudit.P001.Wave1.TotalProbabilityCountable

open AronowAudit.P001 MeasureTheory

theorem n1_proof : N1 := by
  intro Ω _ μ _ B C hC
  rw [prob, prob, prob, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ← Set.sdiff_eq, measure_inter_add_sdiff B hC]

end AronowAudit.P001.Wave1.TotalProbabilityCountable
