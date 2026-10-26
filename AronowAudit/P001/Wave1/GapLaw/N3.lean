import AronowAudit.P001.Wave1.GapLawBlueprint
import AronowAudit.P001.Wave1.GapLaw.N1
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.GapLaw

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

noncomputable section

theorem n3_proof : N3 := by
  classical
  intro h1 h2
  obtain ⟨hprob, hXint, hYint, hXmean, hYmean, hXsupport, hYsupport⟩ := h1
  letI : IsProbabilityMeasure gapJointLaw := hprob
  letI : IsProbabilityMeasure gapMarginal := gap_marginal_probability
  letI : IsProbabilityMeasure (uniformLaw (-1) 1) := gap_uniform_probability
  have hset (A : Set ℝ) (hA : MeasurableSet A) :
      (∫ ω in Prod.fst ⁻¹' A, ω.2 ∂gapJointLaw) = 0 := by
    have he : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set ℝ) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    rw [he]
    change (∫ ω in A ×ˢ Set.univ, ω.2
      ∂gapMarginal.prod (uniformLaw (-1) 1)) = 0
    rw [setIntegral_prod Prod.snd (hYint.integrableOn)]
    simp only [Measure.restrict_univ, gap_uniform_mean, integral_zero]
  have hb0 : (fun ω : ℝ × ℝ => pdaBump ω.1) =ᵐ[gapJointLaw]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hXsupport] with ω hω
    exact h2.2.1 ω.1 hω.1
  have hbint : Integrable (pdaBump ∘ Prod.fst) gapJointLaw :=
    (integrable_const (0 : ℝ)).congr hb0.symm
  have hcef0 : IsCEF gapJointLaw Prod.fst Prod.snd (fun _ => 0) := by
    refine ⟨measurable_const, hYint, integrable_const 0, fun A hA => ?_⟩
    rw [hset A hA]
    simp only [integral_zero]
  have hcefb : IsCEF gapJointLaw Prod.fst Prod.snd pdaBump := by
    refine ⟨h2.1.continuous.measurable, hYint, hbint, fun A hA => ?_⟩
    rw [hset A hA, integral_congr_ae (ae_restrict_of_ae hb0), integral_zero]
  exact ⟨hcef0, hcefb⟩

end

end AronowAudit.P001.Wave1.GapLaw
