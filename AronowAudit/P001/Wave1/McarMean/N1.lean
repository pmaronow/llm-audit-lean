import AronowAudit.P001.Wave1.McarMeanBlueprint

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.McarMean

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n1_proof : N1.{u} := by
  intro Ω _ μ _ Y R hY hR hYi _hbinary _hR0 hR1 hind
  have hc := independent_constant_cef μ R Y hR hY hYi hind.symm
  have hp := hc.2.2.2 ({1} : Set ℝ) (measurableSet_singleton 1)
  have he : (∫ ω in {ω | R ω = 1}, Y ω ∂μ) =
      prob μ {ω | R ω = 1} * mean μ Y := by
    simpa [Set.preimage, integral_const, measureReal_def, prob, smul_eq_mul] using hp
  have hobs : (∫ ω in {ω | R ω = 1}, censored (Y ω) (R ω) ∂μ) =
      ∫ ω in {ω | R ω = 1}, Y ω ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (hR (measurableSet_singleton (1 : ℝ)))] with ω hω
    simp [censored, hω]
  unfold conditionalMeanAt
  rw [hobs, he]
  exact (mul_div_cancel_left₀ _ hR1.ne').symm

end

end AronowAudit.P001.Wave1.McarMean
