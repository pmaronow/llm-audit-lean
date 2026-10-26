import AronowAudit.P001.Wave1.CausalIpwDrBlueprint

set_option autoImplicit false

universe u v w

namespace AronowAudit.P001.Wave1.CausalIpwDr

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n2_proof : N2.{u, v} := by
  intro Ω E _ _ μ _ X D p hp
  have hDi : Integrable (fun ω => 1 - D ω) μ := (integrable_const (1 : ℝ)).sub hp.2.1
  have hpi : Integrable ((fun x => 1 - p x) ∘ X) μ :=
    (integrable_const (1 : ℝ)).sub hp.2.2.1
  refine ⟨measurable_const.sub hp.1, hDi, hpi, ?_⟩
  intro A hA
  calc
    (∫ ω in X ⁻¹' A, 1 - D ω ∂μ) =
        (∫ _ in X ⁻¹' A, (1 : ℝ) ∂μ) - ∫ ω in X ⁻¹' A, D ω ∂μ :=
      integral_sub (integrable_const (1 : ℝ)).integrableOn hp.2.1.integrableOn
    _ = (∫ _ in X ⁻¹' A, (1 : ℝ) ∂μ) - ∫ ω in X ⁻¹' A, p (X ω) ∂μ := by
      rw [hp.2.2.2 A hA]
    _ = ∫ ω in X ⁻¹' A, 1 - p (X ω) ∂μ :=
      (integral_sub (integrable_const (1 : ℝ)).integrableOn hp.2.2.1.integrableOn).symm

end

end AronowAudit.P001.Wave1.CausalIpwDr
