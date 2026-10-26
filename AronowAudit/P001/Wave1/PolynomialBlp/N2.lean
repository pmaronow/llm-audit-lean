import AronowAudit.P001.Wave1.PolynomialBlpBlueprint

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.PolynomialBlp

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- CEF orthogonality kills the cross term in the finite squared-risk identity. -/
theorem n2_proof : N2.{u} := by
  intro Ω _ μ _ X Y m hX hY hm hm2 g hg hg2
  let R : Ω → ℝ := fun ω => Y ω - m (X ω)
  let D : Ω → ℝ := fun ω => m (X ω) - g (X ω)
  have hR2 : MemLp R 2 μ := hY.sub hm2
  have hD2 : MemLp D 2 μ := hm2.sub hg2
  obtain ⟨-, hmean, horth⟩ :=
    cef_residual_orthogonality_correction μ X hX Y hY m hm hm2
  change mean μ R = 0 at hmean
  have hO := horth (fun x => m x - g x) (hm.1.sub hg) hD2
  change covariance D R μ = 0 at hO
  rw [covariance_eq_sub hD2 hR2] at hO
  have hDR0 : mean μ (fun ω => D ω * R ω) = 0 := by
    change mean μ (fun ω => D ω * R ω) - mean μ D * mean μ R = 0 at hO
    simpa [hmean] using hO
  have hfun : (fun ω => (Y ω - g (X ω)) ^ 2) =
      (fun ω => (R ω) ^ 2 + (2 * (D ω * R ω) + (D ω) ^ 2)) := by
    funext ω
    dsimp [R, D]
    ring
  have hDRi : Integrable (fun ω => D ω * R ω) μ := hD2.integrable_mul hR2
  have h2DRi : Integrable (fun ω => 2 * (D ω * R ω)) μ := hDRi.const_mul 2
  have hDsqi : Integrable (fun ω => (D ω) ^ 2) μ := hD2.integrable_sq
  have hsumi : Integrable (fun ω => 2 * (D ω * R ω) + (D ω) ^ 2) μ :=
    h2DRi.add hDsqi
  rw [hfun]
  unfold mean
  rw [integral_add hR2.integrable_sq hsumi, integral_add h2DRi hDsqi,
    integral_const_mul]
  change mean μ (fun ω => (R ω) ^ 2) +
      (2 * mean μ (fun ω => D ω * R ω) + mean μ (fun ω => (D ω) ^ 2)) =
    mean μ (fun ω => (R ω) ^ 2) + mean μ (fun ω => (D ω) ^ 2)
  rw [hDR0]
  ring

end

end AronowAudit.P001.Wave1.PolynomialBlp
