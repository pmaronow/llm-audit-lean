import AronowAudit.P027.Wave1.CancellationLimitBlueprint

/-! Integrability and expectation of the squared normalized phase-noise norm. -/

namespace AronowAudit.P027.Wave1.CancellationLimit

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
attribute [local instance] Classical.propDecidable

theorem n3_proof : N3 := by
  intro Ξ _ μ _ r m hr hm σ2 ε hε
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcoord (g : Fin r × Fin 2) :
      Integrable (fun ξ => (noise r m ε ξ g)^2) μ ∧
      (∫ ξ, (noise r m ε ξ g)^2 ∂μ) =
        σ2 * (m : ℝ) * (1 - 1 / (2 * (r : ℝ))) / ((m : ℝ) * (2 * r))^2 := by
    have hlin := noise_linear_moments μ ε σ2 hε (phaseNoiseCoeff g) 0
    dsimp only at hlin
    have hint : Integrable
        (fun ξ => (∑ k : Σ _ : Fin r × Fin 2, Fin m,
          phaseNoiseCoeff g k * ε k ξ)^2) μ := hlin.2.2.1
    have hmean : (∫ ξ, (∑ k : Σ _ : Fin r × Fin 2, Fin m,
          phaseNoiseCoeff g k * ε k ξ)^2 ∂μ) =
        σ2 * (m : ℝ) * (1 - 1 / (2 * (r : ℝ))) := by
      change outcomeE μ (fun ξ => (∑ k : Σ _ : Fin r × Fin 2, Fin m,
        phaseNoiseCoeff g k * ε k ξ)^2) = _
      rw [hlin.2.2.2.1, phase_noise_coeff_square_sum r m hr hm]
      ring
    constructor
    · simpa only [noise, div_pow] using hint.div_const (((m : ℝ) * (2 * r))^2)
    · simp only [noise, div_pow]
      rw [integral_div, hmean]
  refine ⟨integrable_finsetSum _ (fun g _ => (hcoord g).1), ?_⟩
  rw [integral_finsetSum _ (fun g _ => (hcoord g).1)]
  simp_rw [fun g => (hcoord g).2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hrR, hmR] <;> ring

end
end AronowAudit.P027.Wave1.CancellationLimit
