import AronowAudit.P001.Wave1.AteSharpBoundsBlueprint

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.AteSharpBounds

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n1_proof : N1.{u} := by
  classical
  intro Ω _ μ _ Y D hYi hD hbinary hp0 hp1 a b
  let A := {ω | D ω = 1}
  let B := {ω | D ω = 0}
  have hA : MeasurableSet A := hD (measurableSet_singleton 1)
  have hB : MeasurableSet B := hD (measurableSet_singleton 0)
  let u1 : Ω → ℝ := A.indicator Y
  let u0 : Ω → ℝ := B.indicator Y
  let s1 : Ω → ℝ := A.indicator (fun _ => 1)
  let s0 : Ω → ℝ := B.indicator (fun _ => 1)
  have hi1 : Integrable u1 μ := hYi.indicator hA
  have hi0 : Integrable u0 μ := hYi.indicator hB
  have hs1 : Integrable s1 μ := (integrable_const 1).indicator hA
  have hs0 : Integrable s0 μ := (integrable_const 1).indicator hB
  have hmean1 : (∫ ω, s1 ω ∂μ) = prob μ {ω | D ω = 1} := by
    simp [s1, integral_indicator hA, integral_const, measureReal_def, prob, A]
  have hmean0 : (∫ ω, s0 ω ∂μ) = prob μ {ω | D ω = 0} := by
    simp [s0, integral_indicator hB, integral_const, measureReal_def, prob, B]
  have lower_formula (a b : ℝ) :
      mean μ (fun ω => ateLower (Y ω) (D ω) a b) =
        conditionalMeanAt μ D Y 1 * prob μ {ω | D ω = 1} +
          a * prob μ {ω | D ω = 0} -
        (conditionalMeanAt μ D Y 0 * prob μ {ω | D ω = 0} +
          b * prob μ {ω | D ω = 1}) := by
    have he : (fun ω => ateLower (Y ω) (D ω) a b) =ᵐ[μ]
        (fun ω => u1 ω + a * s0 ω - u0 ω - b * s1 ω) := by
      filter_upwards [hbinary] with ω hω
      rcases hω with hr | hr <;> simp [ateLower, u1, u0, s1, s0, A, B, hr]
    have hiA : Integrable (fun ω => u1 ω + a * s0 ω) μ := hi1.add (hs0.const_mul a)
    have hiB : Integrable (fun ω => u1 ω + a * s0 ω - u0 ω) μ := hiA.sub hi0
    unfold mean
    rw [integral_congr_ae he,
      integral_sub hiB (hs1.const_mul b), integral_sub hiA hi0,
      integral_add hi1 (hs0.const_mul a), integral_const_mul, integral_const_mul,
      hmean0, hmean1]
    dsimp [conditionalMeanAt, u1, u0]
    rw [integral_indicator hA, integral_indicator hB,
      div_mul_cancel₀ _ hp1.ne', div_mul_cancel₀ _ hp0.ne']
    ring
  exact ⟨lower_formula a b, lower_formula b a⟩

end

end AronowAudit.P001.Wave1.AteSharpBounds
