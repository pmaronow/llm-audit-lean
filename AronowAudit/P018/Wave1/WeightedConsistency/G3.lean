import AronowAudit.P018.Wave1.WeightedConsistency.G2

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

/-- Uniform bounds give the covariance estimate without a sign assumption on the bound. -/
theorem abs_covariance_le_two_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Z W : Ω → ℝ} {B : ℝ}
    (hZ : MemLp Z 2 μ) (hW : MemLp W 2 μ)
    (hZB : ∀ᵐ ω ∂μ, |Z ω| ≤ B) (hWB : ∀ᵐ ω ∂μ, |W ω| ≤ B) :
    |covariance Z W μ| ≤ 2 * B ^ 2 := by
  have hz : |∫ ω, Z ω ∂μ| ≤ |B| := by
    have ht : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ |B| := by
      simpa only [Real.norm_eq_abs] using (hZB.mono fun ω h => h.trans (le_abs_self B))
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := μ) ht)
  have hw : |∫ ω, W ω ∂μ| ≤ |B| := by
    have ht : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ |B| := by
      simpa only [Real.norm_eq_abs] using (hWB.mono fun ω h => h.trans (le_abs_self B))
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := μ) ht)
  have hzw : |∫ ω, Z ω * W ω ∂μ| ≤ B ^ 2 := by
    have ht : ∀ᵐ ω ∂μ, ‖Z ω * W ω‖ ≤ B^2 := by
      filter_upwards [hZB, hWB] with ω h₁ h₂
      simp only [Real.norm_eq_abs, abs_mul]
      calc
        |Z ω| * |W ω| ≤ |B| * |B| :=
          mul_le_mul (h₁.trans (le_abs_self B)) (h₂.trans (le_abs_self B))
            (abs_nonneg _) (abs_nonneg _)
        _ = B ^ 2 := by nlinarith [sq_abs B]
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := μ) ht)
  rw [covariance_eq_sub hZ hW]
  calc
    |(∫ ω, Z ω * W ω ∂μ) - (∫ ω, Z ω ∂μ) * ∫ ω, W ω ∂μ| ≤
        |∫ ω, Z ω * W ω ∂μ| + |(∫ ω, Z ω ∂μ) * ∫ ω, W ω ∂μ| := abs_sub _ _
    _ ≤ B ^ 2 + |B| * |B| := add_le_add hzw (by
      rw [abs_mul]
      exact mul_le_mul hz hw (abs_nonneg _) (abs_nonneg _))
    _ = 2 * B ^ 2 := by nlinarith [sq_abs B]

theorem g3_proof : G3.{u} := by
  classical
  intro U _ μ _ N E _ σ Z B hmeas hsupp hbound
  let ν := Measure.pi (fun _ : Fin N => μ)
  have hLp (e : E) : MemLp (Z e) 2 ν :=
    MemLp.of_bound (hmeas e).aestronglyMeasurable B (hbound e)
  rw [variance_fun_sum hLp]
  calc
    ∑ e, ∑ f, covariance (Z e) (Z f) ν ≤
        ∑ e, ∑ f, if (σ e ∩ σ f).Nonempty then 2 * B ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_le_sum
      intro f hf
      split_ifs with h
      · exact (le_abs_self _).trans (abs_covariance_le_two_sq ν (hLp e) (hLp f)
          (hbound e) (hbound f))
      · have hd : Disjoint (σ e) (σ f) := Finset.disjoint_iff_inter_eq_empty.mpr
          (Finset.not_nonempty_iff_eq_empty.mp h)
        exact le_of_eq (g2_proof μ (σ e) (σ f) (Z e) (Z f) hd
          (hmeas e) (hmeas f) (hsupp e) (hsupp f) (hLp e) (hLp f))
    _ = 2 * B ^ 2 * ∑ e, ((univ.filter (fun f => (σ e ∩ σ f).Nonempty)).card : ℝ) := by
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring

end
end AronowAudit.P018.Wave1.WeightedConsistency
