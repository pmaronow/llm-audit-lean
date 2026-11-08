import SAP.P018a.WH.W2.Leaves
import AronowAudit.P018.Wave1.Gap.GP0181B1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace SAP.P018a.WH.W2.P.T3_L5

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

lemma inv_nat_limit :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

lemma raw_quadratic_limit :
    Tendsto (fun N : ℕ => (-4 * (N : ℝ) + 6) * ((N : ℝ) - 1)) atTop atBot := by
  have hneg : Tendsto (fun N : ℕ => -(N : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  apply Filter.tendsto_atBot_mono' atTop ?_ hneg
  filter_upwards [eventually_ge_atTop 4] with N hN
  have hn : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmul : 0 ≤ (N : ℝ) * ((N : ℝ) - 4) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith [hmul]

lemma normalized_quadratic_limit :
    Tendsto (fun N : ℕ => (-16 * (N : ℝ) + 24) /
      ((N : ℝ) * ((N : ℝ) - 1))) atTop (𝓝 0) := by
  have hnum : Tendsto (fun N : ℕ =>
      (-16 : ℝ) * (N : ℝ)⁻¹ + 24 * ((N : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun N : ℕ => (-16 : ℝ) * (N : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (-16 : ℝ))).mul inv_nat_limit
    have h₂ : Tendsto (fun N : ℕ => (24 : ℝ) * ((N : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (24 : ℝ))).mul (inv_nat_limit.pow 2)
    simpa using h₁.add h₂
  have hden : Tendsto (fun N : ℕ => (1 : ℝ) - (N : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub inv_nat_limit
  have hratio : Tendsto (fun N : ℕ =>
      ((-16 : ℝ) * (N : ℝ)⁻¹ + 24 * ((N : ℝ)⁻¹) ^ 2) /
        (1 - (N : ℝ)⁻¹)) atTop (𝓝 0) := by
    convert hnum.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1
    ext N
    simp [div_eq_mul_inv]
  apply hratio.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hncast : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hn, hn1]

lemma scaled_variance_formula_limit :
    Tendsto (fun N : ℕ =>
      4 * ((N : ℝ) - 2) * ((N : ℝ) - 3) /
        ((N : ℝ) * ((N : ℝ) - 1))) atTop (𝓝 4) := by
  have hone : Tendsto (fun N : ℕ => (1 : ℝ) - (N : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub inv_nat_limit
  have hA : Tendsto (fun N : ℕ => AronowAudit.P018.Wave1.printed_A N *
      (1 - (N : ℝ)⁻¹)) atTop (𝓝 4) := by
    convert AronowAudit.P018.Wave1.printed_A_limit.mul hone using 1
    ext N
    simp
  apply hA.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hncast : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ) - 1 ≠ 0 := by linarith
  dsimp [AronowAudit.P018.Wave1.printed_A]
  field_simp [hn, hn1]

end SAP.P018a.WH.W2.P.T3_L5

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

theorem SAP.P018a.WH.W2.T3_L5_proof : SAP.P018a.WH.W2.T3_L5 := by
  intro hSample
  refine ⟨?_, ?_, ?_⟩
  · have heq : (fun N : ℕ =>
        (∫ ω, wholeSignMeat ω ∂ unitSampleLaw signKernel N) -
          (N : ℝ) * ((N : ℝ) - 1) ^ 2) =ᶠ[atTop]
        (fun N : ℕ => (-4 * (N : ℝ) + 6) * ((N : ℝ) - 1)) := by
      filter_upwards [eventually_ge_atTop 4] with N hN
      exact (hSample N hN).2.1
    exact (tendsto_congr' heq).2 SAP.P018a.WH.W2.P.T3_L5.raw_quadratic_limit
  · have heq : (fun N : ℕ =>
        ((N : ℝ) / (Dreal N) ^ 2) *
          ((∫ ω, wholeSignMeat ω ∂ unitSampleLaw signKernel N) -
            (N : ℝ) * ((N : ℝ) - 1) ^ 2)) =ᶠ[atTop]
        (fun N : ℕ => (-16 * (N : ℝ) + 24) /
          ((N : ℝ) * ((N : ℝ) - 1))) := by
      filter_upwards [eventually_ge_atTop 4] with N hN
      exact (hSample N hN).2.2.1
    exact (tendsto_congr' heq).2 SAP.P018a.WH.W2.P.T3_L5.normalized_quadratic_limit
  · have heq : (fun N : ℕ =>
        ∫ ω, (N : ℝ) * wholeSignVariance ω ∂ unitSampleLaw signKernel N) =ᶠ[atTop]
        (fun N : ℕ => 4 * ((N : ℝ) - 2) * ((N : ℝ) - 3) /
          ((N : ℝ) * ((N : ℝ) - 1))) := by
      filter_upwards [eventually_ge_atTop 4] with N hN
      exact (hSample N hN).2.2.2
    exact (tendsto_congr' heq).2 SAP.P018a.WH.W2.P.T3_L5.scaled_variance_formula_limit
