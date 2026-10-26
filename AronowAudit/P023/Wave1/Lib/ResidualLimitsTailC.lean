import AronowAudit.P023.Wave1.Lib.UniformProjectionTailC
import AronowAudit.P023.Wave1.Lib.LegendreOdeTailC

/-! Limits of the actual chosen uniform projections, and their finite tail identity. -/

namespace AronowAudit.P023.Wave1
noncomputable section
open MeasureTheory Set Filter Polynomial Finset
open scoped BigOperators Topology ENNReal

theorem tc09_residual_integrable (J : ℕ) :
    Integrable (popResidual uniformMargins J) uniformMargins := by
  change Integrable (fun x => party x - (projection uniformMargins J).eval x) uniformMargins
  simpa only [pow_zero, mul_one] using
    tc04_residual_power_integrable (projection uniformMargins J) 0

theorem tc09_residual_square_integrable (J : ℕ) :
    Integrable (fun x => popResidual uniformMargins J x ^ 2) uniformMargins := by
  let p := projection uniformMargins J
  convert tc04_piecewise_integrable ((1-p)^2) ((-p)^2) using 1
  funext x
  by_cases hx : 0 ≤ x <;> simp [popResidual, party, hx, p]

theorem tc09_residual_volume_integrable (J : ℕ) :
    IntegrableOn (popResidual uniformMargins J) (Icc (-1 : ℝ) 1) := by
  have h := tc09_residual_integrable J
  change Integrable _ ((1/2 : ℝ≥0∞) • volume.restrict (Icc (-1 : ℝ) 1)) at h
  exact (integrable_smul_measure (by norm_num) (by norm_num)).mp h

theorem tc09_variance_exact (n : ℕ) (hn : 1 ≤ n) :
    residualVariance uniformMargins (2*n-1) = centralBinomial n ^ 2 / 4 := by
  have h := (uniform_projection_variance (2*n-1) (by omega)).2.2.1
  have he : (2*n-1+1)/2 = n := by omega
  simpa only [he] using h

theorem tc09_variance_upper (n : ℕ) (hn : 1 ≤ n) :
    residualVariance uniformMargins (2*n-1) ≤ 1 / (4 * Real.pi * (n : ℝ)) := by
  rw [tc09_variance_exact n hn]
  calc
    _ ≤ (1 / (Real.pi * (n : ℝ))) / 4 :=
      div_le_div_of_nonneg_right (central_binomial_wallis_bounds n hn).2 (by norm_num)
    _ = _ := by ring

/-- Cauchy--Schwarz for this actual residual, proved by integrating a nonnegative square. -/
theorem tc09_residual_l1_le_sqrt (J : ℕ) (hJ : 1 ≤ J) :
    expectation uniformMargins (fun x => |popResidual uniformMargins J x|) ≤
      Real.sqrt (residualVariance uniformMargins J) := by
  letI tc09_l1_uniform_probability : IsProbabilityMeasure uniformMargins :=
    ⟨uniform_law_normalized.1⟩
  let v := residualVariance uniformMargins J
  have hv : 0 < v := (uniform_projection_variance J hJ).2.2.2
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hsq : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv.le
  have hi := tc09_residual_square_integrable J
  have habs := (tc09_residual_integrable J).abs
  have hm : (∫ x, |popResidual uniformMargins J x| ∂uniformMargins) ≤
      ∫ x, (popResidual uniformMargins J x ^ 2 + v) / (2 * Real.sqrt v)
        ∂uniformMargins := by
    apply integral_mono habs ((hi.add (integrable_const v)).div_const _)
    intro x
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt v)).mpr
    change |popResidual uniformMargins J x| * (2 * Real.sqrt v) ≤
      popResidual uniformMargins J x ^ 2 + v
    nlinarith [sq_nonneg (|popResidual uniformMargins J x| - Real.sqrt v),
      sq_abs (popResidual uniformMargins J x)]
  rw [integral_div, integral_add hi (integrable_const v), integral_const] at hm
  simp only [probReal_univ, smul_eq_mul, one_mul] at hm
  change (∫ x, |popResidual uniformMargins J x| ∂uniformMargins) ≤
    (v + v) / (2 * Real.sqrt v) at hm
  change expectation uniformMargins _ ≤ Real.sqrt v
  change (∫ x, |popResidual uniformMargins J x| ∂uniformMargins) ≤ _
  have he : (v + v) / (2 * Real.sqrt v) = Real.sqrt v := by
    apply (div_eq_iff (by positivity : 2 * Real.sqrt v ≠ 0)).mpr
    nlinarith
  exact hm.trans_eq he

/-- No completeness theorem is needed: the exact variance forces L² error to zero. -/
theorem tc09_uniform_variance_zero :
    Tendsto (fun n : ℕ => residualVariance uniformMargins (2*n-1)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => 1 / (4 * Real.pi * (n : ℝ))) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  apply squeeze_zero' ?_ ?_ hlim
  · exact Eventually.of_forall fun n => integral_nonneg (fun _ => sq_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact tc09_variance_upper n hn

/-- The ordinary L¹ errors of the actual epsilon-chosen projections tend to zero. -/
theorem tc09_uniform_residual_l1_zero :
    Tendsto (fun n : ℕ => expectation uniformMargins
      (fun x => |popResidual uniformMargins (2*n-1) x|)) atTop (𝓝 0) := by
  have hlim := tc09_uniform_variance_zero.sqrt
  simp only [Real.sqrt_zero] at hlim
  apply squeeze_zero' ?_ ?_ hlim
  · exact Eventually.of_forall fun n => integral_nonneg (fun _ => abs_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact tc09_residual_l1_le_sqrt (2*n-1) (by omega)

/-- The exact finite polynomial identity, before taking any analytic limit. -/
theorem tc09_residual_finite_tail (n M : ℕ) (hn : 1 ≤ n) (hnM : n ≤ M) (x : ℝ) :
    popResidual uniformMargins (2*n-1) x - popResidual uniformMargins (2*M-1) x =
      ∑ m ∈ Finset.Ico n M, tc08_coefficient m *
        (AronowAudit.Literature.legendreRodrigues (2*m+1)).eval x := by
  have hM : 1 ≤ M := by omega
  have hen : (2*n-1+1)/2 = n := by omega
  have heM : (2*M-1+1)/2 = M := by omega
  simp only [popResidual, tc04_uniform_projection_expansion, tc04_uniform_candidate,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, hen, heM]
  have hsum := Finset.sum_range_add_sum_Ico
    (fun m => tc04_odd_coefficient m *
      (AronowAudit.Literature.legendreRodrigues (2*m+1)).eval x) hnM
  change party x - (1/2 + ∑ m ∈ range n, tc04_odd_coefficient m *
      (AronowAudit.Literature.legendreRodrigues (2*m+1)).eval x) -
    (party x - (1/2 + ∑ m ∈ range M, tc04_odd_coefficient m *
      (AronowAudit.Literature.legendreRodrigues (2*m+1)).eval x)) =
    ∑ m ∈ Finset.Ico n M, tc04_odd_coefficient m *
      (AronowAudit.Literature.legendreRodrigues (2*m+1)).eval x
  linarith


theorem tc09_sin_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi/2)) :
    0 ≤ Real.sin t :=
  Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, Real.pi_pos])

theorem tc09_residual_sine_continuousOn (J : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hTp : T < Real.pi/2) :
    ContinuousOn (fun t => popResidual uniformMargins J (Real.sin t)) (Icc (0 : ℝ) T) := by
  apply ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).sub
    ((projection uniformMargins J).continuous.comp
    Real.continuous_sin)).continuousOn.congr
  intro t ht
  simp only [popResidual, party, if_pos (tc09_sin_nonneg ⟨ht.1, ht.2.trans hTp.le⟩)]
  rfl

theorem tc09_residual_sine_integrable (J : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hTp : T < Real.pi/2) :
    IntegrableOn (fun t => |popResidual uniformMargins J (Real.sin t)| * Real.cos t)
      (Icc (0 : ℝ) T) :=
  ((tc09_residual_sine_continuousOn J hT hTp).abs.mul
    Real.continuous_cos.continuousOn).integrableOn_Icc

/-- Change variables on the positive half interval before comparing to the full L¹ error. -/
theorem tc09_residual_sine_substitution (J : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hTp : T < Real.pi/2) :
    (∫ t in Icc (0 : ℝ) T, |popResidual uniformMargins J (Real.sin t)| * Real.cos t) =
      ∫ x in Icc (0 : ℝ) (Real.sin T), |popResidual uniformMargins J x| := by
  have hsinT : 0 ≤ Real.sin T := tc09_sin_nonneg ⟨hT, hTp.le⟩
  have hs := intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := T)
    (f := Real.sin) (f' := Real.cos)
    (g := fun x => |1 - (projection uniformMargins J).eval x|)
    (fun t _ => Real.hasDerivAt_sin t) Real.continuous_cos.continuousOn
    ((continuous_const.sub (projection uniformMargins J).continuous).abs)
  rw [Real.sin_zero] at hs
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsinT]
  calc
    _ = ∫ t in (0 : ℝ)..T,
        |1 - (projection uniformMargins J).eval (Real.sin t)| * Real.cos t := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hT]
      intro t ht
      simp only [popResidual, party, if_pos (tc09_sin_nonneg ⟨ht.1, ht.2.trans hTp.le⟩)]
    _ = _ := hs
    _ = _ := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hsinT]
      intro x hx
      simp only [popResidual, party, if_pos hx.1]

theorem tc09_residual_sine_l1_le (J : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hTp : T < Real.pi/2) :
    (∫ t in Icc (0 : ℝ) T, |popResidual uniformMargins J (Real.sin t)| * Real.cos t) ≤
      2 * expectation uniformMargins (fun x => |popResidual uniformMargins J x|) := by
  rw [tc09_residual_sine_substitution J hT hTp, tc04_eq_interval,
    intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    ← integral_Icc_eq_integral_Ioc]
  have hsub : Icc (0 : ℝ) (Real.sin T) ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2.trans (Real.sin_le_one _)⟩
  have h := setIntegral_mono_set (tc09_residual_volume_integrable J).abs
    (Eventually.of_forall fun x => abs_nonneg (popResidual uniformMargins J x))
    (Eventually.of_forall hsub)
  linarith

end
end AronowAudit.P023.Wave1
