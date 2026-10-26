import AronowAudit.P023.Wave1.Lib.OrderedHarmonicTailC
import AronowAudit.P023.Wave1.Lib.ResidualLimitsTailC

/-! Harmonic comparison for the actual uniform polynomial residuals. -/

namespace AronowAudit.P023.Wave1
noncomputable section
open MeasureTheory Set Filter Finset
open scoped BigOperators Topology ENNReal

def tc09_errorKernel (t : ℝ) : ℝ := (1 + Real.tan t) * Real.sqrt (Real.cos t)

theorem tc09_cos_positive {T t : ℝ} (hTp : T < Real.pi/2) (ht : t ∈ Icc (0 : ℝ) T) :
    0 < Real.cos t :=
  tc08_cos_pos ⟨by linarith [ht.1, Real.pi_pos], ht.2.trans_lt hTp⟩

theorem tc09_errorKernel_continuousOn {T : ℝ} (hTp : T < Real.pi/2) :
    ContinuousOn tc09_errorKernel (Icc (0 : ℝ) T) := by
  unfold tc09_errorKernel
  apply ContinuousOn.mul
  · apply continuousOn_const.add
    intro t ht
    exact ((Real.continuousAt_tan).mpr (tc09_cos_positive hTp ht).ne').continuousWithinAt
  · fun_prop

/-- The Jacobian makes the ODE error integrable, with a bound independent of the endpoint. -/
theorem tc09_errorKernel_integral {T : ℝ} (hT : 0 ≤ T) (hTp : T < Real.pi/2) :
    (∫ t in Icc (0 : ℝ) T, tc09_errorKernel t) ≤ Real.pi/2 + 2 := by
  have hcont : ContinuousOn (fun t => 1 + Real.sin t / Real.sqrt (Real.cos t))
      (Icc (0 : ℝ) T) := by
    apply continuousOn_const.add
    apply Real.continuous_sin.continuousOn.div
      (Real.continuous_sqrt.comp Real.continuous_cos).continuousOn
    intro t ht
    exact (Real.sqrt_pos.mpr (tc09_cos_positive hTp ht)).ne'
  have hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt
      (fun t => t - 2 * Real.sqrt (Real.cos t))
      (1 + Real.sin t / Real.sqrt (Real.cos t)) t := by
    intro t ht
    have hc := tc09_cos_positive hTp ht
    have h := (hasDerivAt_id t).sub (((Real.hasDerivAt_cos t).sqrt hc.ne').const_mul 2)
    convert h using 1
    · rfl
    · ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := T)
    (fun t ht => hd t (by simpa only [uIcc_of_le hT] using ht))
    (hcont.intervalIntegrable_of_Icc hT)
  have hmono : (∫ t in Icc (0 : ℝ) T, tc09_errorKernel t) ≤
      ∫ t in Icc (0 : ℝ) T, 1 + Real.sin t / Real.sqrt (Real.cos t) := by
    apply setIntegral_mono_on (tc09_errorKernel_continuousOn hTp).integrableOn_Icc
      hcont.integrableOn_Icc measurableSet_Icc
    intro t ht
    have hc := tc09_cos_positive hTp ht
    have hr : 0 < Real.sqrt (Real.cos t) := Real.sqrt_pos.mpr hc
    have hr2 : Real.sqrt (Real.cos t)^2 = Real.cos t := Real.sq_sqrt hc.le
    have hr1 : Real.sqrt (Real.cos t) ≤ 1 := by
      exact (Real.sqrt_le_one).mpr (Real.cos_le_one t)
    have he : tc09_errorKernel t = Real.sqrt (Real.cos t) +
        Real.sin t / Real.sqrt (Real.cos t) := by
      unfold tc09_errorKernel
      rw [Real.tan_eq_sin_div_cos]
      field_simp
      rw [hr2]
      ring
    rw [he]
    linarith
  simp_rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT] at hmono
  rw [hi] at hmono
  simp only [Real.cos_zero, Real.sqrt_one, zero_sub] at hmono
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  nlinarith [Real.sqrt_nonneg (Real.cos T)]

theorem tc09_finite_sine_error (n M : ℕ) (hn : 1 ≤ n) (hnM : n ≤ M)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (Real.pi/2)) :
    |popResidual uniformMargins (2*n-1) (Real.sin t) -
        (∑ m ∈ Finset.Ico n M, tc09_sinPhase m t / (m : ℝ)) /
          (Real.pi * Real.sqrt (Real.cos t))| * Real.cos t ≤
      |popResidual uniformMargins (2*M-1) (Real.sin t)| * Real.cos t +
        (2 / (Real.pi * (n : ℝ))) * tc09_errorKernel t := by
  have hc : 0 < Real.cos t := tc09_cos_positive ht.2 ⟨ht.1, le_rfl⟩
  have hr : 0 < Real.sqrt (Real.cos t) := Real.sqrt_pos.mpr hc
  have hr2 : Real.sqrt (Real.cos t)^2 = Real.cos t := Real.sq_sqrt hc.le
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htan : 0 ≤ Real.tan t :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two ht.1 ht.2.le
  let E := fun m => tc08_coefficient m *
    (AronowAudit.Literature.legendreRodrigues (2*m+1)).eval (Real.sin t) -
      tc09_sinPhase m t / ((m : ℝ) * (Real.pi * Real.sqrt (Real.cos t)))
  have he : popResidual uniformMargins (2*n-1) (Real.sin t) -
      (∑ m ∈ Finset.Ico n M, tc09_sinPhase m t / (m : ℝ)) /
        (Real.pi * Real.sqrt (Real.cos t)) =
      popResidual uniformMargins (2*M-1) (Real.sin t) + ∑ m ∈ Finset.Ico n M, E m := by
    have h := tc09_residual_finite_tail n M hn hnM (Real.sin t)
    simp only [E, Finset.sum_sub_distrib, div_mul_eq_div_div, ← Finset.sum_div]
    linarith
  have hsum : |∑ m ∈ Finset.Ico n M, E m| ≤
      ((1 + Real.tan t) / (Real.pi * Real.sqrt (Real.cos t))) *
        (2 / (n : ℝ)) := by
    calc
      _ ≤ ∑ m ∈ Finset.Ico n M, |E m| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Ico n M,
          ((1 + Real.tan t) / (Real.pi * Real.sqrt (Real.cos t))) * (1 / (m : ℝ)^2) := by
        apply Finset.sum_le_sum
        intro m hm
        have hmn := (Finset.mem_Ico.mp hm).1
        have herr := legendre_sine_error_explicit m (by omega) ht
        have hearg : E m = tc08_coefficient m *
            (AronowAudit.Literature.legendreRodrigues (2*m+1)).eval (Real.sin t) -
            Real.sin (tc08_frequency m * t) /
              (Real.pi * (m : ℝ) * Real.sqrt (Real.cos t)) := by
          dsimp [E, tc09_sinPhase, tc08_frequency]
          congr 1
          ring
        rw [hearg]
        exact herr.trans_eq (by ring)
      _ = ((1 + Real.tan t) / (Real.pi * Real.sqrt (Real.cos t))) *
          ∑ m ∈ Finset.Ico n M, 1 / (m : ℝ)^2 := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (tc09_reciprocal_square_tail n M hn hnM)
        (by positivity)
  rw [he]
  calc
    _ ≤ (|popResidual uniformMargins (2*M-1) (Real.sin t)| +
        |∑ m ∈ Finset.Ico n M, E m|) * Real.cos t :=
      mul_le_mul_of_nonneg_right (abs_add_le _ _) hc.le
    _ ≤ (|popResidual uniformMargins (2*M-1) (Real.sin t)| +
        ((1 + Real.tan t) / (Real.pi * Real.sqrt (Real.cos t))) *
          (2 / (n : ℝ))) * Real.cos t := by gcongr
    _ = _ := by
      dsimp [tc09_errorKernel]
      field_simp
      nlinarith

/-- A Fatou bridge which also proves the integrability of the limit. -/
theorem tc09_nonnegative_integral_limit_bound {μ : Measure ℝ} {G : ℕ → ℝ → ℝ}
    {f : ℝ → ℝ} {b : ℕ → ℝ} {B : ℝ}
    (hG : ∀ M, Integrable (G M) μ) (hGn : ∀ M, 0 ≤ᵐ[μ] G M)
    (hf : 0 ≤ᵐ[μ] f)
    (hlim : ∀ᵐ t ∂μ, Tendsto (fun M => G M t) atTop (𝓝 (f t)))
    (hb : ∀ M, (∫ t, G M t ∂μ) ≤ b M) (hbB : Tendsto b atTop (𝓝 B)) :
    Integrable f μ ∧ (∫ t, f t ∂μ) ≤ B := by
  have hmono : ∀ M, (∫⁻ t, ‖G M t‖ₑ ∂μ) ≤ ENNReal.ofReal (b M) := by
    intro M
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hG M)]
    have he : (∫ t, ‖G M t‖ ∂μ) = ∫ t, G M t ∂μ :=
      integral_congr_ae ((hGn M).mono fun _ ht => Real.norm_of_nonneg ht)
    rw [he]
    exact ENNReal.ofReal_le_ofReal (hb M)
  have hbound : liminf (fun M => ∫⁻ t, ‖G M t‖ₑ ∂μ) atTop ≤ ENNReal.ofReal B := by
    calc
      _ ≤ liminf (fun M => ENNReal.ofReal (b M)) atTop :=
        liminf_le_liminf (Eventually.of_forall hmono)
      _ = _ := (ENNReal.continuous_ofReal.tendsto B |>.comp hbB).liminf_eq
  have hfi : Integrable f μ := integrable_of_tendsto hlim
    (fun M => (hG M).aestronglyMeasurable) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
  refine ⟨hfi, ?_⟩
  have hfatou := (lintegral_enorm_le_liminf_of_tendsto hlim
    (fun M => (hG M).aestronglyMeasurable.aemeasurable.enorm)).trans hbound
  rw [← ofReal_integral_norm_eq_lintegral_enorm hfi] at hfatou
  have he : (∫ t, ‖f t‖ ∂μ) = ∫ t, f t ∂μ :=
    integral_congr_ae (hf.mono fun _ ht => Real.norm_of_nonneg ht)
  rw [he] at hfatou
  have hB : 0 ≤ B := ge_of_tendsto hbB (Eventually.of_forall fun M =>
    (integral_nonneg_of_ae (hGn M)).trans (hb M))
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hfatou

/-- The quantitative comparison is obtained from the finite identity and the actual L¹ limit. -/
theorem tc09_harmonic_weighted_error (n : ℕ) (hn : 1 ≤ n) {T : ℝ}
    (hT : 0 ≤ T) (hTp : T < Real.pi/2) :
    IntegrableOn (fun t => |popResidual uniformMargins (2*n-1) (Real.sin t) -
      tc09_harmonicTail n t / (Real.pi * Real.sqrt (Real.cos t))| * Real.cos t)
      (Icc (0 : ℝ) T) ∧
    (∫ t in Icc (0 : ℝ) T, |popResidual uniformMargins (2*n-1) (Real.sin t) -
      tc09_harmonicTail n t / (Real.pi * Real.sqrt (Real.cos t))| * Real.cos t) ≤
      (Real.pi + 4) / (Real.pi * (n : ℝ)) := by
  let G := fun (M : ℕ) (t : ℝ) =>
    |popResidual uniformMargins (2*n-1) (Real.sin t) -
      (∑ m ∈ Finset.Ico n (n+M), tc09_sinPhase m t / (m : ℝ)) /
        (Real.pi * Real.sqrt (Real.cos t))| * Real.cos t
  let b := fun M : ℕ => 2 * expectation uniformMargins
    (fun x => |popResidual uniformMargins (2*(n+M)-1) x|) +
      (2 / (Real.pi * (n : ℝ))) * (Real.pi/2 + 2)
  have hnat : Tendsto (fun M : ℕ => n + M) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat n
  have hG : ∀ M, IntegrableOn (G M) (Icc (0 : ℝ) T) := by
    intro M
    have hsum : Continuous (fun t => ∑ m ∈ Finset.Ico n (n+M),
        tc09_sinPhase m t / (m : ℝ)) := by
      dsimp [tc09_sinPhase]
      fun_prop
    have hquot : ContinuousOn (fun t => (∑ m ∈ Finset.Ico n (n+M),
        tc09_sinPhase m t / (m : ℝ)) / (Real.pi * Real.sqrt (Real.cos t)))
        (Icc (0 : ℝ) T) := by
      apply hsum.continuousOn.div (by fun_prop)
      intro t ht
      exact mul_ne_zero Real.pi_ne_zero (Real.sqrt_pos.mpr (tc09_cos_positive hTp ht)).ne'
    exact (((tc09_residual_sine_continuousOn (2*n-1) hT hTp).sub hquot).abs.mul
      Real.continuous_cos.continuousOn).integrableOn_Icc
  have hGn : ∀ M, 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) T)] G M := by
    intro M
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    exact Eventually.of_forall fun t ht => mul_nonneg (abs_nonneg _) (tc09_cos_positive hTp ht).le
  have hf : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) T)]
      (fun t => |popResidual uniformMargins (2*n-1) (Real.sin t) -
        tc09_harmonicTail n t / (Real.pi * Real.sqrt (Real.cos t))| * Real.cos t) := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    exact Eventually.of_forall fun t ht => mul_nonneg (abs_nonneg _) (tc09_cos_positive hTp ht).le
  have hlim : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), Tendsto (fun M => G M t) atTop
      (𝓝 (|popResidual uniformMargins (2*n-1) (Real.sin t) -
        tc09_harmonicTail n t / (Real.pi * Real.sqrt (Real.cos t))| * Real.cos t)) := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    apply Eventually.of_forall
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      simpa only [G, tc09_sinPhase, mul_zero, Real.sin_zero, zero_div, Finset.sum_const_zero,
        tc09_harmonicTail, zero_mul, div_zero, sub_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
          |popResidual uniformMargins (2*n-1) (Real.sin 0)| * Real.cos 0) atTop (𝓝 _))
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi htpos
        (by linarith [ht.2, hTp, Real.pi_pos])
      have hseq := (tc09_harmonic_ordered_limit n hn hsin.ne').comp
        hnat
      have hseq' := (((tendsto_const_nhds : Tendsto
          (fun _ : ℕ => popResidual uniformMargins (2*n-1) (Real.sin t)) atTop (𝓝 _)).sub
        (hseq.div_const (Real.pi * Real.sqrt (Real.cos t)))).abs).mul_const (Real.cos t)
      simpa only [G, tc09_sinPhase, Function.comp_apply] using hseq'
  have hb : ∀ M, (∫ t in Icc (0 : ℝ) T, G M t) ≤ b M := by
    intro M
    have hk : IntegrableOn tc09_errorKernel (Icc (0 : ℝ) T) volume :=
      (tc09_errorKernel_continuousOn hTp).integrableOn_Icc
    have hr := tc09_residual_sine_integrable (2*(n+M)-1) hT hTp
    have hm : (∫ t in Icc (0 : ℝ) T, G M t) ≤
        ∫ t in Icc (0 : ℝ) T,
          |popResidual uniformMargins (2*(n+M)-1) (Real.sin t)| * Real.cos t +
            (2 / (Real.pi * (n : ℝ))) * tc09_errorKernel t := by
      apply setIntegral_mono_on (hG M) (hr.add (hk.const_mul _)) measurableSet_Icc
      intro t ht
      exact tc09_finite_sine_error n (n+M) hn (by omega) ⟨ht.1, ht.2.trans_lt hTp⟩
    rw [integral_add hr (hk.const_mul _), integral_const_mul] at hm
    exact hm.trans (add_le_add (tc09_residual_sine_l1_le _ hT hTp)
      (mul_le_mul_of_nonneg_left (tc09_errorKernel_integral hT hTp) (by positivity)))
  have hbB : Tendsto b atTop (𝓝 ((Real.pi + 4) / (Real.pi * (n : ℝ)))) := by
    have h := ((tc09_uniform_residual_l1_zero.comp
      hnat).const_mul 2).add_const
        ((2 / (Real.pi * (n : ℝ))) * (Real.pi/2 + 2))
    convert h using 1
    · rfl
    · simp only [mul_zero, zero_add]
      ring
  exact tc09_nonnegative_integral_limit_bound hG hGn hf hlim hb hbB


end
end AronowAudit.P023.Wave1
