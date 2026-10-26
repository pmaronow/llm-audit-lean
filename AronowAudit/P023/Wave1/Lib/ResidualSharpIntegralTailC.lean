import AronowAudit.P023.Wave1.Lib.ResidualSharpEstimateTailC

/-! Uniform integration of the sharp density comparison through the positive endpoint. -/
namespace AronowAudit.P023.Wave1
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal
set_option maxHeartbeats 600000

def tc11_positiveDensity (n : ℕ) (t : ℝ) : ℝ :=
  |1-(projection uniformMargins (2*n-1)).eval (Real.sin t)| *Real.cos t

theorem tc11_positiveDensity_continuous (n : ℕ) : Continuous (tc11_positiveDensity n) := by
  unfold tc11_positiveDensity
  fun_prop

theorem tc11_positiveDensity_eq (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi/2)) :
    tc11_positiveDensity n t = |popResidual uniformMargins (2*n-1) (Real.sin t)| *Real.cos t := by
  simp [tc11_positiveDensity, popResidual, party, tc09_sin_nonneg ht]

theorem tc11_leadingDensity_continuousOn (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (tc11_leadingDensity n) (Icc a b) := by
  unfold tc11_leadingDensity
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro t ht
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact (mul_pos (by positivity : 0 < 2*Real.pi*(n : ℝ)) (ha.trans_le ht.1)).ne'

/-- Integration of the Abel and ODE errors on any truncated positive interval. -/
theorem tc11_integrated_density_error (n : ℕ) (hn : 1 ≤ n) {a T : ℝ}
    (ha : 0 < a) (haT : a ≤ T) (hT : T < Real.pi/2) :
    |(∫ t in a..T, tc11_positiveDensity n t) - (∫ t in a..T, tc11_leadingDensity n t)| ≤
      (Real.pi+4)/(Real.pi*(n : ℝ)) + Real.pi/((n : ℝ)^2*a) + Real.pi^2/(2*(n : ℝ)) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hTp : 0 < T := ha.trans_le haT
  let E := fun t => |popResidual uniformMargins (2*n-1) (Real.sin t) -
    tc09_harmonicTail n t/(Real.pi*Real.sqrt (Real.cos t))| *Real.cos t
  have hE := tc09_harmonic_weighted_error n hn hTp.le hT
  have hsub : Icc a T ⊆ Icc (0 : ℝ) T := fun t ht => ⟨ha.le.trans ht.1,ht.2⟩
  have hEi : IntervalIntegrable E volume a T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le haT]
    exact hE.1.mono_set hsub
  have hEn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) T)] E := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    exact Eventually.of_forall fun t ht => mul_nonneg (abs_nonneg _) (tc09_cos_positive hT ht).le
  have hEb : (∫ t in a..T, E t) ≤ (Real.pi+4)/(Real.pi*(n : ℝ)) := by
    rw [intervalIntegral.integral_of_le haT, ← integral_Icc_eq_integral_Ioc]
    exact (setIntegral_mono_set hE.1 hEn (Eventually.of_forall hsub)).trans hE.2
  have hR := (tc11_positiveDensity_continuous n).intervalIntegrable (μ:=volume) a T
  have hD : IntervalIntegrable (tc11_leadingDensity n) volume a T :=
    (tc11_leadingDensity_continuousOn n hn ha).intervalIntegrable_of_Icc haT
  have hK : IntervalIntegrable (fun t : ℝ => 1/t^2) volume a T := by
    apply ContinuousOn.intervalIntegrable_of_Icc haT
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (ha.trans_le ht.1).ne')
  have hmodel := ((hEi.add (hK.const_mul (Real.pi/(n : ℝ)^2))).add
    (intervalIntegrable_const (c:=Real.pi/(n : ℝ))))
  have hcomp : (∫ t in a..T, |tc11_positiveDensity n t-tc11_leadingDensity n t|) ≤
      (∫ t in a..T, E t + (Real.pi/(n : ℝ)^2)*(1/t^2) + Real.pi/(n : ℝ)) := by
    apply intervalIntegral.integral_mono_on haT (hR.sub hD).abs hmodel
    intro t ht
    rw [tc11_positiveDensity_eq n ⟨ha.le.trans ht.1,ht.2.trans hT.le⟩]
    exact tc11_density_error n hn (ha.trans_le ht.1) (ht.2.trans_lt hT)
  have hint := (intervalIntegral.abs_integral_le_integral_abs haT
    (f:=fun t => tc11_positiveDensity n t-tc11_leadingDensity n t)).trans hcomp
  rw [intervalIntegral.integral_sub hR hD] at hint
  rw [intervalIntegral.integral_add (hEi.add (hK.const_mul (Real.pi/(n : ℝ)^2)))
    (intervalIntegrable_const), intervalIntegral.integral_add hEi
    (hK.const_mul (Real.pi/(n : ℝ)^2)), intervalIntegral.integral_const_mul,
    tc11_inverse_square_integral ha haT, intervalIntegral.integral_const] at hint
  simp only [smul_eq_mul] at hint
  have hKle : (Real.pi/(n : ℝ)^2)*(1/a-1/T) ≤ Real.pi/((n : ℝ)^2*a) := by
    have h := mul_le_mul_of_nonneg_left
      (show 1/a-1/T ≤ 1/a from sub_le_self _ (by positivity : 0 ≤ 1/T)) (by positivity : 0 ≤ Real.pi/(n : ℝ)^2)
    exact h.trans_eq (by ring)
  have hconst : (T-a)*(Real.pi/(n : ℝ)) ≤ Real.pi^2/(2*(n : ℝ)) := by
    apply (mul_le_mul_of_nonneg_right (show T-a ≤ Real.pi/2 by linarith)
      (by positivity : 0 ≤ Real.pi/(n : ℝ))).trans_eq
    ring
  linarith

/-- The bound is uniform as the endpoint tends to `pi/2`; no pointwise endpoint estimate is used. -/
theorem tc11_full_density_error (n : ℕ) (hn : 2 ≤ n) :
    |(∫ t in (1/(n : ℝ))..(Real.pi/2), tc11_positiveDensity n t) -
      (∫ t in (1/(n : ℝ))..(Real.pi/2), tc11_leadingDensity n t)| ≤
        ((Real.pi+4)/Real.pi+Real.pi+Real.pi^2)/(n : ℝ) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let a : ℝ := 1/(n : ℝ)
  let b : ℝ := Real.pi/2
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < b := by
    have hhalf : a ≤ 1/2 := by dsimp [a]; exact one_div_le_one_div_of_le (by norm_num) htwo
    dsimp [b]
    linarith [Real.two_le_pi]
  have hRint := (tc11_positiveDensity_continuous n).intervalIntegrable (μ:=volume) a b
  have hDint : IntervalIntegrable (tc11_leadingDensity n) volume a b :=
    (tc11_leadingDensity_continuousOn n (by omega) ha).intervalIntegrable_of_Icc hab.le
  have hRder := intervalIntegral.integral_hasDerivAt_right hRint
    (tc11_positiveDensity_continuous n).stronglyMeasurable.stronglyMeasurableAtFilter
    (tc11_positiveDensity_continuous n).continuousAt
  have hDmeas : Measurable (tc11_leadingDensity n) := by unfold tc11_leadingDensity; fun_prop
  have hDcont : ContinuousAt (tc11_leadingDensity n) b := by
    unfold tc11_leadingDensity
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    dsimp [b]
    positivity
  have hDder := intervalIntegral.integral_hasDerivAt_right hDint
    hDmeas.stronglyMeasurable.stronglyMeasurableAtFilter hDcont
  have hlim := ((hRder.continuousAt.sub hDder.continuousAt).abs.tendsto).mono_left
    (show nhdsWithin b (Iio b) ≤ nhds b from nhdsWithin_le_nhds)
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hab).filter_mono nhdsWithin_le_nhds] with T hT haT
  have h := tc11_integrated_density_error n (by omega) ha haT.le hT
  apply h.trans
  dsimp [a]
  field_simp
  nlinarith [Real.pi_pos]

/-- Exact substitution at the positive endpoint, after writing the continuous positive branch. -/
theorem tc11_positiveDensity_substitution (n : ℕ) (hn : 2 ≤ n) :
    (∫ t in (1/(n : ℝ))..(Real.pi/2), tc11_positiveDensity n t) =
      ∫ x in (Real.sin (1/(n : ℝ)))..1, |popResidual uniformMargins (2*n-1) x| := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 ≤ 1/(n : ℝ) := by positivity
  have hab : 1/(n : ℝ) ≤ Real.pi/2 := by
    have hhalf := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<2) htwo
    linarith [Real.two_le_pi]
  have hsin : 0 ≤ Real.sin (1/(n : ℝ)) := tc09_sin_nonneg ⟨ha,hab⟩
  have hs := intervalIntegral.integral_comp_mul_deriv
    (a:=1/(n : ℝ)) (b:=Real.pi/2) (f:=Real.sin) (f':=Real.cos)
    (g:=fun x => |1-(projection uniformMargins (2*n-1)).eval x|)
    (fun t _ => Real.hasDerivAt_sin t) Real.continuous_cos.continuousOn
    ((continuous_const.sub (projection uniformMargins (2*n-1)).continuous).abs)
  change (∫ t in (1/(n : ℝ))..(Real.pi/2),
    |1-(projection uniformMargins (2*n-1)).eval (Real.sin t)| *Real.cos t) = _
  simp only [Function.comp_apply] at hs
  rw [hs,Real.sin_pi_div_two]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le (Real.sin_le_one _)]
  intro x hx
  simp only [popResidual,party,if_pos (hsin.trans hx.1)]

/-- Actual L1 error differs from the leading cosine integral by `O(1/n)` with fixed constants. -/
theorem tc11_l1_leading_density (n : ℕ) (hn : 2 ≤ n) :
    |expectation uniformMargins (fun x => |popResidual uniformMargins (2*n-1) x|) -
      (∫ t in (1/(n : ℝ))..(Real.pi/2), tc11_leadingDensity n t)| ≤
      (2+(Real.pi+4)/Real.pi+Real.pi+Real.pi^2)/(n : ℝ) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 ≤ 1/(n : ℝ) := by positivity
  have hab : 1/(n : ℝ) ≤ Real.pi/2 := by
    have hhalf := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<2) htwo
    linarith [Real.two_le_pi]
  let s := Real.sin (1/(n : ℝ))
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨tc09_sin_nonneg ⟨ha,hab⟩,Real.sin_le_one _⟩
  have hsmall := tc11_residual_small_interval (2*n-1) hs
  have hv := tc09_variance_upper n (by omega)
  have hsin : s ≤ 1/(n : ℝ) := Real.sin_le ha
  have hv' : 2*residualVariance uniformMargins (2*n-1) ≤ 1/(n : ℝ) := by
    calc
      _ ≤ 2*(1/(4*Real.pi*(n : ℝ))) := by gcongr
      _ ≤ _ := by field_simp; nlinarith [Real.two_le_pi]
  have hsmall' : abs (∫ x in (0 : ℝ)..s, |popResidual uniformMargins (2*n-1) x|) ≤ 2/(n : ℝ) := by
    rw [abs_of_nonneg (intervalIntegral.integral_nonneg hs.1 (fun _ _ => abs_nonneg _))]
    calc
      _ ≤ 2*residualVariance uniformMargins (2*n-1)+s := hsmall
      _ ≤ 1/(n : ℝ)+1/(n : ℝ) := add_le_add hv' hsin
      _ = _ := by ring
  have hfullabs : IntegrableOn (fun x => |popResidual uniformMargins (2*n-1) x|) (Icc (-1 : ℝ) 1) volume :=
    (tc09_residual_volume_integrable (2*n-1)).abs
  have hi : IntervalIntegrable (fun x => |popResidual uniformMargins (2*n-1) x|) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hfullabs.mono_set
      (by intro x hx; exact ⟨by linarith [hx.1],hx.2⟩)
  have hleft := hi.mono_set (show uIcc (0 : ℝ) s ⊆ uIcc (0 : ℝ) 1 from by
    rw [uIcc_of_le hs.1,uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro x hx
    exact ⟨hx.1,hx.2.trans hs.2⟩)
  have hright := hi.mono_set (show uIcc s 1 ⊆ uIcc (0 : ℝ) 1 from by
    rw [uIcc_of_le hs.2,uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro x hx
    exact ⟨hs.1.trans hx.1,hx.2⟩)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have herror := tc11_full_density_error n hn
  rw [tc11_positiveDensity_substitution n hn] at herror
  rw [tc11_residual_positive_half, ← hsum]
  have h := (abs_add_le (∫ x in (0 : ℝ)..s, |popResidual uniformMargins (2*n-1) x|)
    ((∫ x in s..1, |popResidual uniformMargins (2*n-1) x|) -
      ∫ t in (1/(n : ℝ))..(Real.pi/2), tc11_leadingDensity n t)).trans
        (add_le_add hsmall' herror)
  convert h using 1 <;> ring

end
end AronowAudit.P023.Wave1
