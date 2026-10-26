import AronowAudit.P023.Wave1.Lib.HarmonicTailTailC
import AronowAudit.P023.Wave1.Lib.CosineAveragingTailC

/-! Unconditional divergence of the actual uniform residual amplification.
The lower bound uses only intervals contained in `[0,1/2]`. -/

namespace AronowAudit.P023.Wave1
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

theorem tc09_cosine_residual_pointwise (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (ha : 0 < a) (ht : t ∈ Icc a (1/2 : ℝ)) :
    Real.cos ((2*(n : ℝ)+1/2)*t)^2/t ≤
      (4 * Real.pi * (n : ℝ)) *
        (|popResidual uniformMargins (2*n-1) (Real.sin t)| * Real.cos t +
          |popResidual uniformMargins (2*n-1) (Real.sin t) -
            tc09_harmonicTail n t/(Real.pi * Real.sqrt (Real.cos t))| * Real.cos t) +
        Real.pi^2 / ((n : ℝ)*a^2) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htpos : 0 < t := ha.trans_le ht.1
  have hTp : (1/2 : ℝ) < Real.pi/2 := by linarith [Real.two_le_pi]
  have hc : 0 < Real.cos t := tc09_cos_positive hTp ⟨htpos.le, ht.2⟩
  have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi htpos
    (by linarith [ht.2, Real.two_le_pi])
  have hr : 0 < Real.sqrt (Real.cos t) := Real.sqrt_pos.mpr hc
  have hr2 : Real.sqrt (Real.cos t)^2 = Real.cos t := Real.sq_sqrt hc.le
  have hr1 : Real.sqrt (Real.cos t) ≤ 1 := Real.sqrt_le_one.mpr (Real.cos_le_one t)
  have hrhalf : (1/2 : ℝ) ≤ Real.sqrt (Real.cos t) := by
    apply (Real.le_sqrt (by norm_num) hc.le).mpr
    have ht2 : t^2 ≤ (1/2 : ℝ)^2 := by
      simpa only [pow_two] using mul_self_le_mul_self htpos.le ht.2
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  let f := tc09_harmonicTail n t
  let c := Real.cos ((2*(n : ℝ)+1/2)*t)
  let r := popResidual uniformMargins (2*n-1) (Real.sin t)
  let e := 1 / ((n : ℝ)^2 * (Real.sin t)^2)
  have htail : |f - c/(2*(n : ℝ)*Real.sin t)| ≤ e :=
    tc09_harmonic_tail_bound n hn hsin
  have hnorm : |c/(2*(n : ℝ)*Real.sin t)| ≤ |f| + e := by
    have h := abs_sub_le (c/(2*(n : ℝ)*Real.sin t)) f 0
    rw [sub_zero, sub_zero, abs_sub_comm] at h
    linarith
  have hc2 : c^2 ≤ |c| := by
    have h := Real.abs_cos_le_one ((2*(n : ℝ)+1/2)*t)
    change |c| ≤ 1 at h
    nlinarith [sq_abs c, mul_nonneg (abs_nonneg c) (sub_nonneg.mpr h)]
  have hsmall : c^2 / (4*(n : ℝ)*t) ≤
      |c/(2*(n : ℝ)*Real.sin t)| * Real.sqrt (Real.cos t) := by
    calc
      _ ≤ |c| / (4*(n : ℝ)*t) := div_le_div_of_nonneg_right hc2 (by positivity)
      _ ≤ |c| / (4*(n : ℝ)*Real.sin t) :=
        div_le_div_of_nonneg_left (abs_nonneg c) (by positivity)
          (mul_le_mul_of_nonneg_left (Real.sin_le htpos.le) (by positivity))
      _ = (|c| / (2*(n : ℝ)*Real.sin t)) * (1/2) := by ring
      _ ≤ (|c| / (2*(n : ℝ)*Real.sin t)) * Real.sqrt (Real.cos t) :=
        mul_le_mul_of_nonneg_left hrhalf (by positivity)
      _ = _ := by rw [abs_div, abs_of_pos (by positivity : 0 < 2*(n : ℝ)*Real.sin t)]
  have hsmall' : c^2 / (4*(n : ℝ)*t) ≤ |f| * Real.sqrt (Real.cos t) + e := by
    apply hsmall.trans
    calc
      _ ≤ (|f| + e) * Real.sqrt (Real.cos t) := mul_le_mul_of_nonneg_right hnorm hr.le
      _ = |f| * Real.sqrt (Real.cos t) + e * Real.sqrt (Real.cos t) := by ring
      _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right (by positivity) hr1)
  have hf : |f| * Real.sqrt (Real.cos t) ≤ Real.pi *
      (|r| * Real.cos t + |r - f/(Real.pi * Real.sqrt (Real.cos t))| * Real.cos t) := by
    have h : |f/(Real.pi * Real.sqrt (Real.cos t))| ≤
        |r| + |r - f/(Real.pi * Real.sqrt (Real.cos t))| := by
      have h := abs_sub_le (f/(Real.pi * Real.sqrt (Real.cos t))) r 0
      rw [sub_zero, sub_zero, abs_sub_comm] at h
      linarith
    have hmul := mul_le_mul_of_nonneg_right h (show 0 ≤ Real.pi * Real.cos t by positivity)
    have he : |f/(Real.pi * Real.sqrt (Real.cos t))| * (Real.pi * Real.cos t) =
        |f| * Real.sqrt (Real.cos t) := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hr]
      field_simp
      rw [hr2]
    rw [he] at hmul
    convert hmul using 1 <;> ring
  have hsinlower : 2*a ≤ Real.pi * Real.sin t := by
    have h := Real.mul_le_sin htpos.le (ht.2.trans hTp.le)
    have h' : (2*t)/Real.pi ≤ Real.sin t := by convert h using 1 <;> ring
    have h'' := (div_le_iff₀ Real.pi_pos).mp h'
    linarith [ht.1]
  have herr : 4 / ((n : ℝ)*(Real.sin t)^2) ≤ Real.pi^2 / ((n : ℝ)*a^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hsquares : (2*a)^2 ≤ (Real.pi * Real.sin t)^2 := by
      simpa only [pow_two] using mul_self_le_mul_self (show 0 ≤ 2*a by positivity) hsinlower
    calc
      _ = (n : ℝ) * (2*a)^2 := by ring
      _ ≤ (n : ℝ) * (Real.pi * Real.sin t)^2 := mul_le_mul_of_nonneg_left hsquares hp.le
      _ = _ := by ring
  change c^2/t ≤ (4*Real.pi*(n : ℝ)) *
    (|r| *Real.cos t + |r-f/(Real.pi*Real.sqrt (Real.cos t))| *Real.cos t) + _
  calc
    _ = (4*(n : ℝ)) * (c^2/(4*(n : ℝ)*t)) := by field_simp <;> ring
    _ ≤ (4*(n : ℝ)) * (|f| *Real.sqrt (Real.cos t)+e) :=
      mul_le_mul_of_nonneg_left hsmall' (by positivity)
    _ ≤ (4*(n : ℝ)) * (Real.pi *
        (|r| *Real.cos t + |r-f/(Real.pi*Real.sqrt (Real.cos t))| *Real.cos t)+e) :=
      mul_le_mul_of_nonneg_left (add_le_add hf le_rfl) (by positivity)
    _ = (4*Real.pi*(n : ℝ)) *
        (|r| *Real.cos t + |r-f/(Real.pi*Real.sqrt (Real.cos t))| *Real.cos t) +
          4/((n : ℝ)*(Real.sin t)^2) := by dsimp [e]; field_simp <;> ring
    _ ≤ _ := add_le_add le_rfl herr

/-- A lower bound for the actual amplification, uniform in the polynomial degree. -/
theorem tc09_amplification_cosine_lower (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (ha : 0 < a) (ha' : a ≤ 1/2) :
    (∫ t in a..(1/2 : ℝ), Real.cos ((2*(n : ℝ)+1/2)*t)^2/t) ≤
      2 * amplification uniformMargins (2*n-1) + 4*(Real.pi+4) +
        Real.pi^2 / ((n : ℝ)*a^2) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hTp : (1/2 : ℝ) < Real.pi/2 := by linarith [Real.two_le_pi]
  let R := fun t => |popResidual uniformMargins (2*n-1) (Real.sin t)| * Real.cos t
  let E := fun t => |popResidual uniformMargins (2*n-1) (Real.sin t) -
    tc09_harmonicTail n t/(Real.pi * Real.sqrt (Real.cos t))| * Real.cos t
  have hsub : Icc a (1/2 : ℝ) ⊆ Icc (0 : ℝ) (1/2) := by
    intro t ht
    exact ⟨ha.le.trans ht.1, ht.2⟩
  have hR := tc09_residual_sine_integrable (2*n-1) (by norm_num : (0 : ℝ) ≤ 1/2) hTp
  have hE := tc09_harmonic_weighted_error n hn (by norm_num : (0 : ℝ) ≤ 1/2) hTp
  have hRa : IntegrableOn R (Icc a (1/2 : ℝ)) := hR.mono_set hsub
  have hEa : IntegrableOn E (Icc a (1/2 : ℝ)) := hE.1.mono_set hsub
  have hRnonneg : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) (1/2))] R := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    exact Eventually.of_forall fun t ht => mul_nonneg (abs_nonneg _) (tc09_cos_positive hTp ht).le
  have hEnonneg : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) (1/2))] E := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    exact Eventually.of_forall fun t ht => mul_nonneg (abs_nonneg _) (tc09_cos_positive hTp ht).le
  have hRbound : (∫ t in Icc a (1/2 : ℝ), R t) ≤
      2 * expectation uniformMargins (fun x => |popResidual uniformMargins (2*n-1) x|) :=
    (setIntegral_mono_set hR hRnonneg (Eventually.of_forall hsub)).trans
      (tc09_residual_sine_l1_le _ (by norm_num) hTp)
  have hEbound : (∫ t in Icc a (1/2 : ℝ), E t) ≤ (Real.pi+4)/(Real.pi*(n : ℝ)) :=
    (setIntegral_mono_set hE.1 hEnonneg (Eventually.of_forall hsub)).trans hE.2
  have hcos : IntegrableOn (fun t => Real.cos ((2*(n : ℝ)+1/2)*t)^2/t)
      (Icc a (1/2 : ℝ)) := by
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.div (by fun_prop) continuousOn_id
    exact fun t ht => (ha.trans_le ht.1).ne'
  have hconst : IntegrableOn (fun _ : ℝ => Real.pi^2/((n : ℝ)*a^2))
      (Icc a (1/2 : ℝ)) volume := continuous_const.integrableOn_Icc
  have hscale : IntegrableOn (fun t => (4*Real.pi*(n : ℝ)) * (R t + E t))
      (Icc a (1/2 : ℝ)) volume := (hRa.add hEa).const_mul _
  have hi : (∫ t in Icc a (1/2 : ℝ), Real.cos ((2*(n : ℝ)+1/2)*t)^2/t) ≤
      (4*Real.pi*(n : ℝ)) *
        ((∫ t in Icc a (1/2 : ℝ), R t) + (∫ t in Icc a (1/2 : ℝ), E t)) +
          Real.pi^2 / ((n : ℝ)*a^2) := by
    have h := setIntegral_mono_on hcos
      (((hRa.add hEa).const_mul (4*Real.pi*(n : ℝ))).add hconst) measurableSet_Icc
      (fun t ht => tc09_cosine_residual_pointwise n hn ha ht)
    simp only [Pi.add_apply] at h
    rw [integral_add hscale hconst,
      integral_const_mul, integral_add hRa hEa, integral_const] at h
    have hvol : (volume.restrict (Icc a (1/2 : ℝ))).real univ =
        volume.real (Icc a (1/2 : ℝ)) := by
      simp only [Measure.real, Measure.restrict_apply_univ]
    rw [hvol, Real.volume_real_Icc_of_le ha'] at h
    simp only [smul_eq_mul] at h
    have hmul : ((1/2 : ℝ)-a) * (Real.pi^2/((n : ℝ)*a^2)) ≤
        Real.pi^2/((n : ℝ)*a^2) :=
      mul_le_of_le_one_left (by positivity) (by linarith)
    exact h.trans (add_le_add le_rfl hmul)
  have hEabs : 0 ≤ expectation uniformMargins (fun x => |popResidual uniformMargins (2*n-1) x|) :=
    integral_nonneg (fun _ => abs_nonneg _)
  have hv : 0 < residualVariance uniformMargins (2*n-1) :=
    (uniform_projection_variance (2*n-1) (by omega)).2.2.2
  have hamp : 4*Real.pi*(n : ℝ) *
      expectation uniformMargins (fun x => |popResidual uniformMargins (2*n-1) x|) ≤
      amplification uniformMargins (2*n-1) := by
    calc
      _ = expectation uniformMargins (fun x => |popResidual uniformMargins (2*n-1) x|) /
          (1/(4*Real.pi*(n : ℝ))) := by field_simp <;> ring
      _ ≤ _ := div_le_div_of_nonneg_left hEabs hv (tc09_variance_upper n hn)
  have hi' := hi.trans (add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add hRbound hEbound) (by positivity)) le_rfl)
  have he : (4*Real.pi*(n : ℝ)) *
      (2 * expectation uniformMargins (fun x => |popResidual uniformMargins (2*n-1) x|) +
        (Real.pi+4)/(Real.pi*(n : ℝ))) =
      2 * (4*Real.pi*(n : ℝ) * expectation uniformMargins
        (fun x => |popResidual uniformMargins (2*n-1) x|)) + 4*(Real.pi+4) := by
    field_simp <;> ring
  rw [he] at hi'
  rw [intervalIntegral.integral_of_le ha', ← integral_Icc_eq_integral_Ioc]
  linarith

/-- Divergence along all odd degrees, using a fixed interior interval for each lower bound. -/
theorem tc09_odd_amplification_diverges :
    Tendsto (fun n : ℕ => amplification uniformMargins (2*n-1)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  let L : ℝ := 4 * (max B 0 + 2*(Real.pi+4) + 2)
  let a : ℝ := (1/2) * Real.exp (-L)
  have hmax : 0 ≤ max B 0 := le_max_right B 0
  have hL : 0 < L := by dsimp [L]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have ha' : a ≤ 1/2 := by
    have he : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    dsimp [a]
    nlinarith
  have hlog : Real.log ((1/2 : ℝ)/a) = L := by
    rw [Real.log_div (by norm_num) ha.ne']
    dsimp [a]
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hlim := tc09_cosine_square_log_limit ha ha'
  rw [hlog] at hlim
  have hlo := (tendsto_order.mp hlim).1 (L/2-1) (by linarith)
  have hzero : Tendsto (fun n : ℕ => Real.pi^2 / ((n : ℝ)*a^2)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    simpa only [mul_comm] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop
        (sq_pos_of_pos ha)
  have hhi := (tendsto_order.mp hzero).2 1 (by norm_num)
  filter_upwards [hlo, hhi, eventually_ge_atTop 1] with n hlow hhigh hn
  have hmain := tc09_amplification_cosine_lower n hn ha ha'
  have hB : B ≤ max B 0 := le_max_left B 0
  dsimp [L] at hlow
  linarith

theorem tc09_uniform_projection_index (J : ℕ) (hJ : 1 ≤ J) :
    projection uniformMargins J = projection uniformMargins (2*((J+1)/2)-1) := by
  rw [tc04_uniform_projection_expansion, tc04_uniform_projection_expansion]
  have he : (2*((J+1)/2)-1+1)/2 = (J+1)/2 := by omega
  simp only [tc04_uniform_candidate, he]

theorem tc09_uniform_amplification_index (J : ℕ) (hJ : 1 ≤ J) :
    amplification uniformMargins J = amplification uniformMargins (2*((J+1)/2)-1) := by
  simp only [amplification, residualVariance, popResidual, tc09_uniform_projection_index J hJ]

/-- Uniform residual amplification diverges without an amplification hypothesis or endpoint estimate. -/
theorem uniform_amplification_diverges :
    Filter.Tendsto (amplification uniformMargins) Filter.atTop Filter.atTop := by
  have hindex : Tendsto (fun J : ℕ => (J+1)/2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop (2*N)] with J hJ
    omega
  have h := tc09_odd_amplification_diverges.comp hindex
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with J hJ
  exact (tc09_uniform_amplification_index J hJ).symm

end
end AronowAudit.P023.Wave1
