import Mathlib.Tactic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected

namespace AronowAudit.P015.TaylorCompletion
open Complex Set Filter Metric
open scoped Topology ENNReal NNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

def fc (z : ℂ) : ℂ := (1+Complex.exp (-z))⁻¹

lemma denominator_norm_ge_pi (z : ℂ) (hz : 1+Complex.exp (-z)=0) : Real.pi ≤ ‖z‖ := by
  have he : Complex.exp (-z)=Complex.exp (Real.pi*Complex.I) := by
    rw [Complex.exp_pi_mul_I]
    linear_combination hz
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have him := congrArg Complex.im hk
  simp only [Complex.neg_im, Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re,
    Complex.intCast_im, mul_zero, zero_mul, add_zero, zero_add, mul_one,
    Complex.re_ofNat] at him
  have hi : Real.pi ≤ |z.im| := by
    by_cases h : 0 ≤ k
    · have hc : (0:ℝ) ≤ k := by exact_mod_cast h
      rw [abs_of_nonpos (by nlinarith [Real.pi_pos] : z.im ≤ 0)]
      nlinarith [Real.pi_pos]
    · have hc : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      rw [abs_of_nonneg (by nlinarith [Real.pi_pos] : 0 ≤ z.im)]
      nlinarith [Real.pi_pos]
  exact hi.trans (Complex.abs_im_le_norm z)

lemma denominator_ne_zero (z : ℂ) (hz : ‖z‖ < Real.pi) : 1+Complex.exp (-z) ≠ 0 := by
  intro h
  exact (not_le_of_gt hz) (denominator_norm_ge_pi z h)

lemma differentiableAt_fc (z : ℂ) (hz : 1+Complex.exp (-z) ≠ 0) :
    DifferentiableAt ℂ fc z := by
  exact ((differentiableAt_const (1:ℂ)).add
    (Complex.differentiableAt_exp.comp z differentiableAt_id.neg)).inv hz

lemma analyticAt_fc_zero : AnalyticAt ℂ fc 0 := by
  exact ((analyticAt_const (𝕜:=ℂ) (v:=(1:ℂ))).add
    (analyticAt_cexp.comp (analyticAt_id.neg))).inv (by simp)

lemma series_radius_lower (s : FormalMultilinearSeries ℂ ℂ ℂ)
    (hs : HasFPowerSeriesAt fc s 0) : ENNReal.ofReal Real.pi ≤ s.radius := by
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro r hr hrpi
  have hri : (r:ℝ) < Real.pi := by simpa using hrpi
  obtain ⟨R,hrR,hRpi⟩ := exists_between hri
  let Rn : ℝ≥0 := ⟨R, lt_of_le_of_lt r.coe_nonneg hrR |>.le⟩
  have hd : DifferentiableOn ℂ fc (closedBall (0:ℂ) Rn) := by
    intro z hz
    apply (differentiableAt_fc z (denominator_ne_zero z ?_)).differentiableWithinAt
    have hh : ‖z‖ ≤ (Rn : ℝ) := by simpa only [mem_closedBall, dist_zero_right] using hz
    have he : (Rn : ℝ) = R := rfl
    rw [he] at hh
    exact hh.trans_lt hRpi
  have hp := hd.hasFPowerSeriesOnBall (show 0 < Rn from by exact_mod_cast (lt_of_le_of_lt r.coe_nonneg hrR))
  have heq := hs.eq_formalMultilinearSeries hp.hasFPowerSeriesAt
  rw [heq]
  exact (show (r:ℝ≥0∞) ≤ Rn from by exact_mod_cast hrR.le).trans hp.r_le

lemma series_radius_upper (s : FormalMultilinearSeries ℂ ℂ ℂ)
    (hs : HasFPowerSeriesAt fc s 0) : s.radius ≤ ENNReal.ofReal Real.pi := by
  by_contra h
  have hgt : ENNReal.ofReal Real.pi < s.radius := lt_of_not_ge h
  have hpos : 0 < s.radius := (ENNReal.ofReal_pos.mpr Real.pi_pos).trans hgt
  let F : ℂ → ℂ := fun z => (1+Complex.exp (-z))*s.sum z
  have hF : AnalyticOnNhd ℂ F (Metric.eball (0:ℂ) s.radius) := by
    intro z hz
    exact ((analyticAt_const.add (analyticAt_cexp.comp analyticAt_id.neg))).mul
      (s.analyticOnNhd z hz)
  obtain ⟨r,hr⟩ := hs
  have hnear : F =ᶠ[𝓝 (0:ℂ)] (fun _ => 1) := by
    have hd : ∀ᶠ z in 𝓝 (0:ℂ), 1+Complex.exp (-z) ≠ 0 :=
      ((continuous_const.add (Complex.continuous_exp.comp continuous_neg)).continuousAt).eventually_ne
        (by simp)
    filter_upwards [Metric.eball_mem_nhds (0:ℂ) hr.r_pos, hd] with z hz hden
    have he : s.sum z=fc z := by simpa only [zero_add] using (hr.sum hz).symm
    change (1+Complex.exp (-z))*s.sum z=1
    rw [he]
    exact mul_inv_cancel₀ hden
  have hpole : (Real.pi*Complex.I : ℂ) ∈ Metric.eball (0:ℂ) s.radius := by
    simpa [Metric.mem_eball, edist_dist, dist_zero_right, Complex.norm_mul,
      abs_of_pos Real.pi_pos] using hgt
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    isPreconnected_eball (by simpa using hpos) hnear hpole
  have he : Complex.exp (-(Real.pi*Complex.I)) = -1 := by
    rw [Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  simp only [F,he,add_neg_cancel,zero_mul] at heq
  exact zero_ne_one heq

theorem logistic_power_series_radius_completed :
    ∃ s : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun z : ℂ => (1+Complex.exp (-z))⁻¹) s 0 ∧
      s.radius=ENNReal.ofReal Real.pi := by
  obtain ⟨s,hs⟩ := analyticAt_fc_zero
  exact ⟨s,hs,le_antisymm (series_radius_upper s hs) (series_radius_lower s hs)⟩

end
end AronowAudit.P015.TaylorCompletion
