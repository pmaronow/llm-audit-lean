import AronowAudit.P001.P001_Foundations
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGLP0013B1r2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-! The logistic density normalizes the Cauchy conditional densities in the second coordinate.
The exceptional marginal slice is handled with a lower nonnegative integral throughout. -/

lemma t36B1r2_exp_two (x : ℝ) : Real.exp (2 * x) = (Real.exp x) ^ 2 := by
  simpa using Real.exp_nat_mul x 2

lemma t36B1r2_smooth : ContDiff ℝ ⊤ smoothSlicePDF := by
  have he : ContDiff ℝ ⊤ (fun z : ℝ × ℝ => Real.exp z.1) :=
    Real.contDiff_exp.comp contDiff_fst
  unfold smoothSlicePDF
  refine ((he.div (contDiff_const.add he) (fun z => by positivity)).pow 2).div ?_ ?_
  · fun_prop
  · intro z
    positivity

lemma t36B1r2_positive (z : ℝ × ℝ) : 0 < smoothSlicePDF z := by
  unfold smoothSlicePDF
  positivity

def t36B1r2_logistic (x : ℝ) : ℝ := Real.exp x / (1 + Real.exp x) ^ 2

lemma t36B1r2_logistic_nonneg (x : ℝ) : 0 ≤ t36B1r2_logistic x := by
  unfold t36B1r2_logistic
  positivity

lemma t36B1r2_logistic_continuous : Continuous t36B1r2_logistic := by
  unfold t36B1r2_logistic
  exact Real.continuous_exp.div ((continuous_const.add Real.continuous_exp).pow 2)
    (fun x => by positivity)

lemma t36B1r2_logistic_left_bound (x : ℝ) : t36B1r2_logistic x ≤ Real.exp x := by
  unfold t36B1r2_logistic
  apply div_le_self (Real.exp_pos x).le
  nlinarith [Real.exp_pos x, sq_nonneg (Real.exp x)]

lemma t36B1r2_logistic_right_bound (x : ℝ) : t36B1r2_logistic x ≤ Real.exp (-x) := by
  unfold t36B1r2_logistic
  calc
    Real.exp x / (1 + Real.exp x) ^ 2 ≤ Real.exp x / (Real.exp x) ^ 2 :=
      div_le_div_of_nonneg_left (Real.exp_pos x).le (by positivity)
        (by nlinarith [Real.exp_pos x])
    _ = (Real.exp x)⁻¹ := by field_simp
    _ = Real.exp (-x) := (Real.exp_neg x).symm

lemma t36B1r2_logistic_integrable : Integrable t36B1r2_logistic volume := by
  have hl : IntegrableOn t36B1r2_logistic (Set.Iic (0 : ℝ)) := by
    apply (integrableOn_exp_Iic 0).mono' t36B1r2_logistic_continuous.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (t36B1r2_logistic_nonneg x)]
      exact t36B1r2_logistic_left_bound x
  have hr : IntegrableOn t36B1r2_logistic (Set.Ioi (0 : ℝ)) := by
    apply (integrableOn_exp_neg_Ioi 0).mono' t36B1r2_logistic_continuous.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (t36B1r2_logistic_nonneg x)]
      exact t36B1r2_logistic_right_bound x
  have h := hl.union hr
  rw [Set.Iic_union_Ioi] at h
  exact integrableOn_univ.mp h

lemma t36B1r2_logistic_derivative (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp t / (1 + Real.exp t)) (t36B1r2_logistic x) x := by
  convert (Real.hasDerivAt_exp x).div
    ((hasDerivAt_const x (1 : ℝ)).add (Real.hasDerivAt_exp x))
    (show (1 : ℝ) + Real.exp x ≠ 0 by positivity) using 1 <;>
    dsimp [t36B1r2_logistic] <;> ring

lemma t36B1r2_logistic_primitive_eq (x : ℝ) :
    Real.exp x / (1 + Real.exp x) = 1 / (1 + Real.exp (-x)) := by
  rw [Real.exp_neg]
  field_simp
  ring

lemma t36B1r2_logistic_mass : (∫ x, t36B1r2_logistic x) = 1 := by
  have hb : Tendsto (fun x : ℝ => Real.exp x / (1 + Real.exp x)) atBot (𝓝 0) := by
    convert Real.tendsto_exp_atBot.div
      (tendsto_const_nhds.add Real.tendsto_exp_atBot) (by norm_num : (1 : ℝ) + 0 ≠ 0)
      using 1 <;> norm_num
  have ht : Tendsto (fun x : ℝ => Real.exp x / (1 + Real.exp x)) atTop (𝓝 1) := by
    simp_rw [t36B1r2_logistic_primitive_eq]
    convert (tendsto_const_nhds.div
      (tendsto_const_nhds.add Real.tendsto_exp_neg_atTop_nhds_zero)
      (by norm_num : (1 : ℝ) + 0 ≠ 0) :
      Tendsto (fun x : ℝ => 1 / (1 + Real.exp (-x))) atTop (𝓝 (1 / (1 + 0 : ℝ))))
      using 1 <;> norm_num
  simpa using integral_of_hasDerivAt_of_tendsto t36B1r2_logistic_derivative
    t36B1r2_logistic_integrable hb ht

def t36B1r2_scale (x : ℝ) : ℝ≥0 := ⟨(Real.exp x)⁻¹, by positivity⟩

lemma t36B1r2_scale_ne_zero (x : ℝ) : t36B1r2_scale x ≠ 0 := by
  apply ne_of_gt
  change 0 < (Real.exp x)⁻¹
  positivity

lemma t36B1r2_cauchy_factorization (x y : ℝ) :
    smoothSlicePDF (x, y) =
      t36B1r2_logistic x * cauchyPDFReal 0 (t36B1r2_scale x) y := by
  rw [smoothSlicePDF, cauchyPDFReal_def', t36B1r2_logistic]
  change (Real.exp x / (1 + Real.exp x)) ^ 2 /
      (Real.pi * (1 + y ^ 2 * Real.exp (2 * x))) =
    Real.exp x / (1 + Real.exp x) ^ 2 *
      (Real.pi⁻¹ * ((Real.exp x)⁻¹)⁻¹ * (1 + ((y - 0) / (Real.exp x)⁻¹) ^ 2)⁻¹)
  rw [t36B1r2_exp_two]
  simp only [inv_inv, sub_zero, div_inv_eq_mul, mul_pow]
  field_simp
  <;> ring

lemma t36B1r2_conditional_cauchy (x : ℝ) :
    Integrable (fun y : ℝ => smoothSlicePDF (x, y)) volume ∧
      (∫ y : ℝ, smoothSlicePDF (x, y)) = t36B1r2_logistic x := by
  have he : (fun y : ℝ => smoothSlicePDF (x, y)) =
      (fun y => t36B1r2_logistic x * cauchyPDFReal 0 (t36B1r2_scale x) y) :=
    funext (t36B1r2_cauchy_factorization x)
  rw [he]
  constructor
  · exact (integrable_cauchyPDFReal 0).const_mul (t36B1r2_logistic x)
  · rw [integral_const_mul, integral_cauchyPDFReal_eq_one 0 (t36B1r2_scale_ne_zero x), mul_one]

lemma t36B1r2_conditional_lintegral (x : ℝ) :
    (∫⁻ y : ℝ, ENNReal.ofReal (smoothSlicePDF (x, y))) =
      ENNReal.ofReal (t36B1r2_logistic x) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (t36B1r2_conditional_cauchy x).1
    (ae_of_all _ fun y => (t36B1r2_positive (x, y)).le), (t36B1r2_conditional_cauchy x).2]

lemma t36B1r2_joint_lintegral :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (smoothSlicePDF z)) = 1 := by
  change (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (smoothSlicePDF z)
    ∂((volume : Measure ℝ).prod volume)) = 1
  rw [lintegral_prod _ t36B1r2_smooth.continuous.measurable.ennreal_ofReal.aemeasurable]
  simp_rw [t36B1r2_conditional_lintegral]
  rw [← ofReal_integral_eq_lintegral_ofReal t36B1r2_logistic_integrable
    (ae_of_all _ t36B1r2_logistic_nonneg), t36B1r2_logistic_mass]
  norm_num

lemma t36B1r2_joint_normalization :
    Integrable smoothSlicePDF volume ∧ (∫ z, smoothSlicePDF z) = 1 := by
  have hm := t36B1r2_smooth.continuous.aestronglyMeasurable (μ := (volume : Measure (ℝ × ℝ)))
  have hn : 0 ≤ᵐ[volume] smoothSlicePDF := ae_of_all _ fun z => (t36B1r2_positive z).le
  have hi : Integrable smoothSlicePDF volume :=
    (lintegral_ofReal_ne_top_iff_integrable hm hn).mp (by rw [t36B1r2_joint_lintegral]; simp)
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hm, t36B1r2_joint_lintegral]
  simp

lemma t36B1r2_zero_slice_lower_bound (x : ℝ) (hx : 0 ≤ x) :
    1 / (4 * Real.pi) ≤ smoothSlicePDF (x, 0) := by
  have he : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx
  have hr : (1 : ℝ) / 2 ≤ Real.exp x / (1 + Real.exp x) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have hs : (1 : ℝ) / 4 ≤ (Real.exp x / (1 + Real.exp x)) ^ 2 := by
    nlinarith [sq_nonneg (Real.exp x / (1 + Real.exp x) - 1 / 2)]
  unfold smoothSlicePDF
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero, mul_one]
  calc
    1 / (4 * Real.pi) = (1 / 4 : ℝ) / Real.pi := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hs Real.pi_pos.le

lemma t36B1r2_zero_slice_infinite :
    (∫⁻ x : ℝ, ENNReal.ofReal (smoothSlicePDF (x, 0))) = ∞ := by
  have hc : ENNReal.ofReal (1 / (4 * Real.pi)) ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.ofReal_pos.mpr (by positivity)
  apply top_unique
  calc
    ∞ = ∫⁻ _ : ℝ in Set.Ici 0, ENNReal.ofReal (1 / (4 * Real.pi)) := by
      rw [setLIntegral_const, Real.volume_Ici, ENNReal.mul_top hc]
    _ ≤ ∫⁻ x : ℝ in Set.Ici 0, ENNReal.ofReal (smoothSlicePDF (x, 0)) :=
      setLIntegral_mono' measurableSet_Ici fun x hx =>
        ENNReal.ofReal_le_ofReal (t36B1r2_zero_slice_lower_bound x hx)
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal (smoothSlicePDF (x, 0)) :=
      setLIntegral_le_lintegral _ _

lemma t36B1r2_slice_left_bound (x y : ℝ) :
    smoothSlicePDF (x, y) ≤ Real.exp (2 * x) / Real.pi := by
  have he := Real.exp_pos x
  have hr : Real.exp x / (1 + Real.exp x) ≤ Real.exp x :=
    div_le_self he.le (by linarith)
  have hs : (Real.exp x / (1 + Real.exp x)) ^ 2 ≤ (Real.exp x) ^ 2 :=
    (sq_le_sq₀ (by positivity) he.le).mpr hr
  have hd : Real.pi ≤ Real.pi * (1 + y ^ 2 * (Real.exp x) ^ 2) := by
    nlinarith [mul_nonneg Real.pi_pos.le (mul_nonneg (sq_nonneg y) (sq_nonneg (Real.exp x)))]
  unfold smoothSlicePDF
  rw [t36B1r2_exp_two]
  calc
    _ ≤ (Real.exp x) ^ 2 / (Real.pi * (1 + y ^ 2 * (Real.exp x) ^ 2)) :=
      div_le_div_of_nonneg_right hs (by positivity)
    _ ≤ (Real.exp x) ^ 2 / Real.pi :=
      div_le_div_of_nonneg_left (sq_nonneg _) Real.pi_pos hd

lemma t36B1r2_slice_right_bound (x y : ℝ) (hy : y ≠ 0) :
    smoothSlicePDF (x, y) ≤ Real.exp ((-2) * x) / (Real.pi * y ^ 2) := by
  have hr : Real.exp x / (1 + Real.exp x) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hs : (Real.exp x / (1 + Real.exp x)) ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ (by positivity) (by norm_num : (0 : ℝ) ≤ 1)).mpr hr
  have hd : Real.pi * (y ^ 2 * Real.exp (2 * x)) ≤
      Real.pi * (1 + y ^ 2 * Real.exp (2 * x)) := by
    nlinarith [Real.pi_pos]
  have hdy : 0 < Real.pi * (y ^ 2 * Real.exp (2 * x)) := by positivity
  unfold smoothSlicePDF
  calc
    _ ≤ 1 / (Real.pi * (1 + y ^ 2 * Real.exp (2 * x))) :=
      div_le_div_of_nonneg_right hs (by positivity)
    _ ≤ 1 / (Real.pi * (y ^ 2 * Real.exp (2 * x))) :=
      div_le_div_of_nonneg_left (by norm_num) hdy hd
    _ = Real.exp ((-2) * x) / (Real.pi * y ^ 2) := by
      rw [show (-2 : ℝ) * x = -(2 * x) by ring, Real.exp_neg]
      ring

lemma t36B1r2_nonzero_slice_integrable (y : ℝ) (hy : y ≠ 0) :
    Integrable (fun x : ℝ => smoothSlicePDF (x, y)) volume := by
  have hm : Continuous (fun x : ℝ => smoothSlicePDF (x, y)) :=
    t36B1r2_smooth.continuous.comp (continuous_id.prodMk continuous_const)
  have hl : IntegrableOn (fun x : ℝ => smoothSlicePDF (x, y)) (Set.Iic 0) := by
    apply ((integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 2) 0).div_const Real.pi).mono'
      hm.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (t36B1r2_positive (x, y)).le]
      exact t36B1r2_slice_left_bound x y
  have hr : IntegrableOn (fun x : ℝ => smoothSlicePDF (x, y)) (Set.Ioi 0) := by
    apply ((integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).div_const
      (Real.pi * y ^ 2)).mono' hm.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (t36B1r2_positive (x, y)).le]
      exact t36B1r2_slice_right_bound x y hy
  have h := hl.union hr
  rw [Set.Iic_union_Ioi] at h
  exact integrableOn_univ.mp h

theorem infinite_marginal_slice_counterexample_proof : ContDiff ℝ ⊤ smoothSlicePDF ∧ (∀ z, 0 < smoothSlicePDF z) ∧
   Integrable smoothSlicePDF volume ∧ (∫ z, smoothSlicePDF z)=1 ∧
   (∫⁻ x : ℝ, ENNReal.ofReal (smoothSlicePDF (x,0)))=∞ ∧
   (∀ y : ℝ, y≠0 → Integrable (fun x => smoothSlicePDF (x,y)) volume) := by
  exact ⟨t36B1r2_smooth, t36B1r2_positive, t36B1r2_joint_normalization.1,
    t36B1r2_joint_normalization.2, t36B1r2_zero_slice_infinite, t36B1r2_nonzero_slice_integrable⟩

end
end AronowAudit.P001.Wave1
