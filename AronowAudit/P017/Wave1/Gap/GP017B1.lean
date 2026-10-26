import AronowAudit.P017.P017_Audit
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Exact Gaussian tail identities and decay faster than every inverse positive power. -/

namespace AronowAudit.P017.Wave1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

/-! ## Exact Gaussian tail -/

private theorem normal_tail_identity_density (x : ℝ) :
    gaussianPDFReal 0 1 x =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

private theorem normal_tail_identity_density_deriv (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1)
      (-x * gaussianPDFReal 0 1 x) x := by
  have hd := ((hasDerivAt_pow 2 x).const_mul (-(1 / 2 : ℝ))).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  have hf : gaussianPDFReal 0 1 = fun y : ℝ =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * y ^ 2) :=
    funext normal_tail_identity_density
  simp only [hf]
  convert hd using 1
  norm_num
  ring

private theorem normal_tail_identity_second_integrable :
    Integrable (fun x : ℝ => x ^ 2 * gaussianPDFReal 0 1 x) := by
  have hi := (integrable_rpow_mul_exp_neg_mul_sq
    (b := (1 / 2 : ℝ)) (s := (2 : ℝ)) (by norm_num) (by norm_num)).const_mul
      (Real.sqrt (2 * Real.pi))⁻¹
  convert hi using 1
  ext x
  rw [normal_tail_identity_density, Real.rpow_two]
  ring

private theorem normal_tail_identity_boundary :
    Tendsto (fun x : ℝ => x * gaussianPDFReal 0 1 x) atTop (𝓝 0) := by
  have hsmall := rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
    (b := (1 / 2 : ℝ)) (by norm_num) (1 : ℝ)
  have he : Tendsto (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0))
  have hz := (hsmall.tendsto_zero_of_tendsto he).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert hz using 1
  · ext x
    rw [normal_tail_identity_density, Real.rpow_one]
    ring
  · ring

private theorem normal_tail_identity_density_tail (a : ℝ) :
    (∫ x in Ioi a, gaussianPDFReal 0 1 x) = normalCDF (-a) := by
  let γ : Measure ℝ := gaussianReal 0 1
  haveI : NullSingletonClass γ :=
    nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  have hmap : γ.map (fun x : ℝ => -x) = γ := by
    simpa only [neg_zero] using
      (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
  have hreflect : γ (Iic (-a)) = γ (Ici a) := by
    conv_lhs => rw [← hmap, Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1
    ext x
    simp
  have hatom : γ (Ioi a) = γ (Ici a) :=
    measure_congr (Ioi_ae_eq_Ici' (measure_singleton a))
  have hpdf : γ (Ioi a) = ENNReal.ofReal
      (∫ x in Ioi a, gaussianPDFReal 0 1 x) :=
    gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0) _
  have hnonneg : 0 ≤ ∫ x in Ioi a, gaussianPDFReal 0 1 x :=
    integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x)
  change _ = (γ (Iic (-a))).toReal
  rw [hreflect, ← hatom, hpdf, ENNReal.toReal_ofReal hnonneg]

private theorem normal_tail_identity_standard_ibp (a : ℝ) :
    (∫ x in Ioi a, x ^ 2 * gaussianPDFReal 0 1 x) =
      a * gaussianPDFReal 0 1 a + normalCDF (-a) := by
  have hsecond := normal_tail_identity_second_integrable.integrableOn (s := Ioi a)
  have hzero := (integrable_gaussianPDFReal 0 1).integrableOn (s := Ioi a)
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y * gaussianPDFReal 0 1 y)
      (gaussianPDFReal 0 1 x - x ^ 2 * gaussianPDFReal 0 1 x) x := by
    convert (hasDerivAt_id' x).mul (normal_tail_identity_density_deriv x) using 1
    ring
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := a) (fun x _ => hd x) (hzero.sub hsecond) normal_tail_identity_boundary
  rw [integral_sub hzero hsecond, normal_tail_identity_density_tail] at hftc
  linarith

private theorem normal_tail_identity_rescale (n : ℕ) (hn : 1 ≤ n) (c σ : ℝ)
    (hσ : 0 < σ) :
    normalTail n c σ =
      2 * (σ / sqrtN n) ^ 2 *
        ∫ z in Ioi (c / (σ / sqrtN n)), z ^ 2 * gaussianPDFReal 0 1 z := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsqrt : 0 < sqrtN n := Real.sqrt_pos.mpr hnpos
  have hsq : sqrtN n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  let s : ℝ := σ / sqrtN n
  have hs : 0 < s := div_pos hσ hsqrt
  have hπ : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  let F : ℝ → ℝ := fun x => x ^ 2 * (sqrtN n / (σ * Real.sqrt (2 * Real.pi))) *
    Real.exp (-(x ^ 2 * (n : ℝ)) / (2 * σ ^ 2))
  have he (z : ℝ) : -((s * z) ^ 2 * (n : ℝ)) / (2 * σ ^ 2) =
      -(1 / 2 : ℝ) * z ^ 2 := by
    dsimp [s]
    rw [← hsq]
    field_simp [ne_of_gt hσ, ne_of_gt hsqrt]
    <;> ring
  have hF (z : ℝ) : F (s * z) = s * (z ^ 2 * gaussianPDFReal 0 1 z) := by
    dsimp only [F]
    rw [he, normal_tail_identity_density]
    dsimp [s]
    field_simp [ne_of_gt hσ, ne_of_gt hsqrt, ne_of_gt hπ]
    <;> ring
  have hsub := integral_comp_mul_left_Ioi' F (c / s) hs
  have hbound : s * (c / s) = c := by field_simp [ne_of_gt hs]
  rw [hbound] at hsub
  simp only [smul_eq_mul] at hsub
  have hfun : (fun z => F (s * z)) =
      (fun z => s * (z ^ 2 * gaussianPDFReal 0 1 z)) := funext hF
  rw [hfun, integral_const_mul] at hsub
  change 2 * (∫ x in Ioi c, F x) = _
  rw [← hsub]
  dsimp [s]
  ring

private theorem normal_tail_identity_sqrt_constant :
    2 / Real.sqrt (2 * Real.pi) = Real.sqrt (2 / Real.pi) := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hroot : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hl : 0 ≤ 2 / Real.sqrt (2 * Real.pi) := by positivity
  have hr : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have hs₁ := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hs₂ := Real.sq_sqrt (show 0 ≤ 2 / Real.pi by positivity)
  have hsq : (2 / Real.sqrt (2 * Real.pi)) ^ 2 =
      (Real.sqrt (2 / Real.pi)) ^ 2 := by
    rw [div_pow, hs₁, hs₂]
    field_simp [ne_of_gt hp]
    <;> ring
  nlinarith

theorem normal_tail_identity_proof (n : ℕ) (hn : 1 ≤ n) (c σ : ℝ)
    (hc : 0 < c) (hσ : 0 < σ) :
    normalTail n c σ =
      c * σ * Real.sqrt (2 / Real.pi) * Real.exp (-(c ^ 2 * (n : ℝ)) / (2 * σ ^ 2)) / sqrtN n +
      2 * σ ^ 2 * normalCDF (-c * sqrtN n / σ) / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsqrt : 0 < sqrtN n := Real.sqrt_pos.mpr hnpos
  have hsq : sqrtN n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hπ : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have ha : c / (σ / sqrtN n) = c * sqrtN n / σ := by
    field_simp [ne_of_gt hσ, ne_of_gt hsqrt]
    <;> ring
  have hexp : -(1 / 2 : ℝ) * (c / (σ / sqrtN n)) ^ 2 =
      -(c ^ 2 * (n : ℝ)) / (2 * σ ^ 2) := by
    rw [ha, ← hsq]
    field_simp [ne_of_gt hσ]
    <;> ring
  rw [normal_tail_identity_rescale n hn c σ hσ, normal_tail_identity_standard_ibp,
    normal_tail_identity_density, hexp]
  have harg : -(c / (σ / sqrtN n)) = -c * sqrtN n / σ := by rw [ha]; ring
  rw [harg]
  have hconst := normal_tail_identity_sqrt_constant
  rw [← hconst, ← hsq]
  field_simp [ne_of_gt hσ, ne_of_gt hsqrt, ne_of_gt hπ]
  <;> ring

/-! ## Every positive power times the tail tends to zero -/

private theorem normal_tail_limits_even_integrable (j : ℕ) :
    Integrable (fun z : ℝ => z ^ (2 * j + 2) * gaussianPDFReal 0 1 z) := by
  have hi := (integrable_rpow_mul_exp_neg_mul_sq
    (b := (1 / 2 : ℝ)) (s := ((2 * j + 2 : ℕ) : ℝ))
    (by norm_num)
    (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))).const_mul
      (Real.sqrt (2 * Real.pi))⁻¹
  convert hi using 1
  ext z
  rw [normal_tail_identity_density, Real.rpow_natCast]
  ring

private theorem normal_tail_limits_even_nonneg (j : ℕ) (z : ℝ) :
    0 ≤ z ^ (2 * j + 2) * gaussianPDFReal 0 1 z := by
  have he : 2 * j + 2 = 2 * (j + 1) := by omega
  rw [he, pow_mul]
  exact mul_nonneg (pow_nonneg (sq_nonneg z) _) (gaussianPDFReal_nonneg _ _ _)

/-- The fixed constant uses a genuine finite even moment of the standard normal. -/
private theorem normal_tail_limits_high_moment_bound (c σ : ℝ)
    (hc : 0 < c) (hσ : 0 < σ) (j n : ℕ) (hn : 1 ≤ n) :
    0 ≤ normalTail n c σ ∧
      normalTail n c σ ≤
        (2 * σ ^ (2 * j + 2) *
          (∫ z : ℝ, z ^ (2 * j + 2) * gaussianPDFReal 0 1 z) / c ^ (2 * j)) /
          (n : ℝ) ^ (j + 1) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsqrt : 0 < sqrtN n := Real.sqrt_pos.mpr hnpos
  have hsq : sqrtN n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  let s : ℝ := σ / sqrtN n
  let a : ℝ := c / s
  let M : ℝ := ∫ z : ℝ, z ^ (2 * j + 2) * gaussianPDFReal 0 1 z
  have hs : 0 < s := div_pos hσ hsqrt
  have ha : 0 < a := div_pos hc hs
  have hM : 0 ≤ M := integral_nonneg (normal_tail_limits_even_nonneg j)
  have hi := normal_tail_limits_even_integrable j
  have hpoint (z : ℝ) (hz : z ∈ Ioi a) :
      z ^ 2 * gaussianPDFReal 0 1 z ≤
        (z ^ (2 * j + 2) * gaussianPDFReal 0 1 z) / a ^ (2 * j) := by
    have hzpos : 0 < z := lt_trans ha hz
    have hp : a ^ (2 * j) ≤ z ^ (2 * j) :=
      pow_le_pow_left₀ ha.le hz.le _
    apply (le_div_iff₀ (pow_pos ha _)).mpr
    have hh := mul_le_mul_of_nonneg_left hp
      (mul_nonneg (sq_nonneg z) (gaussianPDFReal_nonneg 0 1 z))
    simpa only [pow_add, pow_two, mul_assoc, mul_comm, mul_left_comm] using hh
  have htail : (∫ z in Ioi a, z ^ 2 * gaussianPDFReal 0 1 z) ≤ M / a ^ (2 * j) := by
    calc
      _ ≤ ∫ z in Ioi a,
          (z ^ (2 * j + 2) * gaussianPDFReal 0 1 z) / a ^ (2 * j) := by
        apply integral_mono_ae normal_tail_identity_second_integrable.integrableOn
          (hi.integrableOn.div_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
        exact hpoint z hz
      _ = (∫ z in Ioi a, z ^ (2 * j + 2) * gaussianPDFReal 0 1 z) / a ^ (2 * j) :=
        integral_div _ _
      _ ≤ M / a ^ (2 * j) :=
        div_le_div_of_nonneg_right
          (setIntegral_le_integral hi (ae_of_all _ (normal_tail_limits_even_nonneg j)))
          (pow_nonneg ha.le _)
  have hscale : s ^ (2 * j + 2) = σ ^ (2 * j + 2) / (n : ℝ) ^ (j + 1) := by
    have he : 2 * j + 2 = 2 * (j + 1) := by omega
    dsimp only [s]
    rw [div_pow, he, pow_mul (sqrtN n), hsq]
  have halgebra : 2 * s ^ 2 * (M / a ^ (2 * j)) =
      (2 * σ ^ (2 * j + 2) * M / c ^ (2 * j)) / (n : ℝ) ^ (j + 1) := by
    calc
      _ = 2 * s ^ (2 * j + 2) * M / c ^ (2 * j) := by
        have key : ∀ (s' M' c' : ℝ), 2 * s' ^ 2 * (M' / (c' / s') ^ (2 * j)) =
            2 * s' ^ (2 * j + 2) * M' / c' ^ (2 * j) := by
          intro s' M' c'
          rw [div_pow, pow_add s' (2 * j) 2, div_div_eq_mul_div]
          ring
        exact key s M c
      _ = _ := by rw [hscale]; ring
  rw [normal_tail_identity_rescale n hn c σ hσ]
  change 0 ≤ 2 * s ^ 2 * (∫ z in Ioi a, z ^ 2 * gaussianPDFReal 0 1 z) ∧ _
  constructor
  · exact mul_nonneg (by positivity)
      (integral_nonneg (fun z => mul_nonneg (sq_nonneg z) (gaussianPDFReal_nonneg _ _ _)))
  · exact (mul_le_mul_of_nonneg_left htail (by positivity)).trans_eq halgebra

private theorem normal_tail_limits_all_powers (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ)
    (k : ℝ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ k * normalTail n c σ) atTop (𝓝 0) := by
  obtain ⟨j : ℕ, hj⟩ := exists_nat_gt k
  let K : ℝ := 2 * σ ^ (2 * j + 2) *
    (∫ z : ℝ, z ^ (2 * j + 2) * gaussianPDFReal 0 1 z) / c ^ (2 * j)
  have hdiff : 0 < ((j + 1 : ℕ) : ℝ) - k := by
    push_cast
    linarith
  have hz : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (k - ((j + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop hdiff).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    convert h.const_mul K using 1 <;> simp only [neg_sub, mul_zero, Function.comp_def]
  apply squeeze_zero' _ _ hz
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) 
      (normal_tail_limits_high_moment_bound c σ hc hσ j n hn).1
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hb := (normal_tail_limits_high_moment_bound c σ hc hσ j n hn).2
    calc
      (n : ℝ) ^ k * normalTail n c σ ≤ (n : ℝ) ^ k * (K / (n : ℝ) ^ (j + 1)) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = K * (n : ℝ) ^ (k - ((j + 1 : ℕ) : ℝ)) := by
        rw [Real.rpow_sub hnpos, Real.rpow_natCast]
        ring

theorem normal_tail_limits_proof (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ) :
    Tendsto (fun n : ℕ => (n : ℝ) * normalTail n c σ) atTop (𝓝 0) ∧
    ∀ k : ℝ, 0 < k → Tendsto (fun n : ℕ => (n : ℝ) ^ k * normalTail n c σ) atTop (𝓝 0) := by
  constructor
  · simpa only [Real.rpow_one] using
      normal_tail_limits_all_powers c σ hc hσ 1 (by norm_num)
  · exact normal_tail_limits_all_powers c σ hc hσ






end
end AronowAudit.P017.Wave1
