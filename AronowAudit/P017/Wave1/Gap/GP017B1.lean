import AronowAudit.P017.P017_Audit
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
Draft for dd-GP017B1. No Lean process was run.
The original held declarations are used only by the three `type_of%` checks.
See the run report for the outstanding companion-proof dependency of record 4.
-/

namespace AronowAudit.P017.Wave1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

/-! ## Record 1: exact Gaussian tail -/

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

example : type_of% @AronowAudit.P017.normal_tail_identity := normal_tail_identity_proof

/-! ## Record 2: every positive power times the tail tends to zero -/

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

example : type_of% @AronowAudit.P017.normal_tail_limits := normal_tail_limits_proof

/-! ## Record 4: arbitrarily slow outlier probabilities -/

private theorem slow_outlier_counterexample_dyadic_cofinal :
    Tendsto (fun k : ℕ => 2 ^ k) atTop atTop := by
  exact tendsto_atTop_mono (fun k => (Nat.lt_two_pow_self (n := k)).le) tendsto_id

private theorem slow_outlier_counterexample_dyadic_growth (α : ℝ) (hα : 0 < α) :
    Tendsto (fun k : ℕ => ((2 ^ k : ℕ) : ℝ) ^ α * slowP (2 ^ k)) atTop atTop := by
  let d : ℝ := α * Real.log 2
  have hd : 0 < d := mul_pos hα (Real.log_pos (by norm_num))
  have hx : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun k : ℕ => Real.exp (d * ((k : ℝ) + 1)) / ((k : ℝ) + 1))
      atTop atTop := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (tendsto_exp_mul_div_rpow_atTop 1 d hd).comp hx
  have hh := Tendsto.const_mul_atTop (Real.exp_pos (-d)) hg
  apply hh.congr'
  filter_upwards [] with k
  rw [slow_probability_numbers.2.2 k]
  push_cast
  rw [Real.rpow_def_of_pos (by positivity : 0 < (2 : ℝ) ^ k), Real.log_pow]
  have he : (k : ℝ) * Real.log 2 * α = -d + d * ((k : ℝ) + 1) := by dsimp [d]; ring
  rw [he, Real.exp_add]
  ring

private theorem slow_outlier_counterexample_no_polynomial (α : ℝ) (hα : 0 < α) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, slowP n ≤ C / (n : ℝ) ^ α := by
  rintro ⟨C, hC, hbound⟩
  have hsub := slow_outlier_counterexample_dyadic_cofinal.eventually hbound
  have hgrowth := (slow_outlier_counterexample_dyadic_growth α hα).eventually
    (eventually_gt_atTop C)
  obtain ⟨k, hk, hkg⟩ := (hsub.and hgrowth).exists
  have hpos : 0 < ((2 ^ k : ℕ) : ℝ) ^ α := by positivity
  have hupper : ((2 ^ k : ℕ) : ℝ) ^ α * slowP (2 ^ k) ≤ C := by
    have hb := (le_div_iff₀ hpos).mp hk
    nlinarith
  linarith

/-- Only the indicated second-moment lower bound is needed from the companion
witness; the contradiction already works with dyadic exponent one. -/
private theorem slow_outlier_counterexample_not_small
    (hlower : ∀ n : ℕ, 4 ≤ n →
      100 * ((n : ℝ) - 4) * slowP n ≤
        ∫ s, rareRemainder slowP n s ^ 2 ∂iidSamples slowPopulation) :
    ¬ SmallRemainderMS (iidSamples slowPopulation) (rareRemainder slowP) := by
  intro hsmall
  let E : ℕ → ℝ := fun n => ∫ s, rareRemainder slowP n s ^ 2 ∂iidSamples slowPopulation
  have hE (n : ℕ) : 0 ≤ E n := integral_nonneg (fun s => sq_nonneg _)
  change Tendsto (fun n => sqrtN n * E n) atTop (𝓝 0) at hsmall
  have hlow : ∀ᶠ n : ℕ in atTop,
      50 * (n : ℝ) * slowP n ≤ sqrtN n * E n := by
    filter_upwards [eventually_ge_atTop (8 : ℕ)] with n hn
    have hnreal : (8 : ℝ) ≤ n := by exact_mod_cast hn
    have hroot : 1 ≤ sqrtN n := Real.one_le_sqrt.mpr (by linarith)
    have hp := (slow_probability_positive_limit.1 n).1
    have hb := hlower n (by omega)
    have hmul : E n ≤ sqrtN n * E n := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hroot (hE n)
    have hgap := mul_nonneg (show 0 ≤ (n : ℝ) - 8 by linarith) hp.le
    dsimp only [E] at hmul ⊢
    nlinarith
  have hdyadic : Tendsto (fun k : ℕ =>
      50 * ((2 ^ k : ℕ) : ℝ) * slowP (2 ^ k)) atTop atTop := by
    have h := Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 50)
      (slow_outlier_counterexample_dyadic_growth 1 (by norm_num))
    simpa only [Real.rpow_one, mul_assoc] using h
  have hlarge := hdyadic.eventually (eventually_gt_atTop (1 : ℝ))
  have hupper := (hsmall.comp slow_outlier_counterexample_dyadic_cofinal).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hlower' := slow_outlier_counterexample_dyadic_cofinal.eventually hlow
  obtain ⟨k, hk₁, hk₂, hk₃⟩ := (hlarge.and (hupper.and hlower')).exists
  change sqrtN (2 ^ k) * E (2 ^ k) < 1 at hk₂
  linarith

/-- A concrete positive sequence that is slower than any specified positive null
sequence. The value at zero does not require positivity of the specified rate. -/
private theorem slow_outlier_counterexample_slower_rate (r : ℕ → ℝ)
    (hr : ∀ n : ℕ, 1 ≤ n → 0 < r n) (hrlim : Tendsto r atTop (𝓝 0)) :
    ∃ p : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → 0 < p n ∧ p n ≤ 1) ∧
      Tendsto p atTop (𝓝 0) ∧ Tendsto (fun n => p n / r n) atTop atTop := by
  let p : ℕ → ℝ := fun n => min 1 (Real.sqrt (r n))
  have hp (n : ℕ) (hn : 1 ≤ n) : 0 < p n ∧ p n ≤ 1 := by
    exact ⟨lt_min (by norm_num) (Real.sqrt_pos.mpr (hr n hn)), min_le_left _ _⟩
  have hsqrt : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hrlim.sqrt
  have hplim : Tendsto p atTop (𝓝 0) := by
    simpa only [min_eq_right (by norm_num : (0 : ℝ) ≤ 1)] using
      (tendsto_const_nhds (x := (1 : ℝ))).min hsqrt
  have hsqrt' : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hsqrt, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact Real.sqrt_pos.mpr (hr n hn)
  have hinv := tendsto_inv_nhdsGT_zero.comp hsqrt'
  have hratio : Tendsto (fun n => p n / r n) atTop atTop := by
    apply hinv.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hrlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hsmall
    have hrpos := hr n hn
    have hspos : 0 < Real.sqrt (r n) := Real.sqrt_pos.mpr hrpos
    have hpval : p n = Real.sqrt (r n) :=
      min_eq_right (Real.sqrt_le_one.mpr hsmall.le)
    rw [hpval]
    simp only [Function.comp_apply]
    have hsquare := Real.sq_sqrt hrpos.le
    rw [eq_div_iff (ne_of_gt hrpos), inv_mul_eq_div, div_eq_iff (ne_of_gt hspos)]
    nlinarith [hsquare]
  exact ⟨p, hp, hplim, hratio⟩

/-
The companion `arbitrary_outlier_sequence` has no proof in this worktree.
The next helper is an explicit dependency interface, not a replacement proof of
that companion and not the requested final theorem. Its assumption is exactly
the companion's frozen proposition, read by `type_of%`, never its held proof.
Once a genuine companion proof has been imported, the assembly below discharges
all remaining clauses of record 4 with no extra assumptions on the final node.
-/
private theorem slow_outlier_counterexample_assemble
    (hw : type_of% @AronowAudit.P017.arbitrary_outlier_sequence) :
    type_of% @AronowAudit.P017.slow_outlier_counterexample := by
  have hp : ∀ n : ℕ, 1 ≤ n → 0 < slowP n ∧ slowP n ≤ 1 :=
    fun n _ => slow_probability_positive_limit.1 n
  have hlim := slow_probability_positive_limit.2
  rcases hw slowP hp hlim with
    ⟨hm, hi, hmean, hsupp, hrad, hroot, hfinite, hlower, hrest⟩
  have hfailure (n : ℕ) (hn : 1 ≤ n) :
      pr (iidSamples slowPopulation)
        {s | rareEstimator slowP n s ≠ clipReal 0 1 (rareEstimator slowP n s)} = slowP n := by
    rcases hfinite n hn with
      ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, htail⟩
    exact h₁₀
  refine ⟨hp, hlim, hroot, hm, hi, hmean, hsupp, hrad, hfailure,
    slow_probability_numbers.1, slow_probability_numbers.2.1,
    slow_probability_numbers.2.2, slow_outlier_counterexample_dyadic_growth,
    slow_outlier_counterexample_no_polynomial,
    slow_outlier_counterexample_not_small hlower, ?_⟩
  intro r hr hrlim
  obtain ⟨p, hp', hplim, hratio⟩ := slow_outlier_counterexample_slower_rate r hr hrlim
  rcases hw p hp' hplim with
    ⟨hm', hi', hmean', hsupp', hrad', hroot', hfinite', htail⟩
  refine ⟨p, hp', hplim, hroot', ?_, hratio⟩
  intro n hn
  rcases hfinite' n hn with
    ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, htail⟩
  exact h₁₀

/-
FINAL ASSEMBLY TEMPLATE — blocked on a genuine companion proof.
This block is deliberately a comment: no missing theorem is declared or assumed
in the live module. Import the module proving `arbitrary_outlier_sequence_proof`,
then uncomment these declarations. That name is the expected new Wave1 proof,
not the held `AronowAudit.P017.arbitrary_outlier_sequence`.

theorem slow_outlier_counterexample_proof :
    (∀ n : ℕ, 1 ≤ n → 0 < slowP n ∧ slowP n ≤ 1) ∧ Tendsto slowP atTop (𝓝 0) ∧
    RootNNormal (iidSamples slowPopulation) (rareEstimator slowP) 0 ∧
    Measurable slowEffect ∧ Integrable slowEffect slowPopulation ∧
    populationMean slowPopulation slowEffect = 0 ∧
    effectSupport slowPopulation slowEffect = Icc (-1) 1 ∧ effectRadius slowPopulation slowEffect = 1 ∧
    (∀ n : ℕ, 1 ≤ n → pr (iidSamples slowPopulation)
      {s | rareEstimator slowP n s ≠ clipReal 0 1 (rareEstimator slowP n s)} = slowP n) ∧
    slowP 1000 = 1 / 10 ∧ slowP (10 ^ 12) = 1 / 40 ∧
    (∀ k : ℕ, slowP (2 ^ k) = 1 / ((k + 1 : ℕ) : ℝ)) ∧
    (∀ α : ℝ, 0 < α → Tendsto
      (fun k : ℕ => ((2 ^ k : ℕ) : ℝ) ^ α * slowP (2 ^ k)) atTop atTop) ∧
    (∀ α : ℝ, 0 < α → ¬ ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, slowP n ≤ C / (n : ℝ) ^ α) ∧
    ¬ SmallRemainderMS (iidSamples slowPopulation) (rareRemainder slowP) ∧
    (∀ r : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → 0 < r n) → Tendsto r atTop (𝓝 0) →
      ∃ p : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → 0 < p n ∧ p n ≤ 1) ∧ Tendsto p atTop (𝓝 0) ∧
        RootNNormal (iidSamples slowPopulation) (rareEstimator p) 0 ∧
        (∀ n : ℕ, 1 ≤ n → pr (iidSamples slowPopulation)
          {s | rareEstimator p n s ≠ clipReal 0 1 (rareEstimator p n s)} = p n) ∧
        Tendsto (fun n => p n / r n) atTop atTop) := by
  exact slow_outlier_counterexample_assemble arbitrary_outlier_sequence_proof

example : type_of% @AronowAudit.P017.slow_outlier_counterexample :=
  slow_outlier_counterexample_proof
-/

end
end AronowAudit.P017.Wave1
