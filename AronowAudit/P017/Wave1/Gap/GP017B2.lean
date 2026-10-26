import AronowAudit.P017.P017_Audit
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Independence.InfinitePi



namespace AronowAudit.P017.Wave1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

/-- Standard normal absolute tail, with strict exceedance and a closed CDF. -/
private theorem t13_standard_absolute_tail (a : ℝ) (ha : 0 < a) :
    pr (gaussianReal 0 1) {z : ℝ | a < |z|} = 2 * normalCDF (-a) := by
  let γ := gaussianReal 0 1
  letI : NullSingletonClass γ := nullSingletonClass_gaussianReal (by norm_num)
  have hset : {z : ℝ | a < |z|} = Iio (-a) ∪ Ioi a := by
    ext z
    simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioi, lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hdis : Disjoint (Iio (-a)) (Ioi a) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    simp only [mem_Iio, mem_Ioi] at hz hz'
    linarith
  have hleft : γ (Iio (-a)) = γ (Iic (-a)) :=
    measure_congr (Iio_ae_eq_Iic' (measure_singleton (-a)))
  have hright : γ (Ioi a) = γ (Iio (-a)) := by
    have hmap : γ.map (fun z : ℝ => -z) = γ := by
      simpa [γ] using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
    calc
      γ (Ioi a) = γ.map (fun z : ℝ => -z) (Iio (-a)) := by
        rw [Measure.map_apply measurable_neg measurableSet_Iio]
        congr 1
        ext z
        simp only [mem_preimage, mem_Iio, mem_Ioi]
        constructor <;> intro h <;> linarith
      _ = γ (Iio (-a)) := by rw [hmap]
  unfold pr normalCDF
  rw [hset, measureReal_def, measure_union hdis measurableSet_Ioi,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hright, hleft]
  change (γ (Iic (-a))).toReal + (γ (Iic (-a))).toReal =
    2 * (γ (Iic (-a))).toReal
  ring

/-- Pull the tail back through an explicit positive affine Gaussian map. -/
private theorem t13_affine_absolute_tail {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (X : Ξ → ℝ) (hX : Measurable X)
    (μ s a : ℝ) (hs : 0 < s) (ha : 0 < a)
    (hlaw : P.map X = gaussianReal μ ⟨s ^ 2, sq_nonneg s⟩) :
    pr P {ω | a < |X ω - μ|} = 2 * normalCDF (-a / s) := by
  have hmap : (gaussianReal 0 1).map (fun z : ℝ => μ + s * z) =
      gaussianReal μ ⟨s ^ 2, sq_nonneg s⟩ := by
    have heq : (fun z : ℝ => μ + s * z) = (fun z : ℝ => μ + z) ∘ (fun z => s * z) := rfl
    rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop),
      gaussianReal_map_const_mul, gaussianReal_map_const_add]
    simp only [mul_zero, zero_add, mul_one]
    rfl
  have hpull : pr P {ω | a < |X ω - μ|} =
      pr (gaussianReal 0 1) {z : ℝ | a / s < |z|} := by
    unfold pr
    change (P (X ⁻¹' {y : ℝ | a < |y - μ|})).toReal =
      ((gaussianReal 0 1) {z : ℝ | a / s < |z|}).toReal
    rw [← Measure.map_apply hX (by measurability), hlaw, ← hmap,
      Measure.map_apply (by fun_prop) (by measurability)]
    congr 2
    ext z
    simp only [mem_preimage, mem_setOf_eq, add_sub_cancel_left, abs_mul,
      abs_of_pos hs, div_lt_iff₀ hs]
    constructor <;> intro h <;> nlinarith
  rw [hpull, t13_standard_absolute_tail (a / s) (div_pos ha hs)]
  congr 2
  ring

theorem normal_plus_remainder_failure_bound_proof {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (tilde u : Ξ → ℝ)
    (htm : Measurable tilde) (hum : Measurable u) (μ c σ : ℝ)
    (hc : 0 < c) (hσ : 0 < σ) (n : ℕ) (hn : 1 ≤ n)
    (hlaw : P.map tilde = gaussianReal μ ⟨σ ^ 2 / (n : ℝ), by positivity⟩) :
    pr P {ω | |tilde ω + u ω - μ| > c} ≤
      2 * normalCDF (-c * sqrtN n / (2 * σ)) + pr P {ω | |u ω| > c / 2} := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < sqrtN n := Real.sqrt_pos.mpr hnR
  have hs2 : sqrtN n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hv : (σ / sqrtN n) ^ 2 = σ ^ 2 / (n : ℝ) := by
    rw [div_pow, hs2]
  have hlaw' : P.map tilde =
      gaussianReal μ ⟨(σ / sqrtN n) ^ 2, sq_nonneg _⟩ := by
    have hvNN : (⟨(σ / sqrtN n) ^ 2, sq_nonneg _⟩ : ℝ≥0) =
        ⟨σ ^ 2 / (n : ℝ), by positivity⟩ := NNReal.eq hv
    rw [hvNN]
    exact hlaw
  have htail := t13_affine_absolute_tail P tilde htm μ (σ / sqrtN n) (c / 2)
    (div_pos hσ hs) (half_pos hc) hlaw'
  have harg : -(c / 2) / (σ / sqrtN n) = -c * sqrtN n / (2 * σ) := by
    field_simp [hσ.ne', hs.ne']
    <;> ring
  rw [harg] at htail
  simpa only [htail] using sum_failure_union_bound P tilde u μ c

/-- Polynomial Gaussian densities are integrable. This also covers odd powers. -/
private theorem t15_density_pow_integrable (v : ℝ≥0) (hv : 0 < v) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * gaussianPDFReal 0 v x) := by
  have hvR : 0 < (v : ℝ) := hv
  have hbase := integrable_rpow_mul_exp_neg_mul_sq
    (b := 1 / (2 * (v : ℝ))) (by positivity) (s := (k : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have heq : (fun x : ℝ => x ^ k * gaussianPDFReal 0 v x) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        (x ^ (k : ℝ) * Real.exp (-(1 / (2 * (v : ℝ))) * x ^ 2))) := by
    funext x
    rw [Real.rpow_natCast]
    simp only [gaussianPDFReal, sub_zero]
    have hexp : -(x ^ 2) / (2 * (v : ℝ)) = -(1 / (2 * (v : ℝ))) * x ^ 2 := by ring
    rw [hexp]
    ring
  rw [heq]
  exact hbase.const_mul _

/-- Differentiate the centered Gaussian density, retaining the variance factor. -/
private theorem t15_density_deriv (v : ℝ≥0) (hv : 0 < v) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 v) (-x / (v : ℝ) * gaussianPDFReal 0 v x) x := by
  have hvR : (v : ℝ) ≠ 0 := ne_of_gt hv
  have hh := (((hasDerivAt_id' x).pow 2).neg.div_const (2 * (v : ℝ))).exp
  have hh' := hh.const_mul (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  convert hh' using 1
  · funext y
    simp only [gaussianPDFReal, sub_zero, Pi.pow_apply, Pi.neg_apply]
  · simp only [gaussianPDFReal, sub_zero, Pi.pow_apply, Pi.neg_apply,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    field_simp [hvR]
    <;> ring

/-- Integration by parts with an integrable product avoids boundary limits. -/
private theorem t15_gaussian_moment_recurrence (v : ℝ≥0) (hv : 0 < v) (k : ℕ) :
    (∫ x : ℝ, x ^ (k + 2) ∂gaussianReal 0 v) =
      ((k + 1 : ℕ) : ℝ) * (v : ℝ) * (∫ x : ℝ, x ^ k ∂gaussianReal 0 v) := by
  have hvR : (v : ℝ) ≠ 0 := ne_of_gt hv
  have hleft : Integrable (fun x : ℝ =>
      x ^ (k + 1) * (-x / (v : ℝ) * gaussianPDFReal 0 v x)) := by
    convert (t15_density_pow_integrable v hv (k + 2)).const_mul (-(v : ℝ)⁻¹) using 1
    funext x
    simp only [pow_add, pow_one, pow_two]
    ring
  have hright : Integrable (fun x : ℝ =>
      ((k + 1 : ℕ) : ℝ) * x ^ k * gaussianPDFReal 0 v x) := by
    simpa only [mul_assoc] using (t15_density_pow_integrable v hv k).const_mul ((k + 1 : ℕ) : ℝ)
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => x ^ (k + 1)) (u' := fun x => ((k + 1 : ℕ) : ℝ) * x ^ k)
    (v := gaussianPDFReal 0 v) (v' := fun x => -x / (v : ℝ) * gaussianPDFReal 0 v x)
    (fun x _ => by
      convert (hasDerivAt_id' x).pow (k + 1) using 1 <;> simp)
    (fun x _ => t15_density_deriv v hv x) hleft hright
    (t15_density_pow_integrable v hv (k + 1))
  have hl : (fun x : ℝ => x ^ (k + 1) * (-x / (v : ℝ) * gaussianPDFReal 0 v x)) =
      (fun x : ℝ => (-(v : ℝ)⁻¹) * (x ^ (k + 2) * gaussianPDFReal 0 v x)) := by
    funext x
    simp only [pow_add, pow_one, pow_two]
    ring
  rw [hl, integral_const_mul] at hparts
  have hr : (fun x : ℝ => ((k + 1 : ℕ) : ℝ) * x ^ k * gaussianPDFReal 0 v x) =
      (fun x : ℝ => ((k + 1 : ℕ) : ℝ) * (x ^ k * gaussianPDFReal 0 v x)) := by
    funext x; ring
  rw [hr, integral_const_mul] at hparts
  rw [integral_gaussianReal_eq_integral_smul hv.ne',
    integral_gaussianReal_eq_integral_smul hv.ne']
  simp only [smul_eq_mul] at *
  simp_rw [mul_comm (gaussianPDFReal 0 v _)]
  have hh := congrArg (fun z : ℝ => -(v : ℝ) * z) hparts
  field_simp [hvR] at hh
  nlinarith [hh]

private theorem t15_gaussian_even_moments (v : ℝ≥0) (hv : 0 < v) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) ∧
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 ∧
    (∫ x : ℝ, x ^ 6 ∂gaussianReal 0 v) = 15 * (v : ℝ) ^ 3 := by
  have h2 := t15_gaussian_moment_recurrence v hv 0
  have h4 := t15_gaussian_moment_recurrence v hv 2
  have h6 := t15_gaussian_moment_recurrence v hv 4
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, pow_zero, integral_const,
    probReal_univ, smul_eq_mul, one_mul, mul_one] at h2 h4 h6
  refine ⟨h2, ?_, ?_⟩
  · rw [h2] at h4
    nlinarith [h4]
  · rw [h2] at h4
    rw [h4] at h6
    nlinarith [h6]

/-- A law transports both the finite moment and its exact value. -/
private theorem t15_moment_transport {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) (X : Ξ → ℝ) (hX : Measurable X) (v : ℝ≥0)
    (hlaw : P.map X = gaussianReal 0 v) (k : ℕ) :
    Integrable (fun ω => X ω ^ k) P ∧
    (∫ ω, X ω ^ k ∂P) = (∫ x : ℝ, x ^ k ∂gaussianReal 0 v) := by
  have hi : Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 v) := by
    have h := (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := v) (k : ℝ≥0)).integrable_norm_pow'
    apply h.mono' (by fun_prop)
    exact ae_of_all _ (fun x => by simp [Real.norm_eq_abs, abs_pow])
  constructor
  · have hi' : Integrable (fun x : ℝ => x ^ k) (P.map X) := hlaw.symm ▸ hi
    exact hi'.comp_measurable hX
  · rw [← hlaw, integral_map hX.aemeasurable (by fun_prop)]

/-- A local finite fourth-moment bound for the actual clipped error. -/
private theorem t15_actual_mse_bound {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat Z ε : ℕ → Ξ → ℝ)
    (μ c : ℝ) (v : ℝ≥0) (hc : 0 < c) (hv : 0 < v)
    (hhm : ∀ n, Measurable (hat n)) (hr : NormalRemainder P hat Z ε μ v)
    (n : ℕ) (hn : 1 ≤ n) :
    (∫ ω, residual μ c (hat n ω) ^ 2 ∂P) ≤
      6 * (v : ℝ) ^ 2 / (c ^ 2 * (n : ℝ) ^ 2) +
        2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < sqrtN n := Real.sqrt_pos.mpr hnR
  have hs2 : sqrtN n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hZ := hr.1 n hn
  have he := hr.2.1 n hn
  have h4 := t15_moment_transport P (Z n) hZ.1 v hZ.2 4
  have h4val : (∫ ω, Z n ω ^ 4 ∂P) = 3 * (v : ℝ) ^ 2 :=
    h4.2.trans (t15_gaussian_even_moments v hv).2.1
  let B : Ξ → ℝ := fun ω =>
    2 * (Z n ω ^ 4 / (sqrtN n ^ 4 * c ^ 2)) + 2 * (ε n ω ^ 2 / (n : ℝ))
  have hB : Integrable B P :=
    ((h4.1.div_const _).const_mul 2).add ((he.2.div_const _).const_mul 2)
  have hpoint : ∀ᵐ ω ∂P, residual μ c (hat n ω) ^ 2 ≤ B ω := by
    filter_upwards [hr.2.2 n hn] with ω hω
    have hdecomp : hat n ω = (μ + Z n ω / sqrtN n) + ε n ω / sqrtN n := by
      have ht : hat n ω - μ = (Z n ω + ε n ω) / sqrtN n :=
        (eq_div_iff hs.ne').mpr (by nlinarith [hω])
      calc
        hat n ω = μ + (hat n ω - μ) := by ring
        _ = (μ + Z n ω / sqrtN n) + ε n ω / sqrtN n := by rw [ht]; ring
    have hb := (perturbation_square_bounds μ c (μ + Z n ω / sqrtN n)
      (ε n ω / sqrtN n) hc.le).1
    have ht := (residual_tail_fourth_bound μ c (μ + Z n ω / sqrtN n) hc)
    rw [hdecomp]
    have hq : (μ + Z n ω / sqrtN n - μ) ^ 4 / c ^ 2 =
        Z n ω ^ 4 / (sqrtN n ^ 4 * c ^ 2) := by
      simp only [add_sub_cancel_left, div_pow, div_div]
    have heq : (ε n ω / sqrtN n) ^ 2 = ε n ω ^ 2 / (n : ℝ) := by
      rw [div_pow, hs2]
    dsimp only [B]
    rw [heq] at hb
    rw [hq] at ht
    linarith [ht.1.trans ht.2]
  have hhatm := hhm n
  have hI : Integrable (fun ω => residual μ c (hat n ω) ^ 2) P := by
    apply hB.mono' (by unfold residual clipReal; fun_prop)
    filter_upwards [hpoint] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (residual μ c (hat n ω)))] using hω
  calc
    (∫ ω, residual μ c (hat n ω) ^ 2 ∂P) ≤ ∫ ω, B ω ∂P :=
      integral_mono_ae hI hB hpoint
    _ = 6 * (v : ℝ) ^ 2 / (c ^ 2 * (n : ℝ) ^ 2) +
        2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ) := by
      rw [integral_add ((h4.1.div_const _).const_mul 2)
        ((he.2.div_const _).const_mul 2)]
      simp only [integral_const_mul, integral_div, h4val]
      have hs4 : sqrtN n ^ 4 = (n : ℝ) ^ 2 := by
        calc
          sqrtN n ^ 4 = (sqrtN n ^ 2) ^ 2 := by ring
          _ = (n : ℝ) ^ 2 := by rw [hs2]
      rw [hs4]
      ring

theorem proposition4_proof {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hc : 0 < effectRadius G τ)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat Z ε : ℕ → Ξ → ℝ)
    (hhm : ∀ n, Measurable (hat n)) (v : ℝ≥0) (hv : 0 < v)
    (hr : NormalRemainder P hat Z ε (populationMean G τ) v) (he : SmallRemainderMS P ε) :
    SmallMSE P (fun n ω => hat n ω - clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω)) := by
  by_cases htop : effectRadius G τ = ⊤
  · simpa only [htop] using (infinite_radius_facts P hat (populationMean G τ)).2
  · have hcR : 0 < (effectRadius G τ).toReal := ENNReal.toReal_pos hc.ne' htop
    let c := (effectRadius G τ).toReal
    let e : ℕ → ℝ := fun n => ∫ ω, ε n ω ^ 2 ∂P
    have he0 : Tendsto e atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun ω => sq_nonneg _)))
        ?_ he
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hs : 1 ≤ sqrtN n := by
        simpa only [sqrtN, Real.sqrt_one] using Real.sqrt_le_sqrt hnR
      have hnon : 0 ≤ e n := integral_nonneg (fun ω => sq_nonneg _)
      change e n ≤ sqrtN n * e n
      nlinarith
    have h_inv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hupper : Tendsto (fun n : ℕ =>
        6 * (v : ℝ) ^ 2 / (c ^ 2) * (n : ℝ)⁻¹ + 2 * e n) atTop (𝓝 0) := by
      simpa using (h_inv.const_mul (6 * (v : ℝ) ^ 2 / c ^ 2)).add (he0.const_mul 2)
    have hlimit : Tendsto (fun n : ℕ => (n : ℝ) *
        (∫ ω, residual (populationMean G τ) c (hat n ω) ^ 2 ∂P)) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun n => mul_nonneg (Nat.cast_nonneg n)
        (integral_nonneg (fun ω => sq_nonneg _)))) ?_ hupper
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hb := mul_le_mul_of_nonneg_left
        (t15_actual_mse_bound P hat Z ε (populationMean G τ) c v hcR hv hhm hr n hn)
        hnR.le
      have halg : (n : ℝ) * (6 * (v : ℝ) ^ 2 / (c ^ 2 * (n : ℝ) ^ 2) +
          2 * e n / (n : ℝ)) =
          6 * (v : ℝ) ^ 2 / c ^ 2 * (n : ℝ)⁻¹ + 2 * e n := by
        field_simp [hnR.ne', hcR.ne']
        <;> ring
      dsimp only [e] at halg
      rw [halg] at hb
      exact hb
    simpa only [SmallMSE, clipTarget, htop, ↓reduceIte, residual, c] using hlimit

/-- Representation is exactly strict support interior or an atomic endpoint. -/
private theorem t3_representation_iff {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (t : ℝ) :
    Representable G τ t ↔ InteriorOrEndpointAtom G τ t := by
  have hw := weighted_support_consequences G τ hτm hτi
  constructor
  · intro ht
    have hb := representable_support_bounds G τ hτm hτi t ht
    by_cases hL : (t : EReal) = supportInf (effectSupport G τ)
    · exact Or.inr ⟨Or.inl hL, (hw.2.1 t (Or.inl hL)).mp ht⟩
    by_cases hU : (t : EReal) = supportSup (effectSupport G τ)
    · exact Or.inr ⟨Or.inr hU, (hw.2.1 t (Or.inr hU)).mp ht⟩
    · exact Or.inl ⟨lt_of_le_of_ne hb.1 (Ne.symm hL), lt_of_le_of_ne hb.2 hU⟩
  · rintro (⟨hL, hU⟩ | ⟨hend, hatom⟩)
    · exact hw.1 t hL hU
    · exact (hw.2.1 t hend).mpr hatom

/-- The finite clipping interval is contained in the closed support hull. -/
private theorem t3_finite_radius_geometry {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ : Ω → ℝ) (hc : 0 < effectRadius G τ)
    (htop : effectRadius G τ ≠ ⊤) :
    supportInf (effectSupport G τ) ≤
      ((populationMean G τ - (effectRadius G τ).toReal : ℝ) : EReal) ∧
    ((populationMean G τ + (effectRadius G τ).toReal : ℝ) : EReal) ≤
      supportSup (effectSupport G τ) := by
  let μ := populationMean G τ
  let L := supportInf (effectSupport G τ)
  let U := supportSup (effectSupport G τ)
  let q := min (U - (μ : EReal)) ((μ : EReal) - L)
  let r := (effectRadius G τ).toReal
  have hqpos : 0 < q := EReal.toENNReal_pos_iff.mp hc
  have hrq : (r : EReal) = q := by
    calc
      (r : EReal) = ((effectRadius G τ : ℝ≥0∞) : EReal) := EReal.coe_ennreal_toReal htop
      _ = q := EReal.coe_toENNReal hqpos.le
  have hdu : (r : EReal) ≤ U - (μ : EReal) := by rw [hrq]; exact min_le_left _ _
  have hdl : (r : EReal) ≤ (μ : EReal) - L := by rw [hrq]; exact min_le_right _ _
  constructor
  · have h := EReal.add_le_of_le_sub hdl
    rw [EReal.coe_sub, EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot r))
      (.inl (EReal.coe_ne_top r))]
    simpa only [add_comm] using h
  · have h := EReal.add_le_of_le_sub hdu
    simpa only [EReal.coe_add, add_comm] using h

/-- At infinite radius every real number is strictly interior to the support hull. -/
private theorem t3_infinite_radius_interior {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ : Ω → ℝ) (htop : effectRadius G τ = ⊤) (x : ℝ) :
    supportInf (effectSupport G τ) < (x : EReal) ∧
      (x : EReal) < supportSup (effectSupport G τ) := by
  let d := |x - populationMean G τ| + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hsmall : ENNReal.ofReal d < effectRadius G τ := by simp [htop]
  have hi := interior_radius_support G τ d hd hsmall x
  have heq : clipReal (populationMean G τ) d x = x :=
    (clipReal_eq_self_iff _ _ _ hd.le).mpr (by dsimp [d]; linarith [abs_nonneg (x - populationMean G τ)])
  simpa only [heq] using hi

/-- Strictly inside the specified radius, clipping fixes a representable value. -/
private theorem t3_strict_inside_representation {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hc : 0 < effectRadius G τ)
    (x : ℝ) (hx : ENNReal.ofReal |x - populationMean G τ| < effectRadius G τ) :
    Representable G τ (clipTarget (populationMean G τ) (effectRadius G τ) x) := by
  by_cases htop : effectRadius G τ = ⊤
  · have hb := t3_infinite_radius_interior G τ htop x
    simpa only [clipTarget, htop, ↓reduceIte] using
      (weighted_support_consequences G τ hτm hτi).1 x hb.1 hb.2
  · have hr := ENNReal.toReal_pos hc.ne' htop
    have hxr : |x - populationMean G τ| < (effectRadius G τ).toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) htop).mp hx
    have hb := t3_finite_radius_geometry G τ hc htop
    have hi : supportInf (effectSupport G τ) < (x : EReal) ∧
        (x : EReal) < supportSup (effectSupport G τ) := by
      rcases abs_lt.mp hxr with ⟨hl, hu⟩
      exact ⟨hb.1.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith)),
        (EReal.coe_lt_coe_iff.mpr (by linarith)).trans_le hb.2⟩
    have heq := (clipReal_eq_self_iff (populationMean G τ)
      (effectRadius G τ).toReal x hr.le).mpr hxr.le
    simpa only [clipTarget, htop, ↓reduceIte, heq] using
      (weighted_support_consequences G τ hτm hτi).1 x hi.1 hi.2

/-- Consistency controls the complement of a strict inside event at half radius. -/
private theorem t3_strict_inside_limit {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
    (hhm : ∀ n, Measurable (hat n)) (μ : ℝ) (c : ℝ≥0∞) (hc : 0 < c)
    (hh : Consistent P hat μ) :
    Tendsto (fun n => pr P {ω | ENNReal.ofReal |hat n ω - μ| < c}) atTop (𝓝 1) := by
  by_cases htop : c = ⊤
  · simp only [htop, ENNReal.ofReal_lt_top, setOf_true, pr, probReal_univ]
    exact tendsto_const_nhds
  · have hr : 0 < c.toReal := ENNReal.toReal_pos hc.ne' htop
    have hcomp : Tendsto (fun n =>
        pr P {ω | ¬ ENNReal.ofReal |hat n ω - μ| < c}) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => measureReal_nonneg) ?_ (hh (c.toReal / 2) (half_pos hr))
      intro n
      apply measureReal_mono ?_ (measure_ne_top P _)
      intro ω hω
      have hge : c.toReal ≤ |hat n ω - μ| := by
        exact le_of_not_gt (fun h => hω
          ((ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) htop).mpr h))
      change c.toReal / 2 < |hat n ω - μ|
      linarith
    have heq (n : ℕ) : pr P {ω | ENNReal.ofReal |hat n ω - μ| < c} =
        1 - pr P {ω | ¬ ENNReal.ofReal |hat n ω - μ| < c} := by
      have hm : MeasurableSet {ω | ENNReal.ofReal |hat n ω - μ| < c} := by
        have hevent : {ω | ENNReal.ofReal |hat n ω - μ| < c} =
            {ω | |hat n ω - μ| < c.toReal} := by
          ext ω
          exact ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) htop
        rw [hevent]
        exact measurableSet_lt (by simpa only [Real.norm_eq_abs] using ((hhm n).sub_const μ).norm) measurable_const
      have h := measureReal_add_measureReal_compl (μ := P) hm
      change P.real {ω | ENNReal.ofReal |hat n ω - μ| < c} =
        1 - P.real {ω | ¬ ENNReal.ofReal |hat n ω - μ| < c}
      simpa only [probReal_univ, Set.compl_setOf] using (eq_sub_iff_add_eq.mpr h)
    simp_rw [heq]
    simpa using tendsto_const_nhds.sub hcomp

theorem corrected_proposition1_proof {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G)
    (hc : 0 < effectRadius G τ) (P : Measure Ξ) [IsProbabilityMeasure P]
    (hat : ℕ → Ξ → ℝ) (hhm : ∀ n, Measurable (hat n)) :
    (∀ x : ℝ,
      supportInf (effectSupport G τ) ≤ (clipTarget (populationMean G τ) (effectRadius G τ) x : EReal) ∧
      (clipTarget (populationMean G τ) (effectRadius G τ) x : EReal) ≤ supportSup (effectSupport G τ) ∧
      (Representable G τ (clipTarget (populationMean G τ) (effectRadius G τ) x) ↔
        InteriorOrEndpointAtom G τ (clipTarget (populationMean G τ) (effectRadius G τ) x))) ∧
    (∀ x : ℝ, ENNReal.ofReal |x - populationMean G τ| < effectRadius G τ →
      Representable G τ (clipTarget (populationMean G τ) (effectRadius G τ) x)) ∧
    ((effectRadius G τ = ⊤ ∨
      (∀ t : ℝ, (t = populationMean G τ - (effectRadius G τ).toReal ∨
        t = populationMean G τ + (effectRadius G τ).toReal) →
        ((t : EReal) = supportInf (effectSupport G τ) ∨
          (t : EReal) = supportSup (effectSupport G τ)) → 0 < pr G {ω | τ ω = t})) →
      ∀ x, Representable G τ (clipTarget (populationMean G τ) (effectRadius G τ) x)) ∧
    (RootNNormal P hat (populationMean G τ) →
      Tendsto (fun n => pr P {ω | ENNReal.ofReal |hat n ω - populationMean G τ| < effectRadius G τ})
        atTop (𝓝 1) ∧
      Tendsto (fun n => pr P {ω | Representable G τ
        (clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω))}) atTop (𝓝 1)) := by
  have hstrict := t3_strict_inside_representation G τ hτm hτi hc
  have hbounds (x : ℝ) :
      supportInf (effectSupport G τ) ≤
        (clipTarget (populationMean G τ) (effectRadius G τ) x : EReal) ∧
      (clipTarget (populationMean G τ) (effectRadius G τ) x : EReal) ≤
        supportSup (effectSupport G τ) := by
    by_cases htop : effectRadius G τ = ⊤
    · have hi := t3_infinite_radius_interior G τ htop x
      simpa only [clipTarget, htop, ↓reduceIte] using And.intro hi.1.le hi.2.le
    · have hb := t3_finite_radius_geometry G τ hc htop
      have hb' := clipReal_bounds (populationMean G τ) (effectRadius G τ).toReal x
        ENNReal.toReal_nonneg
      simpa only [clipTarget, htop, ↓reduceIte] using
        And.intro (hb.1.trans (EReal.coe_le_coe_iff.mpr hb'.1))
          ((EReal.coe_le_coe_iff.mpr hb'.2).trans hb.2)
  refine ⟨?_, hstrict, ?_, ?_⟩
  · intro x
    exact ⟨(hbounds x).1, (hbounds x).2, t3_representation_iff G τ hτm hτi _⟩
  · intro hcond x
    rcases hcond with htop | hatoms
    · have hi := t3_infinite_radius_interior G τ htop x
      simpa only [clipTarget, htop, ↓reduceIte] using
        (weighted_support_consequences G τ hτm hτi).1 x hi.1 hi.2
    · by_cases htop : effectRadius G τ = ⊤
      · have hi := t3_infinite_radius_interior G τ htop x
        simpa only [clipTarget, htop, ↓reduceIte] using
          (weighted_support_consequences G τ hτm hτi).1 x hi.1 hi.2
      let t := clipTarget (populationMean G τ) (effectRadius G τ) x
      have hb := hbounds x
      by_cases hL : (t : EReal) = supportInf (effectSupport G τ)
      · have hgeom := (t3_finite_radius_geometry G τ hc htop).1
        have hcclip := (clipReal_bounds (populationMean G τ) (effectRadius G τ).toReal x
          ENNReal.toReal_nonneg).1
        have he : t = populationMean G τ - (effectRadius G τ).toReal := by
          have hle : (t : EReal) ≤
              ((populationMean G τ - (effectRadius G τ).toReal : ℝ) : EReal) := by
            rw [hL]; exact hgeom
          exact le_antisymm (EReal.coe_le_coe_iff.mp hle)
            (by simpa only [t, clipTarget, htop, ↓reduceIte] using hcclip)
        exact (t3_representation_iff G τ hτm hτi t).mpr
          (Or.inr ⟨Or.inl hL, hatoms t (Or.inl he) (Or.inl hL)⟩)
      by_cases hU : (t : EReal) = supportSup (effectSupport G τ)
      · have hgeom := (t3_finite_radius_geometry G τ hc htop).2
        have hcclip := (clipReal_bounds (populationMean G τ) (effectRadius G τ).toReal x
          ENNReal.toReal_nonneg).2
        have he : t = populationMean G τ + (effectRadius G τ).toReal := by
          have hle : ((populationMean G τ + (effectRadius G τ).toReal : ℝ) : EReal) ≤
              (t : EReal) := by rw [hU]; exact hgeom
          exact le_antisymm
            (by simpa only [t, clipTarget, htop, ↓reduceIte] using hcclip)
            (EReal.coe_le_coe_iff.mp hle)
        exact (t3_representation_iff G τ hτm hτi t).mpr
          (Or.inr ⟨Or.inr hU, hatoms t (Or.inr he) (Or.inr hU)⟩)
      · exact (weighted_support_consequences G τ hτm hτi).1 t
          (lt_of_le_of_ne hb.1 (Ne.symm hL)) (lt_of_le_of_ne hb.2 hU)
  · intro hroot
    have hcon := (root_normal_tight_and_consistent P hat (populationMean G τ) hroot).2
    have hlim := t3_strict_inside_limit P hat hhm (populationMean G τ) (effectRadius G τ) hc hcon
    refine ⟨hlim, ?_⟩
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds
    · intro n
      apply measureReal_mono ?_ (measure_ne_top P _)
      intro ω hω
      exact hstrict (hat n ω) hω
    · intro n
      have hu := measureReal_mono (μ := P)
        (Set.subset_univ {ω | Representable G τ
          (clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω))})
        (measure_ne_top P _)
      simpa only [pr, probReal_univ] using hu

/-- The effect coordinate has the actual fair two-point law. -/
private theorem t6_effect_law :
    normalPopulation.map normalEffect = fairPair (-1) 1 := by
  have heq : normalEffect = (Prod.snd : ℝ × ℝ → ℝ) := by
    funext ω
    simp [normalEffect, normalY1, normalY0]
  rw [heq, normalPopulation, Measure.map_snd_prod]
  simp

private theorem t6_effect_population :
    Measurable normalEffect ∧ Integrable normalEffect normalPopulation ∧
    populationMean normalPopulation normalEffect = 0 ∧
    effectSupport normalPopulation normalEffect = {-1, 1} ∧
    effectRadius normalPopulation normalEffect = 1 := by
  have hm : Measurable normalEffect := by
    have heq : normalEffect = (Prod.snd : ℝ × ℝ → ℝ) := by
      funext ω
      simp [normalEffect, normalY1, normalY0]
    rw [heq]
    exact measurable_snd
  have hiL : Integrable (fun x : ℝ => x) ((1 / 2 : ℝ≥0∞) • Measure.dirac (-1)) := by
    apply (integrable_smul_measure (by norm_num) (by norm_num)).mpr
    exact integrable_dirac (by simp)
  have hiU : Integrable (fun x : ℝ => x) ((1 / 2 : ℝ≥0∞) • Measure.dirac 1) := by
    apply (integrable_smul_measure (by norm_num) (by norm_num)).mpr
    exact integrable_dirac (by simp)
  have hi : Integrable (fun x : ℝ => x) (fairPair (-1) 1) := hiL.add_measure hiU
  have hmean : (∫ x : ℝ, x ∂fairPair (-1) 1) = 0 := by
    rw [fairPair, integral_add_measure hiL hiU]
    norm_num [integral_smul_measure]
  have hsupport : (fairPair (-1) 1).support = {-1, 1} := by
    ext x
    constructor
    · intro hx
      by_contra hnot
      have hopen : IsOpen ({-1, 1} : Set ℝ)ᶜ := by
        have hh : IsClosed (({-1} : Set ℝ) ∪ {1}) := isClosed_singleton.union isClosed_singleton
        exact hh.isOpen_compl
      have hnb : ({-1, 1} : Set ℝ)ᶜ ∈ 𝓝 x := hopen.mem_nhds hnot
      have hp := (Measure.mem_support_iff_forall x).mp hx _ hnb
      norm_num [fairPair, Measure.add_apply, Measure.smul_apply] at hp
    · intro hx
      apply (Measure.mem_support_iff_forall x).mpr
      intro U hU
      have hxU : x ∈ U := mem_of_mem_nhds hU
      rcases hx with hx | hx
      · have hx' : x = -1 := hx
        subst x
        have hdir : Measure.dirac (-1 : ℝ) U = 1 := Measure.dirac_apply_of_mem hxU
        rw [fairPair, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hdir]
        simp only [smul_eq_mul, mul_one]
        calc
          0 < (1 / 2 : ℝ≥0∞) := by norm_num
          _ ≤ _ := le_add_of_nonneg_right zero_le
      · have hx' : x = 1 := hx
        subst x
        have hdir : Measure.dirac (1 : ℝ) U = 1 := Measure.dirac_apply_of_mem hxU
        rw [fairPair, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hdir]
        simp only [smul_eq_mul, mul_one]
        calc
          0 < (1 / 2 : ℝ≥0∞) := by norm_num
          _ ≤ _ := le_add_of_nonneg_left zero_le
  have hsupport' : effectSupport normalPopulation normalEffect = {-1, 1} := by
    rw [effectSupport, t6_effect_law, hsupport]
  have hmean' : populationMean normalPopulation normalEffect = 0 := by
    unfold populationMean
    calc
      _ = ∫ x : ℝ, x ∂normalPopulation.map normalEffect :=
        (integral_map hm.aemeasurable measurable_id.aestronglyMeasurable).symm
      _ = 0 := by rw [t6_effect_law, hmean]
  refine ⟨hm, ?_, hmean', hsupport', ?_⟩
  · have hi' : Integrable (fun x : ℝ => x) (normalPopulation.map normalEffect) :=
      t6_effect_law.symm ▸ hi
    exact hi'.comp_measurable hm
  · have he : (-1 : EReal) ≤ 1 := by
      change ((-1 : ℝ) : EReal) ≤ ((1 : ℝ) : EReal)
      exact EReal.coe_le_coe_iff.mpr (by norm_num)
    simp only [effectRadius, hmean', hsupport', supportInf, supportSup,
      Set.image_insert_eq, Set.image_singleton, sSup_insert, sInf_insert,
      sSup_singleton, sInf_singleton, EReal.coe_neg, EReal.coe_one, EReal.coe_zero,
      sub_zero, zero_sub, max_eq_right he, min_eq_left he, neg_neg, min_self]
    change ((1 : ℝ) : EReal).toENNReal = 1
    exact (EReal.real_coe_toENNReal 1).trans ENNReal.ofReal_one

private theorem t6_normal_mean_measurable (n : ℕ) : Measurable (normalMean n) := by
  unfold normalMean sampleMean
  fun_prop

/-- Exact finite Gaussian law, including zero for the unnormalized empty sum. -/
private theorem t6_normal_mean_law (n : ℕ) (hn : 1 ≤ n) :
    (iidSamples normalPopulation).map (normalMean n) =
      gaussianReal 0 (1 / (n : ℝ≥0)) := by
  let P := iidSamples normalPopulation
  let X : ℕ → (ℕ → ℝ × ℝ) → ℝ := fun i s => (s i).1
  have hm (i : ℕ) : Measurable (X i) := measurable_fst.comp (measurable_pi_apply i)
  have hcoord (i : ℕ) : HasLaw (X i) (gaussianReal 0 1) P := by
    refine ⟨(hm i).aemeasurable, ?_⟩
    change (Measure.infinitePi (fun _ : ℕ => normalPopulation)).map
      ((Prod.fst : ℝ × ℝ → ℝ) ∘ (fun s => s i)) = _
    rw [← Measure.map_map measurable_fst (measurable_pi_apply i), Measure.infinitePi_map_eval]
    simp [normalPopulation, Measure.map_fst_prod]
  have hind : iIndepFun X P :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (Prod.fst : ℝ × ℝ → ℝ)) (fun _ => measurable_fst)
  have hsum (k : ℕ) : HasLaw (fun s => ∑ i ∈ Finset.range k, X i s)
      (gaussianReal 0 (k : ℝ≥0)) P := by
    induction k with
    | zero =>
      refine ⟨(by fun_prop), ?_⟩
      simp [gaussianReal_zero_var]
    | succ k ih =>
      have hInd : IndepFun (fun s => ∑ i ∈ Finset.range k, X i s) (X k) P := by
        simpa only [Finset.sum_fn] using hind.indepFun_sum_range_succ hm k
      have hAdd := gaussianReal_add_gaussianReal_of_indepFun hInd ih (hcoord k)
      refine ⟨(by fun_prop), ?_⟩
      simpa only [Finset.sum_range_succ, Pi.add_def, zero_add, Nat.cast_add, Nat.cast_one]
        using hAdd
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hscaled := gaussianReal_div_const (hsum n) (n : ℝ)
  change P.map (normalMean n) = _
  rw [show normalMean n = (fun s => (∑ i ∈ Finset.range n, X i s) / (n : ℝ)) from rfl]
  rw [hscaled.map_eq]
  simp only [zero_div]
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_natCast, NNReal.coe_one]
  field_simp [hnR.ne']
  <;> ring

private theorem t6_normal_remainder :
    NormalRemainder (iidSamples normalPopulation) shiftedNormalMean normalZ normalEpsilon 0 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hs2 : sqrtN n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    refine ⟨measurable_const.mul (t6_normal_mean_measurable n), ?_⟩
    have heq : normalZ n = (fun x : ℝ => sqrtN n * x) ∘ normalMean n := rfl
    rw [heq, ← Measure.map_map (by fun_prop) (t6_normal_mean_measurable n),
      t6_normal_mean_law n hn, gaussianReal_map_const_mul]
    simp only [mul_zero]
    congr 1
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, NNReal.coe_div, NNReal.coe_natCast]
    rw [hs2]
    field_simp [hnR.ne']
  · intro n hn
    exact ⟨measurable_const, integrable_const ((1 / sqrtN n)^2)⟩
  · intro n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hs : 0 < sqrtN n := Real.sqrt_pos.mpr hnR
    have hs2 : sqrtN n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    apply ae_of_all
    intro s
    dsimp only [shiftedNormalMean, normalZ, normalEpsilon]
    rw [sub_zero, mul_add]
    congr 1
    apply (eq_div_iff hs.ne').mpr
    calc
      (sqrtN n * (1 / (n : ℝ))) * sqrtN n = sqrtN n ^ 2 / (n : ℝ) := by ring
      _ = 1 := by rw [hs2]; exact div_self hnR.ne'

/-- Markov's second-moment estimate, with a strict tail and a closed central event. -/
private theorem t6_central_probability :
    pr (iidSamples normalPopulation) {s | |normalMean 25 s| ≤ 1 / 2} ≥ 21 / 25 := by
  let P := iidSamples normalPopulation
  let C := {s : ℕ → ℝ × ℝ | |normalMean 25 s| ≤ 1 / 2}
  have hmC : MeasurableSet C :=
    measurableSet_le (by simpa only [Real.norm_eq_abs] using (t6_normal_mean_measurable 25).norm) measurable_const
  have h2 := t15_moment_transport P (normalMean 25) (t6_normal_mean_measurable 25)
    (1 / 25) (by simpa using t6_normal_mean_law 25 (by norm_num)) 2
  have hval : (∫ s, normalMean 25 s ^ 2 ∂P) = 1 / 25 := by
    rw [h2.2, (t15_gaussian_even_moments (1 / 25) (by norm_num)).1]
    norm_num
  have hlow : (1 / 4 : ℝ) * pr P Cᶜ ≤ ∫ s, normalMean 25 s ^ 2 ∂P := by
    have hi : Integrable (Cᶜ.indicator (fun _ => (1 / 4 : ℝ))) P :=
      (integrable_const _).indicator hmC.compl
    have hp : ∀ s, Cᶜ.indicator (fun _ => (1 / 4 : ℝ)) s ≤ normalMean 25 s ^ 2 := by
      intro s
      by_cases hs : s ∈ C
      · rw [Set.indicator_of_notMem (show s ∉ Cᶜ from fun h => h hs)]
        positivity
      · rw [Set.indicator_of_mem hs]
        have habs : 1 / 2 < |normalMean 25 s| := lt_of_not_ge hs
        have hsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (abs_nonneg (normalMean 25 s))).mpr habs.le
        norm_num only [sq_abs, one_div, inv_pow, Nat.reducePow] at hsq ⊢
        exact hsq
    have hh := integral_mono hi h2.1 hp
    simpa only [integral_indicator_const _ hmC.compl, smul_eq_mul, pr, mul_comm] using hh
  have hcompl : pr P Cᶜ = 1 - pr P C := probReal_compl_eq_one_sub hmC
  rw [hcompl, hval] at hlow
  change 21 / 25 ≤ pr P C
  linarith

private theorem t6_difference_square_integrable :
    Integrable (fun s => shiftedDifference 25 s ^ 2) (iidSamples normalPopulation) := by
  have hm := t6_normal_mean_measurable 25
  let P := iidSamples normalPopulation
  have h2 := (t15_moment_transport P (normalMean 25) (t6_normal_mean_measurable 25)
    (1 / 25) (by simpa using t6_normal_mean_law 25 (by norm_num)) 2).1
  have hi : Integrable (fun s => 2 * normalMean 25 s ^ 2 + 2) P :=
    (h2.const_mul 2).add (integrable_const 2)
  apply hi.mono' (by unfold shiftedDifference clipReal shiftedNormalMean; fun_prop)
  apply ae_of_all
  intro s
  have hb := clipReal_bounds 0 1 (shiftedNormalMean 25 s) (by norm_num)
  have hb2 : clipReal 0 1 (shiftedNormalMean 25 s) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (clipReal 0 1 (shiftedNormalMean 25 s) + 1),
      mul_nonneg (by linarith : 0 ≤ 1 - clipReal 0 1 (shiftedNormalMean 25 s))
        (by linarith : 0 ≤ 1 + clipReal 0 1 (shiftedNormalMean 25 s))]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold shiftedDifference
  nlinarith [sq_nonneg (normalMean 25 s + clipReal 0 1 (shiftedNormalMean 25 s))]

private theorem t6_mse_lower :
    (∫ s, shiftedDifference 25 s ^ 2 ∂iidSamples normalPopulation) ≥ 21 / 15625 := by
  let P := iidSamples normalPopulation
  let C := {s : ℕ → ℝ × ℝ | |normalMean 25 s| ≤ 1 / 2}
  have hmC : MeasurableSet C :=
    measurableSet_le (by simpa only [Real.norm_eq_abs] using (t6_normal_mean_measurable 25).norm) measurable_const
  have hi : Integrable (C.indicator (fun _ => (1 / 625 : ℝ))) P :=
    (integrable_const _).indicator hmC
  have hp : ∀ s, C.indicator (fun _ => (1 / 625 : ℝ)) s ≤ shiftedDifference 25 s ^ 2 := by
    intro s
    by_cases hs : s ∈ C
    · rw [Set.indicator_of_mem hs]
      have hh := (shifted_25_central (normalMean 25 s) hs).2.2.2
      simpa only [shiftedDifference, shiftedNormalMean, Nat.cast_ofNat] using hh.ge
    · rw [Set.indicator_of_notMem hs]
      positivity
  have hh := integral_mono hi t6_difference_square_integrable hp
  have hcentral := t6_central_probability
  have hInt : (∫ s, C.indicator (fun _ => (1 / 625 : ℝ)) s ∂P) =
      pr P C * (1 / 625) := by
    simpa only [pr, smul_eq_mul] using integral_indicator_const (μ := P) (1 / 625 : ℝ) hmC
  rw [hInt] at hh
  change 21 / 25 ≤ pr P C at hcentral
  linarith

/-- Reflection identifies the two second-moment tails of the centered law. -/
private theorem t6_gaussian_two_sided_tail (v : ℝ≥0) :
    (∫ x : ℝ, if |x| > 1 then x ^ 2 else 0 ∂gaussianReal 0 v) =
      2 * (∫ x in Ioi (1 : ℝ), x ^ 2 ∂gaussianReal 0 v) := by
  let γ := gaussianReal 0 v
  have hi : Integrable (fun x : ℝ => x ^ 2) γ := by
    have h := (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := v) (2 : ℝ≥0)).integrable_norm_pow'
    simpa only [id_eq, Real.norm_eq_abs, sq_abs] using h
  have hip : Integrable (fun x : ℝ => if 1 < x then x ^ 2 else 0) γ := by
    convert hi.indicator (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ))) using 1
    funext x; rfl
  have hin : Integrable (fun x : ℝ => if x < -1 then x ^ 2 else 0) γ := by
    convert hi.indicator (measurableSet_Iio : MeasurableSet (Iio (-1 : ℝ))) using 1
    funext x; rfl
  have hneg : (∫ x : ℝ, if x < -1 then x ^ 2 else 0 ∂γ) =
      (∫ x : ℝ, if 1 < x then x ^ 2 else 0 ∂γ) := by
    have hmap : γ.map (fun x : ℝ => -x) = γ := by
      simpa only [γ, neg_zero] using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := v))
    calc
      (∫ x : ℝ, if x < -1 then x ^ 2 else 0 ∂γ) =
          (∫ x : ℝ, if 1 < -x then (-x) ^ 2 else 0 ∂γ) := by
            apply integral_congr_ae
            apply ae_of_all
            intro x
            have he : 1 < -x ↔ x < -1 := by constructor <;> intro h <;> linarith
            simp only [he, neg_sq]
      _ = (∫ x : ℝ, if 1 < x then x ^ 2 else 0 ∂γ.map (fun x : ℝ => -x)) := by
        rw [integral_map (by fun_prop)
          ((Measurable.ite measurableSet_Ioi (measurable_id'.pow_const 2) measurable_const).aestronglyMeasurable)]
      _ = _ := by rw [hmap]
  have hsplit (x : ℝ) : (if |x| > 1 then x ^ 2 else 0) =
      (if x < -1 then x ^ 2 else 0) + (if 1 < x then x ^ 2 else 0) := by
    by_cases hn : x < -1
    · have hp : ¬ 1 < x := by linarith
      have ha : 1 < |x| := by rw [abs_of_neg (by linarith)]; linarith
      simp only [hn, hp, ha, ↓reduceIte, add_zero]
    · by_cases hp : 1 < x
      · have ha : 1 < |x| := lt_of_lt_of_le hp (le_abs_self x)
        simp only [hn, hp, ha, ↓reduceIte, zero_add]
      · have ha : ¬ 1 < |x| := not_lt.mpr (abs_le.mpr (by constructor <;> linarith))
        simp only [hn, hp, ha, ↓reduceIte, zero_add]
  simp_rw [hsplit]
  rw [integral_add hin hip, hneg]
  have hpos : (∫ x : ℝ, if 1 < x then x ^ 2 else 0 ∂γ) =
      ∫ x in Ioi (1 : ℝ), x ^ 2 ∂γ := by
    simpa only [Set.indicator, mem_Ioi] using
      (integral_indicator (μ := γ) (f := fun x : ℝ => x ^ 2) measurableSet_Ioi)
  rw [hpos]
  ring

/-- The displayed paper integral is precisely the second tail moment at n=25. -/
private theorem t6_tail_density_identity :
    normalTail 25 1 1 =
      (∫ s, if |normalMean 25 s| > 1 then normalMean 25 s ^ 2 else 0
        ∂iidSamples normalPopulation) := by
  let γ := gaussianReal 0 (1 / 25)
  have hlaw : (iidSamples normalPopulation).map (normalMean 25) = γ := by
    simpa only [γ, Nat.cast_ofNat] using t6_normal_mean_law 25 (by norm_num)
  have hpull : (∫ s, if |normalMean 25 s| > 1 then normalMean 25 s ^ 2 else 0
      ∂iidSamples normalPopulation) =
      ∫ x : ℝ, if |x| > 1 then x ^ 2 else 0 ∂γ := by
    rw [← hlaw, integral_map (t6_normal_mean_measurable 25).aemeasurable
      ((Measurable.ite
        (measurableSet_lt measurable_const (by simpa only [Real.norm_eq_abs] using (measurable_id' : Measurable (fun x : ℝ => x)).norm))
        (measurable_id'.pow_const 2) measurable_const).aestronglyMeasurable)]
  rw [hpull, t6_gaussian_two_sided_tail]
  have hdensity (x : ℝ) : gaussianPDFReal 0 (1 / 25 : ℝ≥0) x =
      5 / Real.sqrt (2 * Real.pi) * Real.exp (-(x ^ 2 * 25) / 2) := by
    have hsqrt : Real.sqrt (2 * Real.pi * ((1 / 25 : ℝ≥0) : ℝ)) =
        Real.sqrt (2 * Real.pi) / 5 := by
      norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
      rw [show 2 * Real.pi * (1 / 25) = 2 * Real.pi / 25 by ring,
        Real.sqrt_div (by positivity)]
      norm_num
    unfold gaussianPDFReal
    rw [hsqrt]
    simp only [sub_zero, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    have he : -(x ^ 2) / (2 * (1 / 25 : ℝ)) = -(x ^ 2 * 25) / 2 := by ring
    rw [he]
    congr 1
    field_simp
  have hrestrict : (∫ x in Ioi (1 : ℝ), x ^ 2 ∂γ) =
      ∫ x in Ioi (1 : ℝ), x ^ 2 * gaussianPDFReal 0 (1 / 25 : ℝ≥0) x := by
    rw [← integral_indicator measurableSet_Ioi,
      integral_gaussianReal_eq_integral_smul (by norm_num : (1 / 25 : ℝ≥0) ≠ 0)]
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simp only [Set.indicator_of_mem hx, smul_eq_mul, mul_comm]
    · simp only [Set.indicator_of_notMem hx, smul_zero]
  rw [hrestrict]
  unfold normalTail
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [hdensity]
  have hs25 : sqrtN 25 = 5 := by norm_num [sqrtN]
  norm_num only [hs25, Nat.cast_ofNat, one_mul, mul_one, one_pow]
  ring

/-- The strict tail square is dominated by the sixth power, everywhere. -/
private theorem t6_tail_le_sixth (x : ℝ) :
    (if |x| > 1 then x ^ 2 else 0) ≤ x ^ 6 := by
  split_ifs with hx
  · have hx2 : 1 ≤ x ^ 2 := by
      have hs := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg x)).mpr hx.le
      simpa only [one_pow, sq_abs] using hs
    have hx4 : 1 ≤ x ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - 1)]
    have hm := mul_le_mul_of_nonneg_left hx4 (sq_nonneg x)
    nlinarith [hm]
  · positivity

theorem normal_shift_mse_counterexample_proof :
    Measurable normalEffect ∧ Integrable normalEffect normalPopulation ∧
    populationMean normalPopulation normalEffect = 0 ∧
    effectSupport normalPopulation normalEffect = {-1, 1} ∧ effectRadius normalPopulation normalEffect = 1 ∧
    NormalRemainder (iidSamples normalPopulation) shiftedNormalMean normalZ normalEpsilon 0 1 ∧
    SmallRemainderMS (iidSamples normalPopulation) normalEpsilon ∧
    (∀ n : ℕ, 1 ≤ n → (∫ s, normalEpsilon n s ^ 2 ∂iidSamples normalPopulation) = 1 / (n : ℝ)) ∧
    (∀ s, |normalMean 25 s| ≤ 1 / 2 →
      clipReal 0 1 (shiftedNormalMean 25 s) = shiftedNormalMean 25 s ∧ shiftedDifference 25 s ^ 2 = 1 / 625) ∧
    pr (iidSamples normalPopulation) {s | |normalMean 25 s| ≤ 1 / 2} ≥ 21 / 25 ∧
    (∫ s, shiftedDifference 25 s ^ 2 ∂iidSamples normalPopulation) ≥ 21 / 15625 ∧
    normalTail 25 1 1 =
      (∫ s, if |normalMean 25 s| > 1 then normalMean 25 s ^ 2 else 0 ∂iidSamples normalPopulation) ∧
    normalTail 25 1 1 ≤ (∫ s, normalMean 25 s ^ 6 ∂iidSamples normalPopulation) ∧
    (∫ s, normalMean 25 s ^ 6 ∂iidSamples normalPopulation) = 15 / 15625 ∧
    (∫ s, shiftedDifference 25 s ^ 2 ∂iidSamples normalPopulation) - normalTail 25 1 1 ≥ 6 / 15625 ∧
    (0 : ℝ) < 6 / 15625 := by
  have hpop := t6_effect_population
  have hrem := normal_shift_remainder_ms
  have hcentral := t6_central_probability
  have hlower := t6_mse_lower
  have htail := t6_tail_density_identity
  have h6 := t15_moment_transport (iidSamples normalPopulation) (normalMean 25)
    (t6_normal_mean_measurable 25) (1 / 25)
    (by simpa only [Nat.cast_ofNat] using t6_normal_mean_law 25 (by norm_num)) 6
  have h6val : (∫ s, normalMean 25 s ^ 6 ∂iidSamples normalPopulation) = 15 / 15625 := by
    rw [h6.2, (t15_gaussian_even_moments (1 / 25) (by norm_num)).2.2]
    norm_num
  have hm := t6_normal_mean_measurable 25
  have htailI : Integrable (fun s => if |normalMean 25 s| > 1 then normalMean 25 s ^ 2 else 0)
      (iidSamples normalPopulation) := by
    apply h6.1.mono'
      ((Measurable.ite
        (measurableSet_lt measurable_const (by simpa only [Real.norm_eq_abs] using hm.norm))
        (hm.pow_const 2) measurable_const).aestronglyMeasurable)
    apply ae_of_all
    intro s
    have hn : 0 ≤ (if |normalMean 25 s| > 1 then normalMean 25 s ^ 2 else 0 : ℝ) := by
      split_ifs <;> positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using t6_tail_le_sixth (normalMean 25 s)
  have htailBound : normalTail 25 1 1 ≤
      (∫ s, normalMean 25 s ^ 6 ∂iidSamples normalPopulation) := by
    rw [htail]
    exact integral_mono htailI h6.1 (fun s => t6_tail_le_sixth (normalMean 25 s))
  refine ⟨hpop.1, hpop.2.1, hpop.2.2.1, hpop.2.2.2.1, hpop.2.2.2.2,
    t6_normal_remainder, hrem.2, hrem.1, ?_, hcentral, hlower, htail, htailBound, h6val, ?_, ?_⟩
  · intro s hs
    have hh := shifted_25_central (normalMean 25 s) hs
    simpa only [shiftedNormalMean, shiftedDifference, Nat.cast_ofNat] using hh.2.2
  · rw [h6val] at htailBound
    linarith
  · norm_num

end
end AronowAudit.P017.Wave1
