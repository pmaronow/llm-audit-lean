import AronowAudit.P010.P010_Population
import AronowAudit.P033.P033_Audit
import AronowAudit.P053.P053_NormalQuantiles

namespace AronowAudit.P033.Wave1

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section

local instance GP010P033B1b_t1_normal_nullSingleton : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

lemma GP010P033B1b_t1_normalCDF_eq (x : ℝ) : normalCDF x = cdf (gaussianReal 0 1) x := by
  rw [cdf_eq_real]
  rfl

lemma GP010P033B1b_t1_critical_bridge :
    normalCritical = AronowAudit.P053.normalCritical (1/20) := by
  unfold normalCritical normalQuantile AronowAudit.P053.normalCritical
  congr 1
  ext x
  norm_num [normalCDF, AronowAudit.P053.standardNormalCDF, measureReal_def]

lemma GP010P033B1b_t1_critical_pos : 0 < normalCritical := by
  rw [GP010P033B1b_t1_critical_bridge]
  exact AronowAudit.P053.NormalCompletion.normalCritical_pos (1/20)
    (by norm_num) (by norm_num)

lemma GP010P033B1b_t1_critical_cdf : normalCDF normalCritical = 39/40 := by
  have h := AronowAudit.P053.NormalCompletion.normalCritical_cdf (1/20)
    (by norm_num) (by norm_num)
  rw [← GP010P033B1b_t1_critical_bridge] at h
  norm_num [AronowAudit.P053.standardNormalCDF, normalCDF, measureReal_def] at h ⊢
  exact h

/-- Closed central mass, retaining the exact endpoint convention. -/
lemma GP010P033B1b_t1_normal_central_mass (c : ℝ) (hc : 0 ≤ c) :
    (gaussianReal 0 1).real (Icc (-c) c) = 2*normalCDF c-1 := by
  have hcont : ContinuousWithinAt (cdf (gaussianReal 0 1)) (Iic (-c)) (-c) :=
    (AronowAudit.P053.NormalCompletion.cdf_continuousAt
      (gaussianReal 0 1) (-c)).continuousWithinAt
  have hnonneg : 0 ≤ cdf (gaussianReal 0 1) c-cdf (gaussianReal 0 1) (-c) :=
    sub_nonneg.mpr ((monotone_cdf (μ := gaussianReal 0 1)) (by linarith))
  have hmass : gaussianReal 0 1 (Icc (-c) c) = ENNReal.ofReal
      (cdf (gaussianReal 0 1) c-cdf (gaussianReal 0 1) (-c)) := by
    calc
      _ = (cdf (gaussianReal 0 1)).measure (Icc (-c) c) := by rw [measure_cdf]
      _ = _ := by rw [StieltjesFunction.measure_Icc, hcont.leftLim_eq]
  rw [measureReal_def, hmass, ENNReal.toReal_ofReal hnonneg,
    AronowAudit.P053.NormalCompletion.normal_cdf_neg, ← GP010P033B1b_t1_normalCDF_eq]
  ring

/-- Center and divide by a positive standard deviation. -/
lemma GP010P033B1b_t1_standardize {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Ω → ℝ) (τ s : ℝ) (hs : 0 < s)
    (hT : HasLaw T (gaussianReal τ ⟨s^2, sq_nonneg s⟩) μ) :
    HasLaw (fun ω => (T ω-τ)/s) (gaussianReal 0 1) μ := by
  have hv : (⟨s^2, sq_nonneg s⟩ : NNReal) ≠ 0 := by
    intro hzero
    have hz := congrArg (fun x : NNReal => (x : ℝ)) hzero
    change s^2 = 0 at hz
    exact (pow_ne_zero 2 (ne_of_gt hs)) hz
  have hg := gaussianReal_div_const (gaussianReal_sub_const hT τ) s
  have heq : (⟨s^2, sq_nonneg s⟩ / NNReal.mk (s^2) (sq_nonneg s) : NNReal) = 1 := div_self hv
  simpa only [sub_self, zero_div, heq] using hg

/-- Exact pointwise geometry of a symmetric confidence interval. -/
lemma GP010P033B1b_t1_interval_event {Ω : Type*} (T : Ω → ℝ) (τ c s : ℝ) (hs : 0 < s) :
    {ω | τ ∈ Icc (T ω-c*s) (T ω+c*s)} =
      {ω | (T ω-τ)/s ∈ Icc (-c) c} := by
  ext ω
  simp only [mem_setOf_eq, mem_Icc, le_div_iff₀ hs, div_le_iff₀ hs]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith

lemma GP010P033B1b_t1_coverage_of_pivot {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℝ) (τ s c : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hZ : HasLaw (fun ω => (T ω-τ)/s) (gaussianReal 0 1) μ) :
    intervalCoverage μ T τ (c*s) = 2*normalCDF c-1 := by
  unfold intervalCoverage
  rw [GP010P033B1b_t1_interval_event T τ c s hs]
  calc
    _ = (gaussianReal 0 1).real (Icc (-c) c) :=
      hZ.measureReal_eq measurableSet_Icc
    _ = _ := GP010P033B1b_t1_normal_central_mass c hc.le

lemma GP010P033B1b_t1_gaussian_affine_coverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℝ) (τ s c : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hT : HasLaw T (gaussianReal τ ⟨s^2, sq_nonneg s⟩) μ) :
    intervalCoverage μ T τ (c*s) = 2*normalCDF c-1 :=
  GP010P033B1b_t1_coverage_of_pivot μ T τ s c hs hc (GP010P033B1b_t1_standardize μ T τ s hs hT)

lemma GP010P033B1b_t1_se_facts :
    0 < m1SELinear ∧ 0 < m1SECorrected ∧
    m1SELinear^2 = 83/25 ∧ m1SECorrected^2 = 82/5 := by
  have h83 : (Real.sqrt 83)^2 = 83 := Real.sq_sqrt (by norm_num)
  have h410 : (Real.sqrt 410)^2 = 410 := Real.sq_sqrt (by norm_num)
  refine ⟨by unfold m1SELinear; positivity,
    by unfold m1SECorrected; positivity, ?_, ?_⟩
  · unfold m1SELinear
    rw [div_pow, h83]
    norm_num
  · unfold m1SECorrected
    rw [div_pow, h410]
    norm_num

/-- Product-Gaussian specialization using signed left and right weights. -/
lemma GP010P033B1b_t1_rd_gaussian (w : Fin 4 → ℝ) (s : ℝ)
    (hm : (∑ si : Fin 2 × Fin 4,
      (if si.1 = 0 then -w si.2 else w si.2) *
      (if si.1 = 0 then m1Control (-m1Distance si.2)
        else m1Treated (m1Distance si.2))) = 4)
    (hv : (∑ si : Fin 2 × Fin 4,
      (if si.1 = 0 then -w si.2 else w si.2)^2) = s^2) :
    HasLaw (rdEstimator w) (gaussianReal 4 ⟨s^2, sq_nonneg s⟩)
      (rdConditionalLaw m1Treated m1Control) := by
  let mean : Fin 2 × Fin 4 → ℝ := fun si =>
    if si.1 = 0 then m1Control (-m1Distance si.2) else m1Treated (m1Distance si.2)
  let weight : Fin 2 × Fin 4 → ℝ := fun si => if si.1 = 0 then -w si.2 else w si.2
  have heq : rdEstimator w = fun Y => ∑ si, weight si*Y si := by
    funext Y
    norm_num [rdEstimator, Fintype.sum_prod_type, Fin.sum_univ_succ, weight]
    ring
  have hg := gaussian_product_law mean weight
  change (∑ si, weight si*mean si) = 4 at hm
  change (∑ si, weight si^2) = s^2 at hv
  rw [hm, hv] at hg
  have hnn : (s^2).toNNReal = (⟨s^2, sq_nonneg s⟩ : NNReal) :=
    Real.toNNReal_of_nonneg (sq_nonneg s)
  rw [hnn] at hg
  rw [heq]
  exact hg

lemma GP010P033B1b_t1_m1_laws :
    HasLaw (rdEstimator m1Linear)
      (gaussianReal 4 ⟨m1SELinear^2, sq_nonneg m1SELinear⟩)
      (rdConditionalLaw m1Treated m1Control) ∧
    HasLaw (rdEstimator m1Corrected)
      (gaussianReal 4 ⟨m1SECorrected^2, sq_nonneg m1SECorrected⟩)
      (rdConditionalLaw m1Treated m1Control) := by
  have hsa := GP010P033B1b_t1_se_facts.2.2.1
  have hsb := GP010P033B1b_t1_se_facts.2.2.2
  constructor
  · apply GP010P033B1b_t1_rd_gaussian
    · norm_num [m1Linear, m1Control, m1Treated, m1Distance,
        Fintype.sum_prod_type, Fin.sum_univ_succ]
    · rw [hsa]
      norm_num [m1Linear, Fintype.sum_prod_type, Fin.sum_univ_succ]
  · apply GP010P033B1b_t1_rd_gaussian
    · norm_num [m1Corrected, m1Linear, m1Bias, m1BiasMoment, m1Curvature,
        m1Control, m1Treated, m1Distance, Fintype.sum_prod_type, Fin.sum_univ_succ]
    · rw [hsb]
      norm_num [m1Corrected, m1Linear, m1Bias, m1BiasMoment, m1Curvature,
        Fintype.sum_prod_type, Fin.sum_univ_succ]

lemma GP010P033B1b_t1_m1_pivots :
    HasLaw (fun Y => (rdEstimator m1Linear Y-4)/m1SELinear)
      (gaussianReal 0 1) (rdConditionalLaw m1Treated m1Control) ∧
    HasLaw (fun Y => (rdEstimator m1Corrected Y-4)/m1SECorrected)
      (gaussianReal 0 1) (rdConditionalLaw m1Treated m1Control) :=
  ⟨GP010P033B1b_t1_standardize _ _ 4 _ GP010P033B1b_t1_se_facts.1 GP010P033B1b_t1_m1_laws.1,
    GP010P033B1b_t1_standardize _ _ 4 _ GP010P033B1b_t1_se_facts.2.1 GP010P033B1b_t1_m1_laws.2⟩

lemma GP010P033B1b_t1_observed :
    rdEstimator m1Linear m1Observed = 4 ∧ rdEstimator m1Corrected m1Observed = 4 := by
  norm_num [rdEstimator, m1Linear, m1Corrected, m1Bias, m1BiasMoment,
    m1Curvature, m1Observed, Fin.sum_univ_succ]

lemma GP010P033B1b_t1_t_comparisons :
    absoluteT (rdEstimator m1Corrected m1Observed) m1SECorrected < 49/25 ∧
    (49/25 : ℝ) < absoluteT (rdEstimator m1Linear m1Observed) m1SELinear := by
  rcases GP010P033B1b_t1_se_facts with ⟨ha, hb, hsa, hsb⟩
  rw [GP010P033B1b_t1_observed.1, GP010P033B1b_t1_observed.2]
  norm_num only [absoluteT, Nat.abs_ofNat]
  constructor
  · apply (div_lt_iff₀ hb).2
    have hn : 0 < (49/25 : ℝ)*m1SECorrected := mul_pos (by norm_num) hb
    apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 4) hn.le).mp
    rw [mul_pow, hsb]
    norm_num
  · apply (lt_div_iff₀ ha).2
    have hn : 0 < (49/25 : ℝ)*m1SELinear := mul_pos (by norm_num) ha
    apply (sq_lt_sq₀ hn.le (by norm_num : (0 : ℝ) ≤ 4)).mp
    rw [mul_pow, hsa]
    norm_num

theorem diagnostic_counterexample_proof :
    Continuous m1Control ∧ Continuous m1Treated ∧
    rdEffect m1Treated m1Control 0 = 4 ∧
    (∫ Y, rdEstimator m1Linear Y ∂rdConditionalLaw m1Treated m1Control) = 4 ∧
    (∫ Y, rdEstimator m1Corrected Y ∂rdConditionalLaw m1Treated m1Control) = 4 ∧
    variance (rdEstimator m1Linear) (rdConditionalLaw m1Treated m1Control) = 83/25 ∧
    variance (rdEstimator m1Corrected) (rdConditionalLaw m1Treated m1Control) = 82/5 ∧
    m1SELinear = Real.sqrt (variance (rdEstimator m1Linear)
      (rdConditionalLaw m1Treated m1Control)) ∧
    m1SECorrected = Real.sqrt (variance (rdEstimator m1Corrected)
      (rdConditionalLaw m1Treated m1Control)) ∧
    HasLaw (fun Y => (rdEstimator m1Linear Y-4)/m1SELinear)
      (gaussianReal 0 1) (rdConditionalLaw m1Treated m1Control) ∧
    HasLaw (fun Y => (rdEstimator m1Corrected Y-4)/m1SECorrected)
      (gaussianReal 0 1) (rdConditionalLaw m1Treated m1Control) ∧
    intervalCoverage (rdConditionalLaw m1Treated m1Control) (rdEstimator m1Linear)
      4 (normalCritical*m1SELinear) = 19/20 ∧
    intervalCoverage (rdConditionalLaw m1Treated m1Control) (rdEstimator m1Corrected)
      4 (normalCritical*m1SECorrected) = 19/20 ∧
    intervalCoverage (rdConditionalLaw m1Treated m1Control) (rdEstimator m1Linear)
      4 ((49/25)*m1SELinear) = 2*normalCDF (49/25)-1 ∧
    intervalCoverage (rdConditionalLaw m1Treated m1Control) (rdEstimator m1Corrected)
      4 ((49/25)*m1SECorrected) = 2*normalCDF (49/25)-1 ∧
    0 < m1SELinear ∧ m1SELinear < m1SECorrected ∧
    rdEstimator m1Linear m1Observed = 4 ∧ rdEstimator m1Corrected m1Observed = 4 ∧
    absoluteT (rdEstimator m1Corrected m1Observed) m1SECorrected < 49/25 ∧
    (49/25 : ℝ) < absoluteT (rdEstimator m1Linear m1Observed) m1SELinear := by
  rcases m1_probability_moments with ⟨hma, hmb, hva, hvb⟩
  rcases GP010P033B1b_t1_se_facts with ⟨ha, hb, hsa, hsb⟩
  have hca (c : ℝ) (hc : 0 < c) :
      intervalCoverage (rdConditionalLaw m1Treated m1Control) (rdEstimator m1Linear)
        4 (c*m1SELinear) = 2*normalCDF c-1 :=
    GP010P033B1b_t1_coverage_of_pivot _ _ 4 _ c ha hc GP010P033B1b_t1_m1_pivots.1
  have hcb (c : ℝ) (hc : 0 < c) :
      intervalCoverage (rdConditionalLaw m1Treated m1Control) (rdEstimator m1Corrected)
        4 (c*m1SECorrected) = 2*normalCDF c-1 :=
    GP010P033B1b_t1_coverage_of_pivot _ _ 4 _ c hb hc GP010P033B1b_t1_m1_pivots.2
  have hcza : intervalCoverage (rdConditionalLaw m1Treated m1Control)
      (rdEstimator m1Linear) 4 (normalCritical*m1SELinear) = 19/20 := by
    rw [hca normalCritical GP010P033B1b_t1_critical_pos, GP010P033B1b_t1_critical_cdf]
    norm_num
  have hczb : intervalCoverage (rdConditionalLaw m1Treated m1Control)
      (rdEstimator m1Corrected) 4 (normalCritical*m1SECorrected) = 19/20 := by
    rw [hcb normalCritical GP010P033B1b_t1_critical_pos, GP010P033B1b_t1_critical_cdf]
    norm_num
  refine ⟨?_, ?_, ?_, hma, hmb, hva, hvb, ?_, ?_,
    GP010P033B1b_t1_m1_pivots.1, GP010P033B1b_t1_m1_pivots.2, hcza, hczb,
    hca (49/25) (by norm_num), hcb (49/25) (by norm_num), ha, ?_,
    GP010P033B1b_t1_observed.1, GP010P033B1b_t1_observed.2, GP010P033B1b_t1_t_comparisons.1, GP010P033B1b_t1_t_comparisons.2⟩
  · unfold m1Control
    fun_prop
  · unfold m1Treated
    fun_prop
  · norm_num [rdEffect, m1Control, m1Treated]
  · rw [hva, ← hsa, Real.sqrt_sq (le_of_lt ha)]
  · rw [hvb, ← hsb, Real.sqrt_sq (le_of_lt hb)]
  · apply (sq_lt_sq₀ ha.le hb.le).mp
    rw [hsa, hsb]
    norm_num

/-- Chebyshev for the actual standard Gaussian, with an inclusive tail. -/
lemma GP010P033B1b_t2_standard_tail (r : ℝ) (hr : 0 < r) :
    (gaussianReal 0 1).real {x : ℝ | r ≤ |x|} ≤ 1/r^2 := by
  have h := meas_ge_le_variance_div_sq
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2) hr
  have he : (∫ x : ℝ, id x ∂gaussianReal 0 1) = 0 := by
    simpa using (integral_id_gaussianReal (μ := 0) (v := 1))
  have hv : variance id (gaussianReal 0 1) = 1 := by
    simpa using (variance_id_gaussianReal (μ := 0) (v := 1))
  simp only [hv, id_eq, integral_id_gaussianReal, sub_zero] at h
  have hreal := ENNReal.toReal_mono (by simp : ENNReal.ofReal (1/r^2) ≠ ⊤) h
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  exact hreal

/-- Chebyshev lower bound for the CLOSED central interval.
The complement is a strict tail and is contained in the inclusive tail above. -/
lemma GP010P033B1b_t2_central_lower (r : ℝ) (hr : 0 < r) :
    1-1/r^2 ≤ (gaussianReal 0 1).real (Icc (-r) r) := by
  have hsub : (Icc (-r) r)ᶜ ⊆ {x : ℝ | r ≤ |x|} := by
    intro x hx
    have hn : ¬ (-r ≤ x ∧ x ≤ r) := hx
    change r ≤ |x|
    by_cases hx0 : 0 ≤ x
    · rw [abs_of_nonneg hx0]
      have : r < x := by
        by_contra hh
        apply hn
        exact ⟨by linarith, le_of_not_gt hh⟩
      exact this.le
    · rw [abs_of_neg (lt_of_not_ge hx0)]
      have : x < -r := by
        by_contra hh
        apply hn
        exact ⟨le_of_not_gt hh, by linarith⟩
      linarith
  have hm := measureReal_mono (μ := gaussianReal 0 1) hsub
  rw [measureReal_compl measurableSet_Icc, probReal_univ] at hm
  have ht := GP010P033B1b_t2_standard_tail r hr
  linarith

lemma GP010P033B1b_t2_critical_lt_five : normalCritical < 5 := by
  have hl := GP010P033B1b_t2_central_lower 5 (by norm_num)
  rw [GP010P033B1b_t1_normal_central_mass 5 (by norm_num)] at hl
  have hcrit := GP010P033B1b_t1_critical_cdf
  have hlt : normalCDF normalCritical < normalCDF 5 := by
    norm_num at hl
    linarith
  rw [GP010P033B1b_t1_normalCDF_eq, GP010P033B1b_t1_normalCDF_eq] at hlt
  exact AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.lt_iff_lt.mp hlt

/-- Exact source inclusion for M2. Only the upper endpoint of the interval is needed. -/
lemma GP010P033B1b_t2_m2_event_inclusion (κ : ℝ) :
    {Y | 24 ∈ Icc (rdEstimator m1Linear Y-κ*m1SELinear)
      (rdEstimator m1Linear Y+κ*m1SELinear)} ⊆
    {Y | 20/m1SELinear-κ ≤ (rdEstimator m1Linear Y-4)/m1SELinear} := by
  intro Y hY
  have ha := GP010P033B1b_t1_se_facts.1
  change 20/m1SELinear-κ ≤ (rdEstimator m1Linear Y-4)/m1SELinear
  rw [le_div_iff₀ ha]
  have hcancel : (20/m1SELinear-κ)*m1SELinear = 20-κ*m1SELinear := by
    field_simp [ne_of_gt ha]
    <;> ring
  rw [hcancel]
  have hy : (24 : ℝ) ≤ rdEstimator m1Linear Y+κ*m1SELinear := hY.2
  linarith

lemma GP010P033B1b_t2_bias_ratio_square : (20/m1SELinear)^2 = (10000/83 : ℝ) := by
  rw [div_pow, GP010P033B1b_t1_se_facts.2.2.1]
  norm_num

lemma GP010P033B1b_t2_bias_ratio_gt_ten : (10 : ℝ) < 20/m1SELinear := by
  have hp : 0 < 20/m1SELinear := div_pos (by norm_num) GP010P033B1b_t1_se_facts.1
  apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 10) hp.le).mp
  rw [GP010P033B1b_t2_bias_ratio_square]
  norm_num

lemma GP010P033B1b_t2_printed_threshold : (5 : ℝ) < 20/m1SELinear-(49/25) := by
  have hp : 0 < 20/m1SELinear := div_pos (by norm_num) GP010P033B1b_t1_se_facts.1
  have hsq : (5+(49/25 : ℝ))^2 < (20/m1SELinear)^2 := by
    rw [GP010P033B1b_t2_bias_ratio_square]
    norm_num
  have hlt := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 5+49/25) hp.le).mp hsq
  linarith

/-- Any M2 critical multiplier whose standardized lower threshold is at least five. -/
lemma GP010P033B1b_t2_m2_coverage_upper (κ : ℝ) (hκ : 5 ≤ 20/m1SELinear-κ) :
    intervalCoverage (rdConditionalLaw m2Treated m1Control)
      (rdEstimator m1Linear) 24 (κ*m1SELinear) ≤ 1/25 := by
  let Z : ((Fin 2 × Fin 4) → ℝ) → ℝ :=
    fun Y => (rdEstimator m1Linear Y-4)/m1SELinear
  have hZ : HasLaw Z (gaussianReal 0 1)
      (rdConditionalLaw m2Treated m1Control) := by
    rw [m2_conditional_law_eq]
    exact GP010P033B1b_t1_m1_pivots.1
  letI : IsProbabilityMeasure (rdConditionalLaw m2Treated m1Control) := by
    unfold rdConditionalLaw
    infer_instance
  have hsub : {Y | 24 ∈ Icc (rdEstimator m1Linear Y-κ*m1SELinear)
        (rdEstimator m1Linear Y+κ*m1SELinear)} ⊆ {Y | 5 ≤ |Z Y|} := by
    intro Y hY
    have hz : 20/m1SELinear-κ ≤ Z Y := GP010P033B1b_t2_m2_event_inclusion κ hY
    exact le_trans (le_trans hκ hz) (le_abs_self (Z Y))
  unfold intervalCoverage
  calc
    _ ≤ (rdConditionalLaw m2Treated m1Control).real {Y | 5 ≤ |Z Y|} :=
      measureReal_mono hsub
    _ = (gaussianReal 0 1).real {x : ℝ | 5 ≤ |x|} :=
      hZ.measureReal_eq (measurableSet_le measurable_const measurable_id.abs)
    _ ≤ 1/25 := by
      convert GP010P033B1b_t2_standard_tail 5 (by norm_num) using 1 <;> norm_num

lemma GP010P033B1b_t2_m2_printed_upper :
    intervalCoverage (rdConditionalLaw m2Treated m1Control)
      (rdEstimator m1Linear) 24 ((49/25)*m1SELinear) ≤ 1/25 :=
  GP010P033B1b_t2_m2_coverage_upper (49/25) GP010P033B1b_t2_printed_threshold.le

lemma GP010P033B1b_t2_m2_critical_upper :
    intervalCoverage (rdConditionalLaw m2Treated m1Control)
      (rdEstimator m1Linear) 24 (normalCritical*m1SELinear) ≤ 1/25 := by
  apply GP010P033B1b_t2_m2_coverage_upper
  have hz := GP010P033B1b_t2_critical_lt_five
  have hd := GP010P033B1b_t2_bias_ratio_gt_ten
  linarith

lemma GP010P033B1b_t2_m1_printed_lower :
    (1776/2401 : ℝ) ≤ intervalCoverage (rdConditionalLaw m1Treated m1Control)
      (rdEstimator m1Linear) 4 ((49/25)*m1SELinear) := by
  have hl := GP010P033B1b_t2_central_lower (49/25) (by norm_num)
  rw [GP010P033B1b_t1_normal_central_mass (49/25) (by norm_num)] at hl
  rw [GP010P033B1b_t1_coverage_of_pivot _ _ 4 _ (49/25) GP010P033B1b_t1_se_facts.1
    (by norm_num) GP010P033B1b_t1_m1_pivots.1]
  norm_num at hl ⊢
  exact hl

lemma GP010P033B1b_t2_m1_critical_exact :
    intervalCoverage (rdConditionalLaw m1Treated m1Control)
      (rdEstimator m1Linear) 4 (normalCritical*m1SELinear) = 19/20 := by
  rw [GP010P033B1b_t1_coverage_of_pivot _ _ 4 _ normalCritical GP010P033B1b_t1_se_facts.1
    GP010P033B1b_t1_critical_pos GP010P033B1b_t1_m1_pivots.1, GP010P033B1b_t1_critical_cdf]
  norm_num

/-- The low-coverage and exact-coverage predicates identify S and its complement. -/
lemma GP010P033B1b_t2_study_classification (N : ℕ) (S : Finset (Fin N)) :
    (Finset.univ.filter (fun j => intervalCoverage
      (if j ∈ S then rdConditionalLaw m2Treated m1Control else rdConditionalLaw m1Treated m1Control)
      (rdEstimator m1Linear) (studyEffect S j) (normalCritical*m1SELinear) ≤ 1/25)).card = S.card ∧
    (Finset.univ.filter (fun j => intervalCoverage
      (if j ∈ S then rdConditionalLaw m2Treated m1Control else rdConditionalLaw m1Treated m1Control)
      (rdEstimator m1Linear) (studyEffect S j) (normalCritical*m1SELinear) = 19/20)).card = N-S.card := by
  classical
  have hlo := GP010P033B1b_t2_m2_critical_upper
  have hex := GP010P033B1b_t2_m1_critical_exact
  have hne : intervalCoverage (rdConditionalLaw m2Treated m1Control)
      (rdEstimator m1Linear) 24 (normalCritical*m1SELinear) ≠ 19/20 := by
    intro he
    rw [he] at hlo
    norm_num at hlo
  have hfilter : (Finset.univ.filter (fun j => intervalCoverage
      (if j ∈ S then rdConditionalLaw m2Treated m1Control else rdConditionalLaw m1Treated m1Control)
      (rdEstimator m1Linear) (studyEffect S j) (normalCritical*m1SELinear) ≤ 1/25)) = S := by
    ext j
    by_cases hj : j ∈ S
    · norm_num [hj, studyEffect, hlo]
    · norm_num [hj, studyEffect, hex]
  have hfilter' : (Finset.univ.filter (fun j => intervalCoverage
      (if j ∈ S then rdConditionalLaw m2Treated m1Control else rdConditionalLaw m1Treated m1Control)
      (rdEstimator m1Linear) (studyEffect S j) (normalCritical*m1SELinear) = 19/20)) =
        Finset.univ \ S := by
    ext j
    by_cases hj : j ∈ S
    · norm_num [hj, studyEffect, hne]
    · norm_num [hj, studyEffect, hex]
  rw [hfilter, hfilter']
  refine ⟨rfl, ?_⟩
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ S),
    Finset.card_univ, Fintype.card_fin]

theorem diagnostic_correction_proof :
    (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (A B : Ω → ℝ) (τ σA σB c : ℝ), 0 < σA → 0 < σB → 0 < c →
      HasLaw A (gaussianReal τ ⟨σA^2, sq_nonneg σA⟩) μ →
      HasLaw B (gaussianReal τ ⟨σB^2, sq_nonneg σB⟩) μ →
      intervalCoverage μ A τ (c*σA) = 2*normalCDF c-1 ∧
      intervalCoverage μ B τ (c*σB) = 2*normalCDF c-1) ∧
    rdConditionalLaw m2Treated m1Control = rdConditionalLaw m1Treated m1Control ∧
    (∀ (E : Type*) [MeasurableSpace E] (F : ((Fin 2 × Fin 4) → ℝ) → E),
      Measurable F → (rdConditionalLaw m2Treated m1Control).map F =
        (rdConditionalLaw m1Treated m1Control).map F) ∧
    (∫ Y, rdEstimator m1Linear Y ∂rdConditionalLaw m2Treated m1Control) -
      rdEffect m2Treated m1Control 0 = -20 ∧
    (∀ κ : ℝ, 0 < κ → {Y | 24 ∈ Icc (rdEstimator m1Linear Y-κ*m1SELinear)
      (rdEstimator m1Linear Y+κ*m1SELinear)} ⊆
      {Y | 20/m1SELinear-κ ≤ (rdEstimator m1Linear Y-4)/m1SELinear}) ∧
    ((20/m1SELinear)^2 = (10000/83 : ℝ) ∧
      (5+(49/25 : ℝ))^2 = 30276/625 ∧ (30276/625 : ℝ) < 10000/83) ∧
    (0 < normalCritical ∧ normalCritical < 5 ∧ (10:ℝ) < 20/m1SELinear) ∧
    intervalCoverage (rdConditionalLaw m2Treated m1Control) (rdEstimator m1Linear)
      24 ((49/25)*m1SELinear) ≤ 1/25 ∧
    intervalCoverage (rdConditionalLaw m2Treated m1Control) (rdEstimator m1Linear)
      24 (normalCritical*m1SELinear) ≤ 1/25 ∧
    (1776/2401 : ℝ) ≤ intervalCoverage (rdConditionalLaw m1Treated m1Control)
      (rdEstimator m1Linear) 4 ((49/25)*m1SELinear) ∧
    (1/25 : ℝ) < 1776/2401 ∧
    intervalCoverage (rdConditionalLaw m1Treated m1Control) (rdEstimator m1Linear)
      4 (normalCritical*m1SELinear) = 19/20 ∧
    (∀ N : ℕ, 1 ≤ N →
      (∀ S : Finset (Fin N), studyDataLaw N S = studyDataLaw N ∅) ∧
      (∀ S : Finset (Fin N),
        (Finset.univ.filter (fun j => intervalCoverage
          (if j ∈ S then rdConditionalLaw m2Treated m1Control else rdConditionalLaw m1Treated m1Control)
          (rdEstimator m1Linear) (studyEffect S j) (normalCritical*m1SELinear) ≤ 1/25)).card = S.card ∧
        (Finset.univ.filter (fun j => intervalCoverage
          (if j ∈ S then rdConditionalLaw m2Treated m1Control else rdConditionalLaw m1Treated m1Control)
          (rdEstimator m1Linear) (studyEffect S j) (normalCritical*m1SELinear) = 19/20)).card = N-S.card) ∧
      ¬ ∃ F : (Fin N → (Fin 2 × Fin 4) → ℝ) → ℕ, Measurable F ∧
        ∀ S : Finset (Fin N), ∀ᵐ Y ∂studyDataLaw N S, F Y = S.card) ∧
    (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (L βhat : Ω → ℝ), MemLp L 2 μ → MemLp βhat 2 μ →
      variance (fun ω => L ω-βhat ω) μ = variance L μ + variance βhat μ -
        2*covariance L βhat μ) := by
  refine ⟨?_, m2_conditional_law_eq, ?_, ?_, ?_, ?_, ?_,
    GP010P033B1b_t2_m2_printed_upper, GP010P033B1b_t2_m2_critical_upper, GP010P033B1b_t2_m1_printed_lower,
    by norm_num, GP010P033B1b_t2_m1_critical_exact, ?_, ?_⟩
  · intro Ω mΩ μ hμ A B τ σA σB c hσA hσB hc hA hB
    exact ⟨GP010P033B1b_t1_gaussian_affine_coverage μ A τ σA c hσA hc hA,
      GP010P033B1b_t1_gaussian_affine_coverage μ B τ σB c hσB hc hB⟩
  · intro E mE F hF
    rw [m2_conditional_law_eq]
  · rw [m2_conditional_law_eq, m1_probability_moments.1]
    norm_num [rdEffect, m2Treated, m2Perturbation, m1Control, m1Treated]
  · intro κ hκ
    exact GP010P033B1b_t2_m2_event_inclusion κ
  · exact ⟨GP010P033B1b_t2_bias_ratio_square, by norm_num, by norm_num⟩
  · exact ⟨GP010P033B1b_t1_critical_pos, GP010P033B1b_t2_critical_lt_five, GP010P033B1b_t2_bias_ratio_gt_ten⟩
  · intro N hN
    refine ⟨?_, GP010P033B1b_t2_study_classification N, no_uniform_subset_count N hN⟩
    intro S
    exact (study_laws_identical.{0} N S).1
  · intro Ω mΩ μ hμ L βhat hL hβ
    exact bias_adjustment_variance μ L βhat hL hβ

end
end AronowAudit.P033.Wave1

namespace AronowAudit.P010.Wave1

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical

/-- Integrability of the identity under a normalized event law. -/
lemma GP010P033B1b_t15_integrable_eventLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (E : Set Ω) (hE : 0 < μ E)
    (hi : Integrable f (μ.restrict E)) :
    Integrable id (eventLaw μ f E) := by
  have him : Integrable id ((μ.restrict E).map f) := by
    apply (integrable_map_measure aestronglyMeasurable_id hf.aemeasurable).2
    simpa only [Function.id_comp] using hi
  unfold eventLaw
  exact him.smul_measure (ENNReal.inv_ne_top.mpr (ne_of_gt hE))

/-- Recover the first moment on potential passers from the observed passer law. -/
lemma GP010P033B1b_t15_passer_integrability_transfer {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K)
    (hi : Integrable observedY (μ.restrict (passEvent ∩ armEvent a))) :
    Integrable (potentialY a) (μ.restrict (potentialPass a)) := by
  letI := h.1
  have hobs : Integrable id (passerLaw μ a) :=
    GP010P033B1b_t15_integrable_eventLaw μ observedY measurable_observedY
      (passEvent ∩ armEvent a) (passing_event_positive μ h a) hi
  have hpot : Integrable id (eventLaw μ (potentialY a) (potentialPass a)) := by
    rw [conditional_law_consistency μ h a]
    exact hobs
  have hpos : 0 < μ (potentialPass a) :=
    ((nonzero_passing_corrected μ h.1 h.2.1).2.mp h.2.2) a
  change Integrable id ((μ (potentialPass a))⁻¹ •
    (μ.restrict (potentialPass a)).map (potentialY a)) at hpot
  have hmap : Integrable id ((μ.restrict (potentialPass a)).map (potentialY a)) := by
    exact (integrable_inv_smul_measure (ne_of_gt hpos)
      (measure_ne_top μ (potentialPass a))).mp hpot
  simpa only [Function.id_comp] using
    hmap.comp_measurable (measurable_potentialY a)

/-- The extended-real quantile at level `r` is finite, and its closed upper tail has mass `1-r`. -/
lemma GP010P033B1b_quantile_cut (F : Measure ℝ) [IsProbabilityMeasure F]
    (hc : Atomless F) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ q : ℝ, quantile F r = q ∧ F.real (Ici q) = 1-r := by
  letI : NullSingletonClass F := ⟨hc⟩
  have hcont : Continuous (cdf F) := continuous_iff_continuousAt.mpr
    (AronowAudit.P053.NormalCompletion.cdf_continuousAt F)
  obtain ⟨c, hcf⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq F hr hr1
  obtain ⟨l, hl⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq F
    (show 0 < r/2 by linarith) (show r/2 < 1 by linarith)
  let S : Set ℝ := {x | r ≤ cdf F x}
  have hne : S.Nonempty := ⟨c, by simpa [S, hcf]⟩
  have hb : BddBelow S := by
    refine ⟨l, ?_⟩
    intro x hx
    by_contra hh
    have hmono := (monotone_cdf F) (le_of_lt (lt_of_not_ge hh))
    change r ≤ cdf F x at hx
    rw [hl] at hmono
    linarith
  let q := sInf S
  have hqm : q ∈ S := (isClosed_le continuous_const hcont).csInf_mem hne hb
  have hqc : q ≤ c := csInf_le hb (show c ∈ S by simpa [S, hcf])
  have hqf : cdf F q = r := le_antisymm
    (by simpa [hcf] using (monotone_cdf F hqc)) hqm
  have hquant : quantile F r = (q : EReal) := by
    apply le_antisymm
    · apply sInf_le
      change r ≤ (F {y : ℝ | (y : EReal) ≤ (q : EReal)}).toReal
      simp only [EReal.coe_le_coe_iff]
      change r ≤ F.real (Iic q)
      rw [← cdf_eq_real]
      exact hqm
    · apply le_sInf
      intro x hx
      change r ≤ (F {y : ℝ | (y : EReal) ≤ x}).toReal at hx
      induction x using EReal.rec with
      | bot =>
        have hz : {y : ℝ | (y : EReal) ≤ ⊥} = ∅ := by ext y; simp
        simp only [hz, measure_empty, ENNReal.toReal_zero] at hx
        exact False.elim (not_le_of_gt hr hx)
      | coe x =>
        apply EReal.coe_le_coe_iff.mpr
        apply csInf_le hb
        change r ≤ cdf F x
        simp only [EReal.coe_le_coe_iff] at hx
        change r ≤ F.real (Iic x) at hx
        rwa [← cdf_eq_real] at hx
      | top => exact le_top
  refine ⟨q, hquant, ?_⟩
  have hi : F.real (Iio q) = r := by
    rw [measureReal_congr (Iio_ae_eq_Iic' (hc q)), ← cdf_eq_real, hqf]
  have hh := measureReal_compl (μ := F) measurableSet_Iio (s := Iio q)
  simpa only [compl_Iio, probReal_univ, hi] using hh

/-- Upper threshold means dominate means of events with at least their mass. -/
lemma GP010P033B1b_threshold_mean {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ)
    (hf : Measurable f) (hi : Integrable f ν) (A : Set Ω)
    (hA : MeasurableSet A) (q : ℝ)
    (hp : 0 < ν.real {x | q ≤ f x})
    (hm : ν.real {x | q ≤ f x} ≤ ν.real A) :
    eventMean ν f A ≤ eventMean ν f {x | q ≤ f x} := by
  have hia : Integrable (fun x => f x-q) ν := hi.sub (integrable_const q)
  have he : {x | 0 ≤ f x-q} = {x | q ≤ f x} := by ext x; simp
  have hbound := setIntegral_le_nonneg hA
    ((hf.sub measurable_const).stronglyMeasurable) hia
  change (∫ x in A, f x-q ∂ν) ≤ ∫ x in {x | 0 ≤ f x-q}, f x-q ∂ν at hbound
  rw [he, integral_sub hi.integrableOn (integrable_const q),
    integral_sub hi.integrableOn (integrable_const q), setIntegral_const,
    setIntegral_const] at hbound
  simp only [smul_eq_mul] at hbound
  have hnon : 0 ≤ ∫ x in {x | q ≤ f x}, f x-q ∂ν :=
    setIntegral_nonneg (measurableSet_le measurable_const hf) (by intro x hx; exact sub_nonneg.mpr hx)
  rw [integral_sub hi.integrableOn (integrable_const q), setIntegral_const] at hnon
  simp only [smul_eq_mul] at hnon
  change (∫ x in A, f x ∂ν) / ν.real A ≤
    (∫ x in {x | q ≤ f x}, f x ∂ν) / ν.real {x | q ≤ f x}
  apply (div_le_div_iff₀ (lt_of_lt_of_le hp hm) hp).mpr
  nlinarith

/-- Normalizing a restriction preserves every nested event mean. -/
lemma GP010P033B1b_normalized_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (P E : Set Ω) (hP : MeasurableSet P) (hpos : 0 < μ P) :
    eventMean ((μ P)⁻¹ • μ.restrict P) f E = eventMean μ f (P ∩ E) := by
  have hc : ((μ P)⁻¹).toReal ≠ 0 := by
    rw [ENNReal.toReal_inv]
    exact inv_ne_zero (ENNReal.toReal_ne_zero.mpr ⟨ne_of_gt hpos, measure_ne_top μ P⟩)
  unfold eventMean
  simp only [Measure.restrict_smul, Measure.restrict_restrict' hP,
    integral_smul_measure, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    Measure.restrict_apply' hP]
  rw [inter_comm E P]
  exact mul_div_mul_left _ _ hc

/-- The finite-branch bound alone, without the sharpness part of T14. -/
lemma GP010P033B1b_potential_bound {K d : ℕ} (μ : Measure (State K d))
    [IsProbabilityMeasure μ] (a : Fin K) (hA : 0 < μ alwaysPass)
    (hc : Atomless (eventLaw μ (potentialY a) (potentialPass a)))
    (hi : Integrable (potentialY a) (μ.restrict (potentialPass a)))
    (hr : potentialTrim μ a < 1) :
    eventMean μ (potentialY a) alwaysPass ≤
      tailUpper (eventLaw μ (potentialY a) (potentialPass a)) (potentialTrim μ a) := by
  let P := potentialPass (d := d) a
  let f := potentialY (d := d) a
  let r := potentialTrim μ a
  let ν := (μ P)⁻¹ • μ.restrict P
  let F := eventLaw μ f P
  have hPA : (alwaysPass : Set (State K d)) ⊆ P := fun ω hω => hω a
  have hP : MeasurableSet P := measurableSet_potentialPass a
  have hpos : 0 < μ P := lt_of_lt_of_le hA (measure_mono hPA)
  letI : IsProbabilityMeasure ν := ⟨by
    simp only [ν, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ne_of_gt hpos) (measure_ne_top μ P)⟩
  have hf : Measurable f := measurable_potentialY a
  have hif : Integrable f ν := hi.smul_measure (ENNReal.inv_ne_top.mpr (ne_of_gt hpos))
  have hmap : ν.map f = F := by
    dsimp only [ν]
    rw [Measure.map_smul _ hf.aemeasurable]
    rfl
  letI : IsProbabilityMeasure F := hmap ▸ inferInstance
  have hr0 : 0 ≤ r := by unfold r potentialTrim; positivity
  have hfail : ν.real (alwaysPassᶜ) =
      (μ ((otherPass a)ᶜ ∩ potentialPass a)).toReal / (μ P).toReal := by
    have hset : (alwaysPassᶜ ∩ P : Set (State K d)) =
        (otherPass a)ᶜ ∩ potentialPass a := by
      rw [always_pass_focal a]
      ext ω
      simp only [mem_inter_iff, mem_compl_iff, not_and, P]
      tauto
    simp only [ν, measureReal_def, Measure.smul_apply, smul_eq_mul,
      ENNReal.toReal_mul, ENNReal.toReal_inv,
      Measure.restrict_apply measurableSet_always.compl, hset, div_eq_mul_inv]
    ring
  have hmass : 1-r ≤ ν.real alwaysPass := by
    have hu := other_arm_conditional_union_bound μ inferInstance a hpos
    have hcompl := measureReal_compl (μ := ν) measurableSet_always
    rw [probReal_univ] at hcompl
    rw [← hfail] at hu
    change ν.real alwaysPassᶜ ≤ r at hu
    linarith
  have hmeanA : eventMean ν f alwaysPass = eventMean μ f alwaysPass := by
    rw [GP010P033B1b_normalized_mean μ f P alwaysPass hP hpos,
      inter_eq_right.mpr hPA]
  have hmeanTail : eventMean ν f {ω | quantile F r ≤ (f ω : EReal)} = tailUpper F r := by
    rw [GP010P033B1b_normalized_mean μ f P _ hP hpos]
    exact (eventMean_eventLaw μ f hf P hP hpos
      {y | quantile F r ≤ (y : EReal)}
      (measurableSet_le measurable_const measurable_coe_real_ereal)).symm
  change eventMean μ f alwaysPass ≤ tailUpper F r
  rw [← hmeanA, ← hmeanTail]
  by_cases hz : r = 0
  · have hquant : quantile F r = ⊥ := by
      apply bot_unique
      apply sInf_le
      simp [hz]
    have hmassOne : ν.real alwaysPass = 1 := le_antisymm (measureReal_le_one) (by linarith)
    have hmeasureOne : ν alwaysPass = 1 := by
      exact (ENNReal.toReal_eq_one_iff _).mp hmassOne
    have hae : ∀ᵐ ω ∂ν, ω ∈ alwaysPass :=
      (mem_ae_iff_prob_eq_one measurableSet_always).mpr hmeasureOne
    have hrestrict : ν.restrict alwaysPass = ν := Measure.restrict_eq_self_of_ae_mem hae
    have hset : {ω | quantile F r ≤ (f ω : EReal)} = univ := by simp [hquant]
    simp only [hset, eventMean, hrestrict, Measure.restrict_univ, measure_univ,
      ENNReal.toReal_one, div_one, hmeasureOne, le_refl]
  · obtain ⟨q, hq, hqmass⟩ := GP010P033B1b_quantile_cut F hc r (lt_of_le_of_ne hr0 (Ne.symm hz)) hr
    have hset : {ω | quantile F r ≤ (f ω : EReal)} = {ω | q ≤ f ω} := by
      ext ω; simp only [hq, EReal.coe_le_coe_iff]
    have htailmass : ν.real {ω | q ≤ f ω} = 1-r := by
      rw [← hqmass, ← hmap]
      simp only [measureReal_def, Measure.map_apply hf measurableSet_Ici]
      rfl
    rw [hset]
    apply GP010P033B1b_threshold_mean ν f hf hif alwaysPass measurableSet_always q
    · rw [htailmass]; linarith
    · rw [htailmass]; exact hmass

theorem observable_upper_bound_corrected_proof {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) (hA : 0 < μ alwaysPass)
    (hc : Atomless (μ.map observedY))
    (hi : Integrable observedY (μ.restrict (passEvent ∩ armEvent a))) :
    eventLaw μ (potentialY a) (potentialPass a) = passerLaw μ a ∧
    (∀ b, (μ (potentialPass b)).toReal = passingRate μ b) ∧
    potentialTrim μ a = trimRatio μ a ∧
    tailUpper (eventLaw μ (potentialY a) (potentialPass a)) (trimRatio μ a) = upperBound μ a ∧
    (trimRatio μ a < 1 →
      eventMean μ (potentialY a) alwaysPass = eventMean μ (potentialY a) (otherPass a ∩ potentialPass a) ∧
      eventMean μ (potentialY a) alwaysPass ≤ upperBound μ a) := by
  letI := h.1
  have hF := conditional_law_consistency μ h a
  have htrim := potential_trim_consistency μ h a
  have htail : tailUpper (eventLaw μ (potentialY a) (potentialPass a))
      (trimRatio μ a) = upperBound μ a := by
    rw [hF]
    exact (passer_tail_mean_formula μ h a).2.symm
  refine ⟨hF, ?_, htrim, htail, ?_⟩
  · intro b
    exact ((nonzero_passing_corrected μ h.1 h.2.1).1 b).symm
  · intro hr
    refine ⟨by rw [always_pass_focal a], ?_⟩
    have hci : Atomless (eventLaw μ (potentialY a) (potentialPass a)) := by
      rw [hF]
      exact passer_atomless μ a hc
    have hii := GP010P033B1b_t15_passer_integrability_transfer μ h a hi
    have hbound := GP010P033B1b_potential_bound μ a hA hci hii
      (by simpa only [htrim] using hr)
    rw [htrim, htail] at hbound
    exact hbound

end AronowAudit.P010.Wave1
