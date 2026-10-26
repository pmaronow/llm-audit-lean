import AronowAudit.P018.P018_Audit
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Order.DenselyOrdered
import AronowAudit.P018.Wave1.WeightedConsistency
import AronowAudit.P018.Wave1.Gap.GP0181B1
import AronowAudit.P018.Wave1.Gap.GP0182B1
import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.InfinitePi

/-!
P018-T8: corrected contrast coverage under the original `Standing` assumptions.
The proof derives the scalar projection CLT, covariance consistency, and studentization
before applying the fixed normal-quantile coverage argument.
-/

noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
open scoped symmDiff
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ## Coverage probabilities -/

theorem GP0182B2b_contrast_coverage_quantile_bridge (α : ℝ) :
    normalQuantile (1-α/2) = AronowAudit.P053.normalCritical α := by
  rfl

theorem GP0182B2b_contrast_coverage_quantile_pos (α : ℝ) (hα : 0 < α ∧ α < 1) :
    0 < normalQuantile (1-α/2) := by
  rw [GP0182B2b_contrast_coverage_quantile_bridge]
  exact AronowAudit.P053.NormalCompletion.normalCritical_pos α hα.1 hα.2

theorem GP0182B2b_contrast_coverage_quantile_mass (α : ℝ) (hα : 0 < α ∧ α < 1) :
    (gaussianReal 0 1 (Set.Icc (-normalQuantile (1-α/2))
      (normalQuantile (1-α/2)))).toReal = 1-α := by
  rw [GP0182B2b_contrast_coverage_quantile_bridge]
  exact AronowAudit.P053.NormalCompletion.normalCritical_interval_mass α hα.1 hα.2

/-- On the positive-variance event, cancel the positive square root.
The weak inequality `0 ≤ v` in the coverage event is kept literally. -/
theorem GP0182B2b_contrast_coverage_event_iff (x v q : ℝ) (hv : 0 < v) :
    (0 ≤ v ∧ |x| ≤ q * Real.sqrt v) ↔ |x / Real.sqrt v| ≤ q := by
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  simp only [hv.le, true_and]

theorem GP0182B2b_contrast_coverage_event_symmDiff {Ω : Type*} (x v : Ω → ℝ) (q : ℝ) :
    ({ω | 0 ≤ v ω ∧ |x ω| ≤ q * Real.sqrt (v ω)} ∆
      {ω | |x ω / Real.sqrt (v ω)| ≤ q}) ⊆ {ω | v ω ≤ 0} := by
  intro ω hω
  by_contra hbad
  have hv : 0 < v ω := lt_of_not_ge hbad
  have he := GP0182B2b_contrast_coverage_event_iff (x ω) (v ω) q hv
  rcases hω with hω | hω
  · exact hω.2 (he.mp hω.1)
  · exact hω.2 (he.mpr hω.1)

/-- Relate the changing-space weak-limit predicate to interval mass.
Using AEMeasurability here preserves the strength of the original predicate. -/
theorem GP0182B2b_contrast_coverage_interval_limit
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)]
    (T : ∀ N, Ω N → ℝ) (hT : weakLimit μ T (gaussianReal 0 1))
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun N => (μ N {ω | |T N ω| ≤ q}).toReal) atTop
      (𝓝 ((gaussianReal 0 1 (Set.Icc (-q) q)).toReal)) := by
  let P : ℕ → ProbabilityMeasure ℝ := fun N =>
    ⟨(μ N).map (T N), inferInstance⟩
  let G : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hP : Tendsto P atTop (𝓝 G) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro g
    have hg (N : ℕ) : (∫ z, g z ∂(P N : Measure ℝ)) =
        ∫ ω, g (T N ω) ∂μ N := by
      exact integral_map (hT.1 N) g.continuous.measurable.aestronglyMeasurable
    simpa only [hg, G, ProbabilityMeasure.coe_mk] using hT.2.2 g
  let GP0182B2b_gaussianNull : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)
  have hfront : (G : Measure ℝ) (frontier (Set.Icc (-q) q)) = 0 := by
    rw [frontier_Icc (by linarith : -q ≤ q)]
    exact ((Set.finite_singleton q).insert (-q)).measure_zero (gaussianReal 0 1)
  have hmass :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hP hfront
  have hreal := (ENNReal.continuousAt_toReal
    (measure_ne_top (gaussianReal 0 1) (Set.Icc (-q) q))).tendsto.comp hmass
  have he (N : ℕ) : (P N : Measure ℝ) (Set.Icc (-q) q) =
      μ N {ω | |T N ω| ≤ q} := by
    change ((μ N).map (T N)) (Set.Icc (-q) q) = _
    rw [Measure.map_apply_of_aemeasurable (hT.1 N) measurableSet_Icc]
    congr 1
    ext ω
    exact abs_le.symm
  change Tendsto (fun N => ((P N : Measure ℝ) (Set.Icc (-q) q)).toReal) atTop
    (𝓝 ((gaussianReal 0 1 (Set.Icc (-q) q)).toReal)) at hreal
  simpa only [he] using hreal

/-- Generic coverage argument. The later helpers derive both probabilistic
inputs and the concrete measurability facts from the original `Standing` hypothesis. -/
theorem GP0182B2b_contrast_coverage_from_studentization
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)]
    (x v : ∀ N, Ω N → ℝ)
    (hx : ∀ N, Measurable (x N)) (hv : ∀ N, Measurable (v N))
    (hweak : weakLimit μ (fun N ω => x N ω / Real.sqrt (v N ω))
      (gaussianReal 0 1))
    (hbad : Tendsto (fun N => (μ N {ω | v N ω ≤ 0}).toReal) atTop (𝓝 0))
    (α : ℝ) (hα : 0 < α ∧ α < 1) :
    Tendsto (fun N => (μ N {ω | 0 ≤ v N ω ∧
      |x N ω| ≤ normalQuantile (1-α/2) * Real.sqrt (v N ω)}).toReal)
      atTop (𝓝 (1-α)) := by
  let q := normalQuantile (1-α/2)
  let A := fun N => {ω : Ω N | 0 ≤ v N ω ∧ |x N ω| ≤ q * Real.sqrt (v N ω)}
  let B := fun N => {ω : Ω N | |x N ω / Real.sqrt (v N ω)| ≤ q}
  have hA (N : ℕ) : MeasurableSet (A N) :=
    (measurableSet_le measurable_const (hv N)).inter
      (measurableSet_le (continuous_abs.measurable.comp (hx N)) (measurable_const.mul (hv N).sqrt))
  have hB (N : ℕ) : MeasurableSet (B N) :=
    measurableSet_le (continuous_abs.measurable.comp ((hx N).div (hv N).sqrt)) measurable_const
  have hbound (N : ℕ) : |(μ N (A N)).toReal - (μ N (B N)).toReal| ≤
      (μ N {ω | v N ω ≤ 0}).toReal := by
    calc
      _ ≤ (μ N (A N ∆ B N)).toReal :=
        abs_measureReal_sub_le_measureReal_symmDiff
          (hA N).nullMeasurableSet (hB N).nullMeasurableSet
      _ ≤ _ := measureReal_mono (GP0182B2b_contrast_coverage_event_symmDiff (x N) (v N) q)
  have hdiff : Tendsto (fun N =>
      (μ N (A N)).toReal - (μ N (B N)).toReal) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbad
      (fun N => norm_nonneg _) (fun N => by simpa only [Real.norm_eq_abs] using hbound N)
  have hcentral : Tendsto (fun N => (μ N (B N)).toReal) atTop (𝓝 (1-α)) := by
    have h := GP0182B2b_contrast_coverage_interval_limit μ
      (fun N ω => x N ω / Real.sqrt (v N ω)) hweak q
      (GP0182B2b_contrast_coverage_quantile_pos α hα).le
    simpa only [q, B, GP0182B2b_contrast_coverage_quantile_mass α hα] using h
  have hsum := hdiff.add hcentral
  simpa only [sub_add_cancel, zero_add] using hsum


theorem GP0182B2b_measurable_inverse {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (A : Ω → Mat k) (hA : Measurable A) : Measurable (fun ω => (A ω)⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact ((continuous_id.matrix_det.measurable.comp hA).inv).smul
    (continuous_id.matrix_adjugate.measurable.comp hA)

theorem GP0182B2b_measurable_statistics {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (c : Vec k) (N : ℕ) :
    Measurable (fun ω : Fin N → U => dot c (coefficientError K ω)) ∧
    Measurable (fun ω : Fin N → U =>
      dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c)) := by
  classical
  have hp (d : Dyad N) : Measurable (fun ω : Fin N → U =>
      (ω (firstUnit d), ω (secondUnit d))) :=
    (measurable_pi_apply (firstUnit d)).prodMk (measurable_pi_apply (secondUnit d))
  have hX (d : Dyad N) : Measurable (fun ω : Fin N → U => design K ω d) :=
    by
    simpa only [design, Function.comp_def] using
      hK.2.1.comp (hp d)
  have hY (d : Dyad N) : Measurable (fun ω : Fin N → U => response K ω d) :=
    by
    simpa only [response, Function.comp_def] using
      hK.2.2.1.comp (hp d)
  have hXa (d : Dyad N) (a : Fin k) :
      Measurable (fun ω : Fin N → U => design K ω d a) :=
    (measurable_pi_apply a).comp (hX d)
  have hG : Measurable (fun ω : Fin N → U => sampleGram (design K ω)) := by
    apply measurable_pi_lambda
    intro a
    apply measurable_pi_lambda
    intro b
    simp only [sampleGram, Matrix.sum_apply, outer]
    fun_prop
  have hI := GP0182B2b_measurable_inverse _ hG
  have hIa (a b : Fin k) :
      Measurable (fun ω : Fin N → U => (sampleGram (design K ω))⁻¹ a b) :=
    (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hI)
  have hO (a : Fin k) :
      Measurable (fun ω : Fin N → U => sampleOLS (design K ω) (response K ω) a) := by
    simp only [sampleOLS, Matrix.mulVec, dotProduct, Finset.sum_apply,
      score, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hR (d : Dyad N) : Measurable (fun ω : Fin N → U =>
      fittedResidual (design K ω) (response K ω) d) := by
    simp only [fittedResidual, dot]
    fun_prop
  have hM (a b : Fin k) : Measurable (fun ω : Fin N → U =>
      meat members (fun d => score (design K ω d)
        (fittedResidual (design K ω) (response K ω) d)) a b) := by
    simp only [meat, Matrix.sum_apply, matrix_ite_apply, outer,
      score, Pi.smul_apply, smul_eq_mul, Matrix.zero_apply]
    apply Finset.measurable_fun_sum
    intro d hd
    apply Finset.measurable_fun_sum
    intro f hf
    split_ifs <;> fun_prop
  have hV (a b : Fin k) : Measurable (fun ω : Fin N → U =>
      sampleVariance members (design K ω) (response K ω) a b) := by
    simp only [sampleVariance, sandwich, Matrix.mul_apply]
    fun_prop
  constructor
  · simp only [dot, coefficientError, Pi.sub_apply]
    fun_prop
  · simp only [dot, Matrix.mulVec, dotProduct]
    fun_prop

theorem GP0182B2b_coverage_from_pivot {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (c : Vec k)
    (hweak : weakLimit (unitSampleLaw K) (fun N ω =>
      dot c (coefficientError K ω) /
        Real.sqrt (dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c)))
      (gaussianReal 0 1))
    (hbad : Tendsto (fun N : ℕ => (unitSampleLaw K N {ω |
      dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c) ≤ 0}).toReal)
      atTop (𝓝 0))
    (α : ℝ) (hα : 0 < α ∧ α < 1) :
    Tendsto (fun N : ℕ => (unitSampleLaw K N {ω |
      0 ≤ dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c) ∧
      |dot c (coefficientError K ω)| ≤ normalQuantile (1-α/2) *
        Real.sqrt (dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c))}).toReal)
      atTop (𝓝 (1-α)) := by
  let GP0182B2b_unitProbability : IsProbabilityMeasure K.μ := hK.1
  let GP0182B2b_sampleProbability (N : ℕ) : IsProbabilityMeasure (unitSampleLaw K N) := by
    unfold unitSampleLaw
    infer_instance
  exact GP0182B2b_contrast_coverage_from_studentization (unitSampleLaw K)
    (fun N ω => dot c (coefficientError K ω))
    (fun N ω => dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c))
    (fun N => (GP0182B2b_measurable_statistics K hK c N).1)
    (fun N => (GP0182B2b_measurable_statistics K hK c N).2)
    hweak hbad α hα

theorem GP0182B2b_mean_outer_quad {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {k : ℕ} (f : Ω → Vec k)
    (hi : ∀ a b, Integrable (fun ω => f ω a * f ω b) μ) (c : Vec k) :
    dot c ((meanMat μ (fun ω => outer (f ω) (f ω))).mulVec c) =
      ∫ ω, (dot c (f ω))^2 ∂μ := by
  have ht (a b : Fin k) :
      Integrable (fun ω => (c a * f ω a) * (c b * f ω b)) μ := by
    convert (hi a b).const_mul (c a * c b) using 1
    ext ω
    ring
  simp only [dot, pow_two, Finset.sum_mul_sum]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => ht a b))]
  simp_rw [integral_finsetSum _ (fun b _ => ht _ b)]
  simp only [Matrix.mulVec, dotProduct, meanMat, outer, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  calc
    c a * ((∫ ω, f ω a * f ω b ∂μ) * c b) =
        (c a * c b) * ∫ ω, f ω a * f ω b ∂μ := by ring
    _ = ∫ ω, (c a * f ω a) * (c b * f ω b) ∂μ := by
      rw [← integral_const_mul]
      congr 1
      ext ω
      ring

theorem GP0182B2b_populationGram_posDef {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) : (populationGram K).PosDef := by
  have hs : (populationGram K).IsHermitian := by
    ext a b
    simp only [Matrix.conjTranspose_apply, star_trivial, populationGram, meanMat, outer]
    congr 1
    ext uv
    ring
  have hps : (populationGram K).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hs
    intro c
    have hq := GP0182B2b_mean_outer_quad (K.μ.prod K.μ)
      (fun uv => K.X uv.1 uv.2) (corrected_pair_products K hK).1 c
    change 0 ≤ dot c ((populationGram K).mulVec c)
    rw [show dot c ((populationGram K).mulVec c) =
        ∫ uv, (dot c (K.X uv.1 uv.2))^2 ∂K.μ.prod K.μ from hq]
    exact integral_nonneg (fun _ => sq_nonneg _)
  exact hps.posDef_iff_det_ne_zero.mpr hK.2.2.2.2.2.2

theorem GP0182B2b_singleStanding {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) : RepeatedStanding (singleRecord K) := by
  refine ⟨hK.1, ?_, ?_, ?_, ?_⟩
  · intro N hN d
    exact Nat.zero_lt_one
  · intro N d t
    exact ⟨hK.2.1, hK.2.2.1⟩
  · obtain ⟨C, hC, hb⟩ := hK.2.2.2.2.1
    exact ⟨C, hC, fun _ _ _ => hb⟩
  · obtain ⟨j, hj⟩ := hK.2.2.2.2.2.1
    exact ⟨j, fun _ _ _ => hj⟩

theorem GP0182B2b_singleWeightedGram {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (ω : Fin N → U) :
    recordWeightedGram (singleRecord K) (fun _ _ => 1) ω = sampleGram (design K ω) := by
  calc
    _ = repeatedGram (singleRecord K) ω := by
      simp only [recordWeightedGram, repeatedGram, one_smul]
    _ = _ := corrected_single_gram K ω

theorem GP0182B2b_singleWeightedOLS {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (ω : Fin N → U) :
    recordWeightedOLS (singleRecord K) (fun _ _ => 1) ω =
      sampleOLS (design K ω) (response K ω) := by
  simp only [recordWeightedOLS, GP0182B2b_singleWeightedGram, recordWeightedXY,
    one_mul, corrected_single_XY]
  rfl

theorem GP0182B2b_singleWeightedVariance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (ω : Fin N → U) :
    recordWeightedVariance (singleRecord K) (fun _ _ => 1) ω =
      sampleVariance members (design K ω) (response K ω) := by
  rw [recordWeightedVariance, GP0182B2b_singleWeightedGram, GP0182B2b_singleWeightedOLS]
  have he : recordWeightedBlockScore (singleRecord K) (fun _ _ => 1)
      (sampleOLS (design K ω) (response K ω)) ω =
      fun d => score (design K ω d) (fittedResidual (design K ω) (response K ω) d) := by
    funext d
    change (∑ _ : Fin 1, score (design K ω d)
      (1 * (response K ω d - dot (design K ω d)
        (sampleOLS (design K ω) (response K ω))))) = _
    simp only [Fin.sum_univ_one, one_mul]
    rfl
  rw [he]
  rfl

theorem GP0182B2b_singleWeightedH {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (hN : 2 ≤ N) :
    recordWeightedH (singleRecord K) (fun (_ : Dyad N) _ => 1) = populationGram K := by
  have hg : recordWeightedGram (singleRecord K) (fun (_ : Dyad N) _ => 1) =
      (fun ω => sampleGram (design K ω)) := funext (GP0182B2b_singleWeightedGram K)
  simp only [recordWeightedH, hg, corrected_single_law,
    corrected_expected_gram K hK, smul_smul,
    inv_mul_cancel₀ (printed_Dpos hN).ne', one_smul]

theorem GP0182B2b_singleWeightedTarget {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (hN : 2 ≤ N) :
    recordWeightedTarget (singleRecord K) (fun (_ : Dyad N) _ => 1) = trueTarget K N := by
  have hb : recordWeightedBeta (singleRecord K) (fun (_ : Dyad N) _ => 1) =
      repeatedBeta (singleRecord K) N := by
    have hg : recordWeightedGram (singleRecord K) (fun (_ : Dyad N) _ => 1) =
        repeatedGram (singleRecord K) := by
      funext ω
      simp only [recordWeightedGram, repeatedGram, one_smul]
    have hy : recordWeightedXY (singleRecord K) (fun (_ : Dyad N) _ => 1) =
        (fun ω => ∑ d : Dyad N, ∑ t, score (repeatedX (singleRecord K) ω d t)
          (repeatedY (singleRecord K) ω d t)) := by
      funext ω
      simp only [recordWeightedXY, one_mul]
    simp only [recordWeightedBeta, repeatedBeta, hg, hy]
  rw [recordWeightedTarget, GP0182B2b_singleWeightedH K hK hN, hb,
    corrected_single_beta K hK hN]
  have hs : (fun ω : Fin N → U => ∑ d : Dyad N,
      recordWeightedBlockScore (singleRecord K) (fun _ _ => 1) (populationBeta K) ω d) =
      scoreSum K := by
    funext ω
    change (∑ d : Dyad N, ∑ _ : Fin 1, score (design K ω d)
      (1 * (response K ω d - dot (design K ω d) (populationBeta K)))) = _
    simp only [Fin.sum_univ_one, one_mul]
    rfl
  rw [hs]
  rfl

theorem GP0182B2b_singleSetting {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    WeightedConsistency.Setting (singleRecord K) K.X K.Y (fun _ _ _ => false)
      (fun _ _ _ => 1) 1 (populationGram K) := by
  refine ⟨GP0182B2b_singleStanding K hK, ?_, ?_, ?_,
    GP0182B2b_populationGram_posDef K hK, ?_⟩
  · intro N d
    exact fun a b _ => Subsingleton.elim (α := Fin 1) a b
  · intro N d t u v
    exact ⟨rfl, rfl⟩
  · intro N d t
    norm_num
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact (GP0182B2b_singleWeightedH K hK hN).symm

theorem GP0182B2b_variance_consistency {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    inProbability (unitSampleLaw K) (fun N ω =>
      (N : ℝ) • sampleVariance members (design K ω) (response K ω) - trueTarget K N) := by
  letI GP0182B2b_unitProb : IsProbabilityMeasure K.μ := hK.1
  letI GP0182B2b_sampleProb (N : ℕ) : IsProbabilityMeasure (unitSampleLaw K N) := by
    unfold unitSampleLaw
    infer_instance
  have h := weighted_consistency_common_directed_kernel (singleRecord K)
    (GP0182B2b_singleStanding K hK) (fun _ _ => by norm_num [singleRecord])
    K.X K.Y (fun _ _ _ => false) (fun _ _ a b _ => Subsingleton.elim (α := Fin 1) a b)
    (fun _ _ _ _ _ => ⟨rfl, rfl⟩) (fun _ _ _ => 1) (fun _ => 1)
    (fun _ => zero_lt_one) (by refine ⟨1, ?_⟩; intro N d t; norm_num)
    (populationGram K) (GP0182B2b_populationGram_posDef K hK) (by
      simpa only [div_one] using (GP0182B2b_singleSetting K hK).2.2.2.2.2)
  apply WeightedConsistency.inProbability_eventually_eq (unitSampleLaw K) (hf := h)
  filter_upwards [eventually_ge_atTop 2] with N hN
  intro ω
  rw [GP0182B2b_singleWeightedVariance, GP0182B2b_singleWeightedTarget K hK hN]

/-
Adapted from earlier code by P. M. Aronow and Patrick Lopatto.
MIT License

Copyright (c) 2026 P. M. Aronow and Patrick Lopatto

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
/- See NOTICE at the repository root for this adapted section. -/

section GP0182B2b_PairMoments
set_option backward.isDefEq.respectTransparency false

variable {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
variable {ν : Measure Ω} {μ : Measure E} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] in
theorem GP0182B2b_integral_comp_measurePreserving (f : Ω → E)
    (hf : MeasurePreserving f ν μ) (g : E → ℝ) (hg : Measurable g) :
    (∫ x, g (f x) ∂ν) = ∫ y, g y ∂μ := by
  rw [← hf.map_eq]
  exact (integral_map hf.aemeasurable hg.aestronglyMeasurable).symm

omit [IsProbabilityMeasure μ] in
theorem GP0182B2b_pair_measurePreserving (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {i j : ι} (hij : i ≠ j) :
    MeasurePreserving (fun x => (X i x, X j x)) ν (μ.prod μ) := by
  refine ⟨(hX i).measurable.prodMk (hX j).measurable, ?_⟩
  rw [(hind.indepFun hij).map_prod_eq_prod_map_map (hX i).aemeasurable
    (hX j).aemeasurable, (hX i).map_eq, (hX j).map_eq]

theorem GP0182B2b_triple_measurePreserving (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    MeasurePreserving (fun x => ((X i x, X j x), X k x)) ν ((μ.prod μ).prod μ) := by
  refine ⟨((hX i).measurable.prodMk (hX j).measurable).prodMk (hX k).measurable, ?_⟩
  rw [(hind.indepFun_prodMk (fun i => (hX i).measurable) i j k hik hjk).map_prod_eq_prod_map_map
      ((hX i).aemeasurable.prodMk (hX j).aemeasurable) (hX k).aemeasurable,
    (GP0182B2b_pair_measurePreserving X hind hX hij).map_eq, (hX k).map_eq]

theorem GP0182B2b_kernel_pair_memLp (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ))
    {i j : ι} (hij : i ≠ j) : MemLp (fun x => K (X i x, X j x)) 2 ν :=
  hK.comp_measurePreserving (GP0182B2b_pair_measurePreserving X hind hX hij)

theorem GP0182B2b_kernel_pair_integral (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hK : Measurable K) {i j : ι} (hij : i ≠ j) :
    (∫ x, K (X i x, X j x) ∂ν) = ∫ z, K z ∂μ.prod μ :=
  GP0182B2b_integral_comp_measurePreserving _ (GP0182B2b_pair_measurePreserving X hind hX hij) K hK

theorem GP0182B2b_shared_product_integrable {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    Integrable (fun z : (E × E) × E => K z.1 * K (z.1.1, z.2))
      ((μ.prod μ).prod μ) := by
  have h₁ : MemLp (fun z : (E × E) × E => K z.1) 2 ((μ.prod μ).prod μ) :=
    hK.comp_measurePreserving measurePreserving_fst
  have hm : MeasurePreserving (fun z : (E × E) × E => (z.1.1, z.2))
      ((μ.prod μ).prod μ) (μ.prod μ) :=
    measurePreserving_fst.prod (MeasurePreserving.id μ)
  have h₂ : MemLp (fun z : (E × E) × E => K (z.1.1, z.2)) 2 ((μ.prod μ).prod μ) :=
    hK.comp_measurePreserving hm
  exact h₁.integrable_mul h₂

def GP0182B2b_rowIntegral (K : E × E → ℝ) (x : E) : ℝ := ∫ y, K (x, y) ∂μ

theorem GP0182B2b_rowIntegral_measurable {K : E × E → ℝ} (hmK : Measurable K) :
    Measurable (GP0182B2b_rowIntegral (μ := μ) K) :=
  hmK.stronglyMeasurable.integral_prod_right'.measurable

theorem GP0182B2b_row_product_integrable {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    Integrable (fun z : E × E => K z * GP0182B2b_rowIntegral (μ := μ) K z.1) (μ.prod μ) := by
  have hi := (GP0182B2b_shared_product_integrable hK).integral_prod_left
  simpa only [integral_const_mul, GP0182B2b_rowIntegral] using hi

theorem GP0182B2b_rowIntegral_sq_integrable {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    Integrable (fun x => GP0182B2b_rowIntegral (μ := μ) K x ^ 2) μ := by
  have hi := (GP0182B2b_row_product_integrable hK).integral_prod_left
  simpa only [integral_mul_const, GP0182B2b_rowIntegral, pow_two] using hi

theorem GP0182B2b_shared_product_integral {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    (∫ z : (E × E) × E, K z.1 * K (z.1.1, z.2) ∂(μ.prod μ).prod μ) =
      ∫ x, GP0182B2b_rowIntegral (μ := μ) K x ^ 2 ∂μ := by
  rw [integral_prod _ (GP0182B2b_shared_product_integrable hK)]
  simp only [integral_const_mul]
  change (∫ z : E × E, K z * GP0182B2b_rowIntegral (μ := μ) K z.1 ∂μ.prod μ) = _
  rw [integral_prod _ (GP0182B2b_row_product_integrable hK)]
  simp only [integral_mul_const, GP0182B2b_rowIntegral, pow_two]

theorem GP0182B2b_kernel_shared_product_integral (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∫ x, K (X i x, X j x) * K (X i x, X k x) ∂ν) =
      ∫ x, GP0182B2b_rowIntegral (μ := μ) K x ^ 2 ∂μ := by
  have hg : Measurable (fun z : (E × E) × E => K z.1 * K (z.1.1, z.2)) :=
    (hmK.comp measurable_fst).mul (hmK.comp (measurable_fst.fst.prodMk measurable_snd))
  exact (GP0182B2b_integral_comp_measurePreserving _
    (GP0182B2b_triple_measurePreserving X hind hX hij hik hjk) _ hg).trans
    (GP0182B2b_shared_product_integral hK)

theorem GP0182B2b_kernel_disjoint_product_integral (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K)
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    (∫ x, K (X i x, X j x) * K (X k x, X l x) ∂ν) =
      (∫ z, K z ∂μ.prod μ) ^ 2 := by
  have hd := (hind.indepFun_prodMk_prodMk (fun i => (hX i).measurable)
    i j k l hik hil hjk hjl).comp hmK hmK
  have he := hd.integral_fun_mul_eq_mul_integral
    (hmK.comp ((hX i).measurable.prodMk (hX j).measurable)).aestronglyMeasurable
    (hmK.comp ((hX k).measurable.prodMk (hX l).measurable)).aestronglyMeasurable
  simp only [Function.comp_def] at he
  rw [he, GP0182B2b_kernel_pair_integral X hind hX hmK hij, GP0182B2b_kernel_pair_integral X hind hX hmK hkl,
    pow_two]

theorem GP0182B2b_kernel_pair_sq_integral (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) {i j : ι} (hij : i ≠ j) :
    (∫ x, K (X i x, X j x) ^ 2 ∂ν) = ∫ z, K z ^ 2 ∂μ.prod μ :=
  GP0182B2b_kernel_pair_integral X hind hX (hmK.pow_const 2) hij

/-- Exact overlap classification for a symmetric kernel. -/
theorem GP0182B2b_kernel_pair_product_classification [DecidableEq ι] (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    (hsym : ∀ x y, K (x, y) = K (y, x))
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) :
    (∫ x, K (X i x, X j x) * K (X k x, X l x) ∂ν) =
      if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then ∫ z, K z ^ 2 ∂μ.prod μ
      else if i = k ∨ i = l ∨ j = k ∨ j = l then
        ∫ x, GP0182B2b_rowIntegral (μ := μ) K x ^ 2 ∂μ else (∫ z, K z ∂μ.prod μ) ^ 2 := by
  classical
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      simpa only [true_and, true_or, or_true, ite_true, pow_two] using
        GP0182B2b_kernel_pair_sq_integral X hind hX hmK hij
    · have hji : j ≠ i := Ne.symm hij
      simp only [true_and, hjl, and_false, hji, false_or, ite_false, true_or, ite_true]
      exact GP0182B2b_kernel_shared_product_integral X hind hX hmK hK hij hkl hjl
  · by_cases hil : i = l
    · subst l
      by_cases hjk : j = k
      · subst k
        have he : (fun x => K (X i x, X j x) * K (X j x, X i x)) =
            (fun x => K (X i x, X j x) ^ 2) := by
          funext x
          rw [hsym (X j x) (X i x), pow_two]
        rw [he]
        simp only [and_true, or_true, ite_true]
        exact GP0182B2b_kernel_pair_sq_integral X hind hX hmK hij
      · have hki : k ≠ i := hkl
        simp only [hik, false_and, true_and, hjk, or_false, ite_false, true_or,
          false_or, ite_true]
        have he : (fun x => K (X i x, X j x) * K (X k x, X i x)) =
            (fun x => K (X i x, X j x) * K (X i x, X k x)) := by
          funext x
          rw [hsym (X k x) (X i x)]
        rw [he]
        exact GP0182B2b_kernel_shared_product_integral X hind hX hmK hK hij hik hjk
    · by_cases hjk : j = k
      · subst k
        have he : (fun x => K (X i x, X j x) * K (X j x, X l x)) =
            (fun x => K (X j x, X i x) * K (X j x, X l x)) := by
          funext x
          rw [hsym (X i x) (X j x)]
        rw [he]
        simp only [hik, false_and, hil, false_or, true_or, ite_false, ite_true]
        exact GP0182B2b_kernel_shared_product_integral X hind hX hmK hK (Ne.symm hij) hkl hil
      · by_cases hjl : j = l
        · subst l
          have he : (fun x => K (X i x, X j x) * K (X k x, X j x)) =
              (fun x => K (X j x, X i x) * K (X j x, X k x)) := by
            funext x
            rw [hsym (X i x) (X j x), hsym (X k x) (X j x)]
          rw [he]
          simp only [hik, false_and, hil, hjk, false_or, false_and, ite_false,
            or_true, ite_true]
          exact GP0182B2b_kernel_shared_product_integral X hind hX hmK hK (Ne.symm hij)
            (Ne.symm hkl) hik
        · simp only [hik, hil, hjk, hjl, false_and, false_or, ite_false]
          exact GP0182B2b_kernel_disjoint_product_integral X hind hX hmK hij hkl hik hil hjk hjl


end GP0182B2b_PairMoments

theorem GP0182B2b_dyad_product {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ}
    (h : U × U → ℝ) (hm : Measurable h) (hLp : MemLp h 2 (μ.prod μ))
    (hsym : ∀ u v, h (u,v) = h (v,u)) (d f : Dyad N) :
    (∫ ω : Fin N → U, h (ω (firstUnit d), ω (secondUnit d)) *
      h (ω (firstUnit f), ω (secondUnit f)) ∂Measure.pi (fun _ => μ)) =
      if d = f then ∫ uv, h uv ^ 2 ∂μ.prod μ else
      if overlap d f then ∫ u, (GP0182B2b_rowIntegral (μ := μ) h u)^2 ∂μ else
      (∫ uv, h uv ∂μ.prod μ)^2 := by
  classical
  have hc := GP0182B2b_kernel_pair_product_classification
    (fun i : Fin N => fun ω : Fin N → U => ω i)
    (iIndepFun_pi (fun _ => aemeasurable_id))
    (fun i => measurePreserving_eval (fun _ : Fin N => μ) i)
    hm hLp hsym (printed_endpoints_lt d).ne (printed_endpoints_lt f).ne
  have heq : ((firstUnit d = firstUnit f ∧ secondUnit d = secondUnit f) ∨
      (firstUnit d = secondUnit f ∧ secondUnit d = firstUnit f)) ↔ d = f := by
    constructor
    · rintro (⟨h₁,h₂⟩ | ⟨h₁,h₂⟩)
      · apply Subtype.ext
        change members d = members f
        rw [printed_members_endpoints, printed_members_endpoints, h₁, h₂]
      · have hlt := printed_endpoints_lt d
        rw [h₁, h₂] at hlt
        exact False.elim ((not_lt_of_ge (printed_endpoints_lt f).le) hlt)
    · intro hdf
      subst f
      exact Or.inl ⟨rfl,rfl⟩
  have ho : overlap d f ↔ firstUnit d = firstUnit f ∨ firstUnit d = secondUnit f ∨
      secondUnit d = firstUnit f ∨ secondUnit d = secondUnit f := by
    simp only [overlap, printed_members_endpoints, Finset.Nonempty, Finset.mem_inter,
      Finset.mem_insert, Finset.mem_singleton]
    aesop
  simpa only [heq, ← ho] using hc

theorem GP0182B2b_dyad_second {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ} (hN : 2 ≤ N)
    (h : U × U → ℝ) (hm : Measurable h) (hLp : MemLp h 2 (μ.prod μ))
    (hsym : ∀ u v, h (u,v) = h (v,u)) (hmean : (∫ uv, h uv ∂μ.prod μ) = 0) :
    (∫ ω : Fin N → U, (∑ d : Dyad N,
      h (ω (firstUnit d), ω (secondUnit d)))^2 ∂Measure.pi (fun _ => μ)) =
      Dreal N * (∫ uv, h uv^2 ∂μ.prod μ) +
      (N : ℝ) * ((N : ℝ)-1) * ((N : ℝ)-2) *
        (∫ u, (GP0182B2b_rowIntegral (μ := μ) h u)^2 ∂μ) := by
  classical
  let A := ∫ uv, h uv^2 ∂μ.prod μ
  let B := ∫ u, (GP0182B2b_rowIntegral (μ := μ) h u)^2 ∂μ
  have hp (d : Dyad N) : MemLp
      (fun ω : Fin N → U => h (ω (firstUnit d), ω (secondUnit d))) 2
      (Measure.pi (fun _ => μ)) :=
    GP0182B2b_kernel_pair_memLp _ (iIndepFun_pi (fun _ => aemeasurable_id))
      (fun i => measurePreserving_eval (fun _ : Fin N => μ) i)
      hLp (printed_endpoints_lt d).ne
  have ht (d f : Dyad N) : Integrable
      (fun ω : Fin N → U => h (ω (firstUnit d), ω (secondUnit d)) *
        h (ω (firstUnit f), ω (secondUnit f))) (Measure.pi (fun _ => μ)) :=
    (hp d).integrable_mul (hp f)
  simp only [pow_two, Finset.sum_mul_sum]
  rw [integral_finsetSum _ (fun d _ => integrable_finsetSum _ (fun f _ => ht d f))]
  simp_rw [integral_finsetSum _ (fun f _ => ht _ f)]
  have hterm (d f : Dyad N) : (if d = f then A else if overlap d f then B else 0) =
      (if f = d then A else 0) + (if f ∈ neighbors d then B else 0) := by
    by_cases hfd : f = d
    · subst f
      simp only [ite_true, neighbors, Finset.mem_filter, Finset.mem_univ,
        ne_eq, not_true_eq_false, false_and, and_false, ite_false, add_zero]
    · rw [if_neg (Ne.symm hfd), if_neg hfd, zero_add]
      have hmem : f ∈ neighbors d ↔ overlap d f := by
        simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨And.right, fun hh => ⟨hfd, hh⟩⟩
      by_cases ho : overlap d f
      · rw [if_pos ho, if_pos (hmem.mpr ho)]
      · rw [if_neg ho, if_neg (fun hh => ho (hmem.mp hh))]
  have hinner (d : Dyad N) : (∑ f : Dyad N,
      if d = f then A else if overlap d f then B else 0) = A + ((neighbors d).card : ℝ)*B := by
    simp_rw [hterm, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have he : univ.filter (fun f : Dyad N => f ∈ neighbors d) = neighbors d := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← Finset.sum_filter, he, Finset.sum_const, nsmul_eq_mul]
  have hc : (∑ d : Dyad N, ((neighbors d).card : ℝ)) =
      (N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2) := by
    rw [← Nat.cast_sum, (dyad_counts_proof N hN).2.2.1]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ N),
      Nat.cast_sub hN]
    norm_num
  simp_rw [← pow_two]
  simp_rw [GP0182B2b_dyad_product μ h hm hLp hsym, hmean, zero_pow (by decide : 2 ≠ 0)]
  change (∑ d : Dyad N, ∑ f : Dyad N, if d = f then A else if overlap d f then B else 0) = _
  simp_rw [hinner, Finset.sum_add_distrib]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, printed_card_real,
    ← Finset.sum_mul, hc]

theorem GP0182B2b_score_measurable {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (a : Fin k) :
    Measurable (fun uv : U × U => populationScore K uv.1 uv.2 a) := by
  have hX (b : Fin k) := (measurable_pi_apply b).comp hK.2.1
  simp only [populationScore, score, populationResidual, Pi.smul_apply, smul_eq_mul, dot]
  exact (hK.2.2.1.sub (Finset.measurable_fun_sum _
    (fun b _ => (hX b).mul_const _))).mul (hX a)

theorem GP0182B2b_score_mean {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    meanVec (K.μ.prod K.μ) (fun uv => populationScore K uv.1 uv.2) = 0 := by
  let β := populationBeta K
  have hxy := (corrected_pair_products K hK).2
  have hxx (a b : Fin k) := ((corrected_pair_products K hK).1 a b).mul_const (β b)
  have hid (a : Fin k) (uv : U × U) : populationScore K uv.1 uv.2 a =
      K.Y uv.1 uv.2 * K.X uv.1 uv.2 a -
        ∑ b, (K.X uv.1 uv.2 a * K.X uv.1 uv.2 b) * β b := by
    simp only [populationScore, populationResidual, score, Pi.smul_apply, smul_eq_mul,
      dot, sub_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have he : (populationGram K).mulVec β =
      meanVec (K.μ.prod K.μ) (fun uv => score (K.X uv.1 uv.2) (K.Y uv.1 uv.2)) := by
    unfold β populationBeta
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hK.2.2.2.2.2.2), Matrix.one_mulVec]
  ext a
  change (∫ uv, populationScore K uv.1 uv.2 a ∂K.μ.prod K.μ) = 0
  simp_rw [hid]
  rw [integral_sub (hxy a) (integrable_finsetSum _ (fun b _ => hxx a b)),
    integral_finsetSum _ (fun b _ => hxx a b)]
  simp_rw [integral_mul_const]
  exact sub_eq_zero.mpr (congrFun he a).symm

theorem GP0182B2b_score_bound {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᵐ uv ∂K.μ.prod K.μ,
      ∀ a, |populationScore K uv.1 uv.2 a| ≤ L := by
  obtain ⟨C, hC, hb⟩ := hK.2.2.2.2.1
  let β := populationBeta K
  let Ce := C + (k : ℝ)*C*‖β‖
  have hCe : 0 ≤ Ce := by dsimp [Ce]; positivity
  refine ⟨Ce*C, mul_nonneg hCe hC, ?_⟩
  filter_upwards [hb] with uv huv
  have hcoord (a : Fin k) : |K.X uv.1 uv.2 a| ≤ C :=
    (norm_le_pi_norm (K.X uv.1 uv.2) a).trans huv.1
  have hd : |dot (K.X uv.1 uv.2) β| ≤ (k : ℝ)*C*‖β‖ := by
    calc
      _ ≤ ∑ a : Fin k, |K.X uv.1 uv.2 a * β a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin k, C*‖β‖ := Finset.sum_le_sum (fun a _ => by
        rw [abs_mul]
        exact mul_le_mul (hcoord a) (norm_le_pi_norm β a) (abs_nonneg _) hC)
      _ = _ := by simp [mul_assoc]
  have hr : |populationResidual K uv.1 uv.2| ≤ Ce := by
    exact (abs_sub _ _).trans (add_le_add huv.2 hd)
  intro a
  exact (abs_mul _ _).trans_le (mul_le_mul hr (hcoord a) (abs_nonneg _) hCe)

theorem GP0182B2b_score_memLp {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (a : Fin k) (p : ℝ≥0∞) :
    MemLp (fun uv : U × U => populationScore K uv.1 uv.2 a) p (K.μ.prod K.μ) := by
  let GP0182B2b_unitProb : IsProbabilityMeasure K.μ := hK.1
  obtain ⟨L, hL, hb⟩ := GP0182B2b_score_bound K hK
  exact MemLp.of_bound (GP0182B2b_score_measurable K hK a).aestronglyMeasurable L
    (hb.mono (fun uv huv => huv a))


def GP0182B2b_product {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] : Measure (ℕ → U) :=
  Measure.infinitePi (fun _ : ℕ => μ)

instance GP0182B2b_product_probability {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] : IsProbabilityMeasure (GP0182B2b_product μ) := by
  unfold GP0182B2b_product
  infer_instance

def GP0182B2b_prefix {U : Type*} (N : ℕ) (ω : ℕ → U) : Fin N → U := fun i => ω i

theorem GP0182B2b_prefix_measurable {U : Type*} [MeasurableSpace U] (N : ℕ) :
    Measurable (GP0182B2b_prefix (U := U) N) := by
  exact measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)

theorem GP0182B2b_prefix_preserving {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] (N : ℕ) :
    MeasurePreserving (GP0182B2b_prefix (U := U) N) (GP0182B2b_product μ)
      (Measure.pi (fun _ : Fin N => μ)) := by
  refine ⟨GP0182B2b_prefix_measurable N, ?_⟩
  change (Measure.infinitePi (fun _ : ℕ => μ)).map
    (fun ω (i : Fin N) => ω i.val) = _
  rw [Measure.map_infinitePi_infinitePi_of_inj (f := fun i : Fin N => i.val)
    Fin.val_injective, Measure.infinitePi_eq_pi]

theorem GP0182B2b_prefix_integral {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] (N : ℕ) (f : (Fin N → U) → ℝ)
    (hf : Measurable f) :
    (∫ ω, f (GP0182B2b_prefix N ω) ∂GP0182B2b_product μ) =
      ∫ ω, f ω ∂Measure.pi (fun _ : Fin N => μ) := by
  exact GP0182B2b_integral_comp_measurePreserving _
    (GP0182B2b_prefix_preserving μ N) f hf

theorem GP0182B2b_prefix_measure {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] (N : ℕ)
    (A : Set (Fin N → U)) (hA : MeasurableSet A) :
    (GP0182B2b_product μ) (GP0182B2b_prefix N ⁻¹' A) =
      (Measure.pi (fun _ : Fin N => μ)) A := by
  exact (GP0182B2b_prefix_preserving μ N).measure_preimage hA.nullMeasurableSet

theorem GP0182B2b_prefix_inProbability {U E : Type*} [MeasurableSpace U]
    [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    (μ : Measure U) [IsProbabilityMeasure μ]
    (f : ∀ N : ℕ, (Fin N → U) → E) (hm : ∀ N, Measurable (f N))
    (hf : inProbability (fun N => Measure.pi (fun _ : Fin N => μ)) f) :
    TendstoInMeasure (GP0182B2b_product μ) (fun N ω => f N (GP0182B2b_prefix N ω))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have he (N : ℕ) :
      (GP0182B2b_product μ).real {ω | ε ≤ ‖f N (GP0182B2b_prefix N ω) - 0‖} =
        ((Measure.pi (fun _ : Fin N => μ)) {ω | ε ≤ ‖f N ω‖}).toReal := by
    simp only [sub_zero, Measure.real]
    rw [← GP0182B2b_prefix_measure μ N {ω | ε ≤ ‖f N ω‖}
      (measurableSet_le measurable_const (hm N).norm)]
    rfl
  simpa only [he] using hf ε hε

theorem GP0182B2b_iid_ident {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] (f : U → ℝ) (hm : Measurable f) (i : ℕ) :
    IdentDistrib (fun ω : ℕ → U => f (ω i)) f (GP0182B2b_product μ) μ := by
  refine ⟨(hm.comp (measurable_pi_apply i)).aemeasurable, hm.aemeasurable, ?_⟩
  change (GP0182B2b_product μ).map (f ∘ (fun ω : ℕ → U => ω i)) = _
  rw [← Measure.map_map hm (measurable_pi_apply i)]
  congr 1
  exact Measure.infinitePi_map_eval _ _

theorem GP0182B2b_iid_clt {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] (f : U → ℝ) (hm : Measurable f)
    (hLp : MemLp f 2 μ) (hmean : (∫ u, f u ∂μ) = 0) :
    TendstoInDistribution
      (fun (N : ℕ) (ω : ℕ → U) => (Real.sqrt N)⁻¹ * ∑ i : Fin N, f (ω i)) atTop
      id (fun _ => GP0182B2b_product μ) (gaussianReal 0 (ProbabilityTheory.variance f μ).toNNReal) := by
  have hvar : ProbabilityTheory.variance (fun ω : ℕ → U => f (ω 0))
      (GP0182B2b_product μ) = ProbabilityTheory.variance f μ :=
    (GP0182B2b_iid_ident μ f hm 0).variance_eq
  have h0 : (∫ ω : ℕ → U, f (ω 0) ∂GP0182B2b_product μ) = 0 := by
    rw [(GP0182B2b_iid_ident μ f hm 0).integral_eq, hmean]
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun i (ω : ℕ → U) => f (ω i)) (Y := id)
    (P' := gaussianReal 0 (ProbabilityTheory.variance f μ).toNNReal)
    (by rw [hvar]; exact ⟨measurable_id.aemeasurable, Measure.map_id⟩)
    ((GP0182B2b_iid_ident μ f hm 0).memLp_iff.mpr hLp)
    (iIndepFun_infinitePi (P := fun _ : ℕ => μ) (fun _ => hm))
    (fun i => (GP0182B2b_iid_ident μ f hm i).trans (GP0182B2b_iid_ident μ f hm 0).symm)
  simpa only [← Fin.sum_univ_eq_sum_range, h0, mul_zero, sub_zero] using h


def GP0182B2b_dyadAverage {U : Type*} (h : U × U → ℝ) {N : ℕ} (ω : Fin N → U) : ℝ :=
  (Dreal N)⁻¹ * ∑ d : Dyad N, h (ω (firstUnit d), ω (secondUnit d))

theorem GP0182B2b_dyadAverage_measurable {U : Type*} [MeasurableSpace U]
    (h : U × U → ℝ) (hm : Measurable h) (N : ℕ) :
    Measurable (fun ω : Fin N → U => GP0182B2b_dyadAverage h ω) := by
  exact (Finset.measurable_fun_sum _ (fun d _ =>
    hm.comp ((measurable_pi_apply (firstUnit d)).prodMk
      (measurable_pi_apply (secondUnit d))))).const_mul _

theorem GP0182B2b_NdivD_limit :
    Tendsto (fun N : ℕ => (N : ℝ)/Dreal N) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => 2 * ((N : ℝ)-1)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (by simpa only [sub_eq_add_neg] using
        (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop))).const_mul (2 : ℝ)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  dsimp [Dreal]
  field_simp
  <;> ring

theorem GP0182B2b_square_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hLp : MemLp f 2 μ)
    (ε : ℝ) (hε : 0 < ε) :
    (μ {ω | ε ≤ ‖f ω‖}).toReal ≤ (∫ ω, (f ω)^2 ∂μ) / ε^2 := by
  have hs : {ω | ε ≤ ‖f ω‖} ⊆ {ω | ε^2 ≤ (f ω)^2} := by
    intro ω hω
    change ε ≤ |f ω| at hω
    change ε^2 ≤ (f ω)^2
    nlinarith [sq_abs (f ω)]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  calc
    _ ≤ ε^2 * (μ {ω | ε^2 ≤ (f ω)^2}).toReal := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left
        (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hs)) (sq_nonneg ε)
    _ ≤ _ := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (f ω))) hLp.integrable_sq (ε^2)

theorem GP0182B2b_degenerate_null {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ]
    (r : U × U → ℝ) (hm : Measurable r) (hLp : MemLp r 2 (μ.prod μ))
    (hsym : ∀ u v, r (u,v) = r (v,u))
    (hmean : (∫ uv, r uv ∂μ.prod μ) = 0)
    (hrow : ∀ᵐ u ∂μ, GP0182B2b_rowIntegral (μ := μ) r u = 0) :
    inProbability (fun N => Measure.pi (fun _ : Fin N => μ))
      (fun N ω => Real.sqrt N * GP0182B2b_dyadAverage r ω) := by
  have hB : (∫ u, (GP0182B2b_rowIntegral (μ := μ) r u)^2 ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    exact hrow.mono (fun u hu => by
      change (GP0182B2b_rowIntegral (μ := μ) r u)^2 = 0
      rw [hu]
      exact zero_pow (by decide))
  have hp (N : ℕ) : MemLp
      (fun ω : Fin N → U => Real.sqrt N * GP0182B2b_dyadAverage r ω) 2
      (Measure.pi (fun _ => μ)) := by
    apply MemLp.const_mul
    apply MemLp.const_mul
    exact memLp_finsetSum _ (fun d _ => GP0182B2b_kernel_pair_memLp _
      (iIndepFun_pi (fun _ => aemeasurable_id))
      (fun i => measurePreserving_eval (fun _ : Fin N => μ) i)
      hLp (printed_endpoints_lt d).ne)
  have hsecond (N : ℕ) (hN : 2 ≤ N) :
      (∫ ω : Fin N → U, (Real.sqrt N * GP0182B2b_dyadAverage r ω)^2
        ∂Measure.pi (fun _ => μ)) = (N : ℝ)/Dreal N * (∫ uv, r uv^2 ∂μ.prod μ) := by
    simp only [GP0182B2b_dyadAverage, mul_pow]
    rw [integral_const_mul, integral_const_mul,
      GP0182B2b_dyad_second μ hN r hm hLp hsym hmean, hB, mul_zero, add_zero,
      Real.sq_sqrt (Nat.cast_nonneg N)]
    field_simp [(printed_Dpos hN).ne']
    <;> ring
  intro ε hε
  have hlim : Tendsto (fun N : ℕ =>
      ((N : ℝ)/Dreal N * (∫ uv, r uv^2 ∂μ.prod μ))/ε^2) atTop (𝓝 0) := by
    simpa using (GP0182B2b_NdivD_limit.mul_const _).div_const (ε^2)
  apply squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) _ hlim
  filter_upwards [eventually_ge_atTop 2] with N hN
  have h := GP0182B2b_square_probability (Measure.pi (fun _ : Fin N => μ)) _ (hp N) ε hε
  rw [hsecond N hN] at h
  exact h

theorem GP0182B2b_dyad_clt {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ]
    (h : U × U → ℝ) (hm : Measurable h) (hLp : MemLp h 2 (μ.prod μ))
    (hsym : ∀ u v, h (u,v) = h (v,u)) (hmean : (∫ uv, h uv ∂μ.prod μ) = 0) :
    TendstoInDistribution
      (fun (N : ℕ) (ω : ℕ → U) =>
        Real.sqrt N * GP0182B2b_dyadAverage h (GP0182B2b_prefix N ω)) atTop
      id (fun _ => GP0182B2b_product μ)
      (gaussianReal 0 (4 * ∫ u, (GP0182B2b_rowIntegral (μ := μ) h u)^2 ∂μ).toNNReal) := by
  let g := GP0182B2b_rowIntegral (μ := μ) h
  have hg : Measurable g := GP0182B2b_rowIntegral_measurable hm
  have hgLp : MemLp g 2 μ :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr
      (GP0182B2b_rowIntegral_sq_integrable hLp)
  have hgmean : (∫ u, g u ∂μ) = 0 := by
    change (∫ u, ∫ v, h (u,v) ∂μ ∂μ) = 0
    rw [← integral_prod _ (hLp.integrable one_le_two)]
    exact hmean
  let r : U × U → ℝ := fun uv => h uv - g uv.1 - g uv.2
  have hr : Measurable r := (hm.sub (hg.comp measurable_fst)).sub (hg.comp measurable_snd)
  have hrLp : MemLp r 2 (μ.prod μ) :=
    (hLp.sub (hgLp.comp_measurePreserving measurePreserving_fst)).sub
      (hgLp.comp_measurePreserving measurePreserving_snd)
  have hrsym : ∀ u v, r (u,v) = r (v,u) := by
    intro u v
    dsimp [r]
    rw [hsym u v]
    ring
  have hrrow : ∀ᵐ u ∂μ, GP0182B2b_rowIntegral (μ := μ) r u = 0 := by
    filter_upwards [(hLp.integrable one_le_two).prod_right_ae] with u hu
    change (∫ v, h (u,v) - g u - g v ∂μ) = 0
    have his : Integrable (fun v => h (u,v) - g u) μ := hu.sub (integrable_const (g u))
    rw [integral_sub his (hgLp.integrable one_le_two),
      integral_sub hu (integrable_const (g u)), integral_const, probReal_univ, one_smul, hgmean]
    change g u - g u - 0 = 0
    ring
  have hrmean : (∫ uv, r uv ∂μ.prod μ) = 0 := by
    rw [integral_prod _ (hrLp.integrable one_le_two)]
    exact integral_eq_zero_of_ae hrrow
  have hrem := GP0182B2b_degenerate_null μ r hr hrLp hrsym hrmean hrrow
  have hidentity (N : ℕ) (hN : 2 ≤ N) (ω : Fin N → U) :
      Real.sqrt N * GP0182B2b_dyadAverage h ω -
        (Real.sqrt N)⁻¹ * ∑ i : Fin N, (2 * g (ω i)) =
          Real.sqrt N * GP0182B2b_dyadAverage r ω := by
    have hsum := printed_pair_add (fun i => g (ω i))
    simp only [Finset.sum_add_distrib] at hsum
    have hd : (∑ d : Dyad N, h (ω (firstUnit d), ω (secondUnit d))) =
        ((N : ℝ)-1) * ∑ i : Fin N, g (ω i) +
          ∑ d : Dyad N, r (ω (firstUnit d), ω (secondUnit d)) := by
      simp only [r, Finset.sum_sub_distrib]
      linarith
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have hn1 : (N : ℝ)-1 ≠ 0 := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hs : Real.sqrt (N : ℝ) ≠ 0 := by
      exact (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < N)).ne'
    have hcoef : Real.sqrt N * (Dreal N)⁻¹ * ((N : ℝ)-1) =
        (Real.sqrt N)⁻¹ * 2 := by
      dsimp [Dreal]
      field_simp
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
    simp only [GP0182B2b_dyadAverage, hd, ← Finset.mul_sum]
    calc
      _ = (Real.sqrt N * (Dreal N)⁻¹ * ((N : ℝ)-1) - (Real.sqrt N)⁻¹*2) *
          (∑ i : Fin N, g (ω i)) +
          Real.sqrt N * (Dreal N)⁻¹ * (∑ d : Dyad N, r (ω (firstUnit d), ω (secondUnit d))) := by ring
      _ = _ := by rw [hcoef, sub_self, zero_mul, zero_add]; ring
  let T : ∀ N : ℕ, (Fin N → U) → ℝ := fun N ω =>
    Real.sqrt N * GP0182B2b_dyadAverage h ω -
      (Real.sqrt N)⁻¹ * ∑ i : Fin N, (2 * g (ω i))
  have hTm (N : ℕ) : Measurable (T N) :=
    ((GP0182B2b_dyadAverage_measurable h hm N).const_mul _).sub
      ((Finset.measurable_fun_sum _ (fun i _ => (hg.comp (measurable_pi_apply i)).const_mul 2)).const_mul _)
  have hT : inProbability (fun N => Measure.pi (fun _ : Fin N => μ)) T := by
    apply WeightedConsistency.inProbability_eventually_eq _ (hf := hrem)
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact fun ω => (hidentity N hN ω).symm
  have hdist := GP0182B2b_prefix_inProbability μ T hTm hT
  have hvar : ProbabilityTheory.variance (fun u => 2*g u) μ = 4 * ∫ u, (g u)^2 ∂μ := by
    rw [variance_const_mul, variance_eq_sub hgLp, hgmean]
    norm_num
  have hCLT := GP0182B2b_iid_clt μ (fun u => 2*g u) (hg.const_mul 2) (hgLp.const_mul 2)
    (by rw [integral_const_mul, hgmean, mul_zero])
  rw [hvar] at hCLT
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ _ hCLT hdist
    (fun N => (((GP0182B2b_dyadAverage_measurable h hm N).comp
      (GP0182B2b_prefix_measurable N)).const_mul _).aemeasurable)

theorem GP0182B2b_prefix_null_iff {U E : Type*} [MeasurableSpace U]
    [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    (μ : Measure U) [IsProbabilityMeasure μ]
    (f : ∀ N : ℕ, (Fin N → U) → E) (hm : ∀ N, Measurable (f N)) :
    inProbability (fun N => Measure.pi (fun _ : Fin N => μ)) f ↔
      TendstoInMeasure (GP0182B2b_product μ) (fun N ω => f N (GP0182B2b_prefix N ω))
        atTop (fun _ => 0) := by
  refine ⟨GP0182B2b_prefix_inProbability μ f hm, ?_⟩
  intro hf ε hε
  have h := (tendstoInMeasure_iff_measureReal_norm.mp hf) ε hε
  have he (N : ℕ) :
      (GP0182B2b_product μ).real {ω | ε ≤ ‖f N (GP0182B2b_prefix N ω) - 0‖} =
        ((Measure.pi (fun _ : Fin N => μ)) {ω | ε ≤ ‖f N ω‖}).toReal := by
    simp only [sub_zero, Measure.real]
    rw [← GP0182B2b_prefix_measure μ N {ω | ε ≤ ‖f N ω‖}
      (measurableSet_le measurable_const (hm N).norm)]
    rfl
  simpa only [he] using h

theorem GP0182B2b_distribution_zero_inMeasure
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure Ω') [IsProbabilityMeasure ν] (X : ℕ → Ω → ℝ)
    (hX : TendstoInDistribution X atTop (fun _ : Ω' => (0 : ℝ)) (fun _ => P) ν) :
    TendstoInMeasure P X atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  let A : Set ℝ := (Set.Ioo (-ε) ε)ᶜ
  have h0 : (0 : ℝ) ∉ frontier A := by
    rw [show frontier A = {-ε, ε} from
      (frontier_compl (Set.Ioo (-ε) ε)).trans (frontier_Ioo (by linarith))]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (hh | hh) <;> linarith
  have hfront : (ν.map (fun _ : Ω' => (0 : ℝ))) (frontier A) = 0 := by
    simp only [Measure.map_const, measure_univ, one_smul, Measure.dirac_apply,
      Set.indicator_of_notMem h0]
  have hz : (ν.map (fun _ : Ω' => (0 : ℝ))) A = 0 := by
    have hA0 : (0 : ℝ) ∉ A := by
      change ¬ (0 : ℝ) ∈ (Set.Ioo (-ε) ε)ᶜ
      simpa only [Set.mem_compl_iff, Set.mem_Ioo, not_not] using
        (show -ε < (0 : ℝ) ∧ (0 : ℝ) < ε by constructor <;> linarith)
    simp only [Measure.map_const, measure_univ, one_smul, Measure.dirac_apply,
      Set.indicator_of_notMem hA0]
  have hmass := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hX.tendsto hfront
  change Tendsto (fun N => (P.map (X N)) A) atTop
    (𝓝 ((ν.map (fun _ : Ω' => (0 : ℝ))) A)) at hmass
  rw [hz] at hmass
  have hreal := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp hmass
  have he (N : ℕ) : ((P.map (X N)) A).toReal = P.real {ω | ε ≤ ‖X N ω - 0‖} := by
    change ((P.map (X N)) A).toReal = (P {ω | ε ≤ ‖X N ω - 0‖}).toReal
    rw [Measure.map_apply_of_aemeasurable (hX.forall_aemeasurable N) measurableSet_Ioo.compl]
    congr 2
    ext ω
    simp only [A, Set.mem_preimage, Set.mem_compl_iff, Set.mem_Ioo,
      sub_zero, Real.norm_eq_abs, ← abs_lt, not_lt, Set.mem_setOf_eq]
  change Tendsto (fun N => ((P.map (X N)) A).toReal) atTop (𝓝 0) at hreal
  simpa only [he] using hreal

theorem GP0182B2b_measurable_Gram {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (N : ℕ) :
    Measurable (fun ω : Fin N → U => sampleGram (design K ω)) := by
  have hp (d : Dyad N) : Measurable (fun ω : Fin N → U =>
      (ω (firstUnit d), ω (secondUnit d))) :=
    (measurable_pi_apply (firstUnit d)).prodMk (measurable_pi_apply (secondUnit d))
  have hX (d : Dyad N) (a : Fin k) :
      Measurable (fun ω : Fin N → U => design K ω d a) := by
    simpa only [Function.comp_def, design] using
      (measurable_pi_apply a).comp (hK.2.1.comp (hp d))
  apply measurable_pi_lambda
  intro a
  apply measurable_pi_lambda
  intro b
  simp only [sampleGram, Matrix.sum_apply, outer]
  exact Finset.measurable_fun_sum _ (fun d _ => (hX d a).mul (hX d b))

theorem GP0182B2b_Gram_null {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    inProbability (unitSampleLaw K) (fun N ω =>
      (Dreal N)⁻¹ • sampleGram (design K ω) - populationGram K) := by
  let GP0182B2b_unitProb : IsProbabilityMeasure K.μ := hK.1
  let GP0182B2b_sampleProb (N : ℕ) : IsProbabilityMeasure (unitSampleLaw K N) := by
    unfold unitSampleLaw
    infer_instance
  have hreg := WeightedConsistency.m0_proof WeightedConsistency.g1_proof
    (singleRecord K) (GP0182B2b_singleStanding K hK)
  have h := WeightedConsistency.m5_proof WeightedConsistency.g3_proof
    WeightedConsistency.g4_proof WeightedConsistency.g5_proof
    (singleRecord K) K.X K.Y (fun _ _ _ => false) (fun _ _ _ => 1) 1 (populationGram K)
    (GP0182B2b_singleSetting K hK) hreg
  apply WeightedConsistency.inProbability_eventually_eq (unitSampleLaw K) (hf := h)
  filter_upwards [eventually_ge_atTop 2] with N hN ω
  change (Dreal N)⁻¹ • recordWeightedGram (singleRecord K) (fun _ _ => 1) ω -
    recordWeightedH (singleRecord K) (fun _ _ => 1) = _
  rw [GP0182B2b_singleWeightedGram, GP0182B2b_singleWeightedH K hK hN]

theorem GP0182B2b_inverse_Gram_null {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    inProbability (unitSampleLaw K) (fun N ω =>
      ((Dreal N)⁻¹ • sampleGram (design K ω))⁻¹ - (populationGram K)⁻¹) := by
  let GP0182B2b_unitProb : IsProbabilityMeasure K.μ := hK.1
  let GP0182B2b_sampleProb (N : ℕ) : IsProbabilityMeasure (unitSampleLaw K N) := by
    unfold unitSampleLaw
    infer_instance
  exact (WeightedConsistency.g7_proof (populationGram K) hK.2.2.2.2.2.2).2
    (unitSampleLaw K) (fun N ω => (Dreal N)⁻¹ • sampleGram (design K ω))
    (GP0182B2b_Gram_null K hK)

theorem GP0182B2b_singular_probability {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    Tendsto (fun N : ℕ => (unitSampleLaw K N {ω |
      (((Dreal N)⁻¹ • sampleGram (design K ω))).det = 0}).toReal) atTop (𝓝 0) := by
  let GP0182B2b_unitProb : IsProbabilityMeasure K.μ := hK.1
  let GP0182B2b_sampleProb (N : ℕ) : IsProbabilityMeasure (unitSampleLaw K N) := by
    unfold unitSampleLaw
    infer_instance
  have hdet := WeightedConsistency.inProbability_continuousAt (unitSampleLaw K)
    (continuous_id.matrix_det.continuousAt (x := populationGram K)) (GP0182B2b_Gram_null K hK)
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _
    (hdet |(populationGram K).det| (abs_pos.mpr hK.2.2.2.2.2.2))
  intro N
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro ω hω
  change |(populationGram K).det| ≤
    ‖((Dreal N)⁻¹ • sampleGram (design K ω)).det - (populationGram K).det‖
  rw [hω, zero_sub, norm_neg, Real.norm_eq_abs]

theorem GP0182B2b_dot_smul {k : ℕ} (c x : Vec k) (r : ℝ) :
    dot c (r • x) = r * dot c x := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem GP0182B2b_dot_sub {k : ℕ} (c x y : Vec k) :
    dot c (x-y) = dot c x - dot c y := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem GP0182B2b_dot_mulVec {k : ℕ} (c x : Vec k) (P : Mat k) :
    dot c (P.mulVec x) = dot (P.transpose.mulVec c) x := by
  simp only [dot, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem GP0182B2b_quad_smul {k : ℕ} (c : Vec k) (P : Mat k) (r : ℝ) :
    dot c ((r • P).mulVec c) = r * dot c (P.mulVec c) := by
  rw [Matrix.smul_mulVec, GP0182B2b_dot_smul]

theorem GP0182B2b_quad_sub {k : ℕ} (c : Vec k) (P Q : Mat k) :
    dot c ((P-Q).mulVec c) = dot c (P.mulVec c) - dot c (Q.mulVec c) := by
  rw [Matrix.sub_mulVec, GP0182B2b_dot_sub]

theorem GP0182B2b_quad_sandwich {k : ℕ} (c : Vec k) (P Q : Mat k)
    (hP : P.transpose = P) :
    dot c ((sandwich P Q).mulVec c) = dot (P.mulVec c) (Q.mulVec (P.mulVec c)) := by
  rw [sandwich, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    GP0182B2b_dot_mulVec, hP]

theorem GP0182B2b_inverse_symmetric {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    ((populationGram K)⁻¹).transpose = (populationGram K)⁻¹ := by
  have h := (GP0182B2b_populationGram_posDef K hK).isHermitian.inv
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem GP0182B2b_score_symmetric {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (u v : U) :
    populationScore K u v = populationScore K v u := by
  simp only [populationScore, populationResidual, (hK.2.2.2.1 u v).1,
    (hK.2.2.2.1 u v).2]

theorem GP0182B2b_contrast_score {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (a : Vec k) :
    Measurable (fun uv : U × U => dot a (populationScore K uv.1 uv.2)) ∧
    MemLp (fun uv : U × U => dot a (populationScore K uv.1 uv.2)) 2 (K.μ.prod K.μ) ∧
    (∀ u v, dot a (populationScore K u v) = dot a (populationScore K v u)) ∧
    (∫ uv : U × U, dot a (populationScore K uv.1 uv.2) ∂K.μ.prod K.μ) = 0 := by
  let GP0182B2b_unitProb : IsProbabilityMeasure K.μ := hK.1
  have hi (b : Fin k) := (GP0182B2b_score_memLp K hK b 2).const_mul (a b)
  refine ⟨Finset.measurable_fun_sum _ (fun b _ =>
    (GP0182B2b_score_measurable K hK b).const_mul _),
    memLp_finsetSum _ (fun b _ => hi b), ?_, ?_⟩
  · intro u v
    rw [GP0182B2b_score_symmetric K hK u v]
  · simp only [dot]
    rw [integral_finsetSum _ (fun b _ => (hi b).integrable one_le_two)]
    simp_rw [integral_const_mul]
    have hm (b : Fin k) : (∫ uv, populationScore K uv.1 uv.2 b ∂K.μ.prod K.μ) = 0 :=
      congrFun (GP0182B2b_score_mean K hK) b
    simp only [hm, mul_zero, Finset.sum_const_zero]

theorem GP0182B2b_projection_memLp {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (b : Fin k) :
    Measurable (fun u => projection K u b) ∧ MemLp (fun u => projection K u b) 2 K.μ := by
  let GP0182B2b_unitProb : IsProbabilityMeasure K.μ := hK.1
  have hm := GP0182B2b_rowIntegral_measurable (μ := K.μ) (GP0182B2b_score_measurable K hK b)
  refine ⟨hm, (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr ?_⟩
  exact GP0182B2b_rowIntegral_sq_integrable (GP0182B2b_score_memLp K hK b 2)

theorem GP0182B2b_contrast_projection {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (a : Vec k) :
    GP0182B2b_rowIntegral (μ := K.μ)
      (fun uv : U × U => dot a (populationScore K uv.1 uv.2)) =ᵐ[K.μ]
        fun u => dot a (projection K u) := by
  let GP0182B2b_unitProb : IsProbabilityMeasure K.μ := hK.1
  filter_upwards [ae_all_iff.mpr (fun b : Fin k =>
    ((GP0182B2b_score_memLp K hK b 2).integrable one_le_two).prod_right_ae)] with u hu
  change (∫ v, ∑ b, a b * populationScore K u v b ∂K.μ) = _
  rw [integral_finsetSum _ (fun b _ => (hu b).const_mul _)]
  simp only [integral_const_mul]
  rfl

theorem GP0182B2b_contrast_variance {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (c : Vec k) :
    4 * (∫ u, (GP0182B2b_rowIntegral (μ := K.μ)
      (fun uv : U × U => dot ((populationGram K)⁻¹.mulVec c)
        (populationScore K uv.1 uv.2)) u)^2 ∂K.μ) =
      dot c ((limitingTarget K).mulVec c) := by
  let a := (populationGram K)⁻¹.mulVec c
  have he := GP0182B2b_contrast_projection K hK a
  rw [integral_congr_ae (he.mono (fun u hu => congrArg (fun x : ℝ => x^2) hu))]
  rw [limitingTarget, GP0182B2b_quad_smul, GP0182B2b_quad_sandwich c _ _
    (GP0182B2b_inverse_symmetric K hK)]
  congr 1
  exact (GP0182B2b_mean_outer_quad K.μ (projection K)
    (fun i j => (GP0182B2b_projection_memLp K hK i).2.integrable_mul
      (GP0182B2b_projection_memLp K hK j).2) a).symm

theorem GP0182B2b_scoreSum_memLp {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (N : ℕ) (a : Fin k) :
    MemLp (fun ω : Fin N → U => scoreSum K ω a) 2 (unitSampleLaw K N) := by
  let GP0182B2b_unitProb : IsProbabilityMeasure K.μ := hK.1
  simp only [scoreSum, Finset.sum_apply]
  exact memLp_finsetSum _ (fun d _ =>
    (GP0182B2b_score_memLp K hK a 2).comp_measurePreserving (corrected_pair_preserving K d))

theorem GP0182B2b_scoreSum_mean {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (N : ℕ) :
    meanVec (unitSampleLaw K N) (fun ω : Fin N → U => scoreSum K ω) = 0 := by
  let GP0182B2b_unitProb : IsProbabilityMeasure K.μ := hK.1
  let GP0182B2b_sampleProb : IsProbabilityMeasure (unitSampleLaw K N) := by
    unfold unitSampleLaw
    infer_instance
  ext a
  change (∫ ω, scoreSum K ω a ∂unitSampleLaw K N) = 0
  simp only [scoreSum, Finset.sum_apply]
  change (∫ ω, ∑ d : Dyad N, populationScore K (ω (firstUnit d))
    (ω (secondUnit d)) a ∂unitSampleLaw K N) = 0
  have hi (d : Dyad N) : MemLp (fun ω : Fin N → U =>
      populationScore K (ω (firstUnit d)) (ω (secondUnit d)) a) 2 (unitSampleLaw K N) := by
    simpa only [Function.comp_def] using
      (GP0182B2b_score_memLp K hK a 2).comp_measurePreserving (corrected_pair_preserving K d)
  rw [integral_finsetSum _ (fun d _ => (hi d).integrable one_le_two)]
  have hm (d : Dyad N) : (∫ ω, populationScore K (ω (firstUnit d))
      (ω (secondUnit d)) a ∂unitSampleLaw K N) = 0 := by
    rw [corrected_pair_integral K d _ (GP0182B2b_score_measurable K hK a)]
    exact congrFun (GP0182B2b_score_mean K hK) a
  simp only [hm, Finset.sum_const_zero]

theorem GP0182B2b_varMat_centered {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} (f : Ω → Vec k)
    (hLp : ∀ a, MemLp (fun ω => f ω a) 2 μ) (hmean : meanVec μ f = 0) :
    varMat μ f = meanMat μ (fun ω => outer (f ω) (f ω)) := by
  ext a b
  have hm (i : Fin k) : (∫ ω, f ω i ∂μ) = 0 := congrFun hmean i
  change ProbabilityTheory.covariance (fun ω => f ω a) (fun ω => f ω b) μ = _
  rw [covariance_eq_sub (hLp a) (hLp b), hm, hm]
  simp only [zero_mul, sub_zero]
  rfl

theorem GP0182B2b_dot_scoreSum {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (a : Vec k) (ω : Fin N → U) :
    dot a (scoreSum K ω) = ∑ d : Dyad N,
      dot a (populationScore K (ω (firstUnit d)) (ω (secondUnit d))) := by
  simp only [dot, scoreSum, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

theorem GP0182B2b_overlap_factor_limit :
    Tendsto (fun N : ℕ => (N : ℝ)^2 * ((N : ℝ)-1) * ((N : ℝ)-2) / (Dreal N)^2)
      atTop (𝓝 4) := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ)-1)⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    simpa only [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun N : ℕ => 4 * (1-((N : ℝ)-1)⁻¹)) atTop (𝓝 4) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).const_mul (4 : ℝ)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hn1 : (N : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  dsimp [Dreal]
  field_simp
  <;> ring

theorem GP0182B2b_trueTarget_scalar {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (c : Vec k) (hN : 2 ≤ N) :
    let h := fun uv : U × U => dot ((populationGram K)⁻¹.mulVec c) (populationScore K uv.1 uv.2)
    dot c ((trueTarget K N).mulVec c) =
      (N : ℝ)/Dreal N * (∫ uv, h uv^2 ∂K.μ.prod K.μ) +
      ((N : ℝ)^2*((N : ℝ)-1)*((N : ℝ)-2)/(Dreal N)^2) *
        (∫ u, (GP0182B2b_rowIntegral (μ := K.μ) h u)^2 ∂K.μ) := by
  let GP0182B2b_unitProb : IsProbabilityMeasure K.μ := hK.1
  let GP0182B2b_sampleProb : IsProbabilityMeasure (unitSampleLaw K N) := by
    unfold unitSampleLaw
    infer_instance
  dsimp only
  let a := (populationGram K)⁻¹.mulVec c
  let h := fun uv : U × U => dot a (populationScore K uv.1 uv.2)
  have hi := GP0182B2b_scoreSum_memLp K hK N
  rw [trueTarget, GP0182B2b_quad_smul, GP0182B2b_quad_sandwich c _ _
    (GP0182B2b_inverse_symmetric K hK), GP0182B2b_varMat_centered _ _ hi
      (GP0182B2b_scoreSum_mean K hK N),
    GP0182B2b_mean_outer_quad _ _ (fun i j => (hi i).integrable_mul (hi j))]
  simp_rw [GP0182B2b_dot_scoreSum]
  have hd := GP0182B2b_contrast_score K hK a
  have hsecond := GP0182B2b_dyad_second K.μ hN h hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
  dsimp only [h, a] at hsecond
  simp only [unitSampleLaw]
  rw [hsecond]
  field_simp [(printed_Dpos hN).ne']
  <;> ring

theorem GP0182B2b_trueTarget_contrast_limit {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (c : Vec k) :
    Tendsto (fun N => dot c ((trueTarget K N).mulVec c)) atTop
      (𝓝 (dot c ((limitingTarget K).mulVec c))) := by
  let h := fun uv : U × U => dot ((populationGram K)⁻¹.mulVec c) (populationScore K uv.1 uv.2)
  have hlim := (GP0182B2b_NdivD_limit.mul_const (∫ uv, h uv^2 ∂K.μ.prod K.μ)).add
    (GP0182B2b_overlap_factor_limit.mul_const
      (∫ u, (GP0182B2b_rowIntegral (μ := K.μ) h u)^2 ∂K.μ))
  simp only [h, zero_mul, zero_add, GP0182B2b_contrast_variance K hK c] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (GP0182B2b_trueTarget_scalar K hK c hN).symm


theorem GP0182B2b_sum_null {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)]
    {I E : Type*} [Fintype I] [NormedAddCommGroup E]
    (f : I → ∀ N, Ω N → E) (hf : ∀ i, inProbability μ (f i)) :
    inProbability μ (fun N ω => ∑ i, f i N ω) := by
  classical
  have hs (s : Finset I) : inProbability μ (fun N ω => ∑ i ∈ s, f i N ω) := by
    induction s using Finset.induction_on with
    | empty =>
      intro ε hε
      convert tendsto_const_nhds (x := (0 : ℝ)) using 1
      funext N
      simp [not_le.mpr hε]
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        WeightedConsistency.inProbability_add μ (hf i) ih
  exact hs univ

theorem GP0182B2b_null_of_eq_off {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)]
    {E : Type*} [NormedAddCommGroup E] (B : ∀ N, Set (Ω N))
    (hB : Tendsto (fun N => (μ N (B N)).toReal) atTop (𝓝 0))
    (f g : ∀ N, Ω N → E) (hg : inProbability μ g)
    (heq : ∀ᶠ N in atTop, ∀ ω, ω ∉ B N → f N ω = g N ω) : inProbability μ f := by
  intro ε hε
  apply squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) _
    (by simpa using (hg ε hε).add hB)
  filter_upwards [heq] with N hN
  calc
    _ ≤ (μ N ({ω | ε ≤ ‖g N ω‖} ∪ B N)).toReal := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      intro ω hω
      by_cases hb : ω ∈ B N
      · exact Or.inr hb
      · apply Or.inl
        change ε ≤ ‖g N ω‖
        change ε ≤ ‖f N ω‖ at hω
        rwa [hN ω hb] at hω
    _ ≤ _ := WeightedConsistency.probability_union_bound μ N _ _

theorem GP0182B2b_bread_approximation {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (c : Vec k) :
    inProbability (unitSampleLaw K) (fun N ω =>
      Real.sqrt N * dot c (coefficientError K ω) -
        Real.sqrt N * GP0182B2b_dyadAverage
          (fun uv : U × U => dot ((populationGram K)⁻¹.mulVec c) (populationScore K uv.1 uv.2)) ω) := by
  let GP0182B2b_unitProb : IsProbabilityMeasure K.μ := hK.1
  let GP0182B2b_sampleProb (N : ℕ) : IsProbabilityMeasure (unitSampleLaw K N) := by
    unfold unitSampleLaw
    infer_instance
  let P := (populationGram K)⁻¹
  let A := fun N (ω : Fin N → U) => (Dreal N)⁻¹ • sampleGram (design K ω)
  let E := fun N (ω : Fin N → U) (j : Fin k) => ∑ i, c i * ((A N ω)⁻¹ i j - P i j)
  let S := fun N (ω : Fin N → U) (j : Fin k) =>
    Real.sqrt N * GP0182B2b_dyadAverage (fun uv : U × U => populationScore K uv.1 uv.2 j) ω
  have hI (N : ℕ) : Measurable (fun ω : Fin N → U => (A N ω)⁻¹) := by
    apply GP0182B2b_measurable_inverse
    exact (GP0182B2b_measurable_Gram K hK N).const_smul ((Dreal N)⁻¹)
  have hE (N : ℕ) (j : Fin k) : Measurable (fun ω => E N ω j) :=
    Finset.measurable_fun_sum _ (fun i _ => measurable_const.mul
      ((((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hI N))).sub measurable_const)))
  have hS (N : ℕ) (j : Fin k) : Measurable (fun ω => S N ω j) :=
    (GP0182B2b_dyadAverage_measurable _ (GP0182B2b_score_measurable K hK j) N).const_mul _
  have hEnull (j : Fin k) : inProbability (unitSampleLaw K) (fun N ω => E N ω j) := by
    let φ : Mat k → ℝ := fun M => ∑ i, c i * M i j
    have hc : Continuous φ := by unfold φ; fun_prop
    have hi0 : inProbability (unitSampleLaw K) (fun N ω =>
        ((A N ω)⁻¹ - P) - (0 : Mat k)) := by
      simpa only [sub_zero] using GP0182B2b_inverse_Gram_null K hK
    have h := WeightedConsistency.inProbability_continuousAt (unitSampleLaw K)
      (f := fun N ω => (A N ω)⁻¹ - P) (x := (0 : Mat k)) (φ := φ)
      hc.continuousAt hi0
    simpa only [φ, Matrix.zero_apply, Matrix.sub_apply, mul_zero,
      Finset.sum_const_zero, sub_zero] using h
  have hprod (j : Fin k) : inProbability (unitSampleLaw K) (fun N ω => S N ω j * E N ω j) := by
    let h := fun uv : U × U => populationScore K uv.1 uv.2 j
    have hmean : (∫ uv, h uv ∂K.μ.prod K.μ) = 0 := congrFun (GP0182B2b_score_mean K hK) j
    have hsym : ∀ u v, h (u,v) = h (v,u) := fun u v =>
      congrFun (GP0182B2b_score_symmetric K hK u v) j
    let ν := gaussianReal 0 (4 * ∫ u, (GP0182B2b_rowIntegral (μ := K.μ) h u)^2 ∂K.μ).toNNReal
    have hclt : TendstoInDistribution
        (fun N ω => S N (GP0182B2b_prefix N ω) j) atTop id
        (fun _ => GP0182B2b_product K.μ) ν :=
      GP0182B2b_dyad_clt K.μ h (GP0182B2b_score_measurable K hK j)
        (GP0182B2b_score_memLp K hK j 2) hsym hmean
    have hEp := GP0182B2b_prefix_inProbability K.μ (fun N ω => E N ω j)
      (fun N => hE N j) (hEnull j)
    have hp := hclt.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ => p.1*p.2) (by fun_prop) hEp
      (fun N => ((hE N j).comp (GP0182B2b_prefix_measurable N)).aemeasurable)
    have hp0 : TendstoInDistribution
        (fun N ω => S N (GP0182B2b_prefix N ω) j * E N (GP0182B2b_prefix N ω) j)
        atTop (fun _ : ℝ => (0 : ℝ)) (fun _ => GP0182B2b_product K.μ) ν := by
      simpa only [mul_zero] using hp
    exact (GP0182B2b_prefix_null_iff K.μ (fun N ω => S N ω j * E N ω j)
      (fun N => (hS N j).mul (hE N j))).mpr
        (GP0182B2b_distribution_zero_inMeasure (GP0182B2b_product K.μ) ν _ hp0)
  have hsum := GP0182B2b_sum_null (unitSampleLaw K)
    (fun j N ω => S N ω j * E N ω j) hprod
  apply GP0182B2b_null_of_eq_off (unitSampleLaw K)
    (fun N => {ω | (A N ω).det = 0}) (GP0182B2b_singular_probability K hK)
    _ _ hsum
  filter_upwards [eventually_ge_atTop 2] with N hN ω hω
  change (A N ω).det ≠ 0 at hω
  have hD : Dreal N ≠ 0 := (printed_Dpos hN).ne'
  have hG : IsUnit (sampleGram (design K ω)).det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply hω
    dsimp [A]
    rw [Matrix.det_smul, hz, mul_zero]
  have hOLS := ols_score_identity (design K ω) (response K ω) (populationBeta K) hG
  let s : Vec k := (Real.sqrt N / Dreal N) • scoreSum K ω
  have hy : Real.sqrt N • coefficientError K ω = (A N ω)⁻¹.mulVec s := by
    rw [coefficientError, hOLS]
    change Real.sqrt N • ((sampleGram (design K ω))⁻¹.mulVec (scoreSum K ω)) = _
    dsimp only [A, s]
    rw [matrix_inverse_scale_total _ _ (inv_ne_zero hD), inv_inv,
      Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
    have he : Dreal N * (Real.sqrt N / Dreal N) = Real.sqrt N := by
      field_simp
    rw [he]
  have hs (j : Fin k) : s j = S N ω j := by
    simp only [s, S, GP0182B2b_dyadAverage, scoreSum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    change (Real.sqrt N / Dreal N) * (∑ d : Dyad N,
      populationScore K (ω (firstUnit d)) (ω (secondUnit d)) j) =
        Real.sqrt N * ((Dreal N)⁻¹ * ∑ d : Dyad N,
          populationScore K (ω (firstUnit d)) (ω (secondUnit d)) j)
    ring
  have hPs : P.transpose = P := GP0182B2b_inverse_symmetric K hK
  have hyc : Real.sqrt N * dot c (coefficientError K ω) = dot c ((A N ω)⁻¹.mulVec s) := by
    rw [← GP0182B2b_dot_smul, hy]
  have happrox : Real.sqrt N * GP0182B2b_dyadAverage
      (fun uv : U × U => dot (P.mulVec c) (populationScore K uv.1 uv.2)) ω =
        dot c (P.mulVec s) := by
    rw [GP0182B2b_dot_mulVec, hPs]
    dsimp only [s]
    rw [GP0182B2b_dot_smul, GP0182B2b_dot_scoreSum]
    change Real.sqrt N * ((Dreal N)⁻¹ * ∑ d : Dyad N,
      dot (P.mulVec c) (populationScore K (ω (firstUnit d)) (ω (secondUnit d)))) = _
    ring
  change Real.sqrt N * dot c (coefficientError K ω) -
    Real.sqrt N * GP0182B2b_dyadAverage
      (fun uv : U × U => dot (P.mulVec c) (populationScore K uv.1 uv.2)) ω = _
  rw [hyc, happrox, ← GP0182B2b_dot_sub, ← Matrix.sub_mulVec, GP0182B2b_dot_mulVec]
  simp only [dot, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.sub_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hs j]
  change (∑ i, ((A N ω)⁻¹ i j - P i j) * c i) * S N ω j = S N ω j * E N ω j
  rw [mul_comm (S N ω j)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring


theorem GP0182B2b_scaled_variance_null {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (c : Vec k) :
    inProbability (unitSampleLaw K) (fun N ω =>
      (N : ℝ) * dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c) -
        dot c ((limitingTarget K).mulVec c)) := by
  let GP0182B2b_unitProb : IsProbabilityMeasure K.μ := hK.1
  let GP0182B2b_sampleProb (N : ℕ) : IsProbabilityMeasure (unitSampleLaw K N) := by
    unfold unitSampleLaw
    infer_instance
  let φ : Mat k → ℝ := fun M => dot c (M.mulVec c)
  have hc : Continuous φ := by
    simp only [φ, dot, Matrix.mulVec, dotProduct]
    fun_prop
  have hcons : inProbability (unitSampleLaw K) (fun N ω =>
      ((N : ℝ) • sampleVariance members (design K ω) (response K ω) - trueTarget K N) - (0 : Mat k)) := by
    simpa only [sub_zero] using GP0182B2b_variance_consistency K hK
  have h := WeightedConsistency.inProbability_continuousAt (unitSampleLaw K)
    (f := fun N ω => (N : ℝ) • sampleVariance members (design K ω) (response K ω) - trueTarget K N)
    (x := (0 : Mat k)) (φ := φ) hc.continuousAt hcons
  have hz : φ 0 = 0 := by simp [φ, dot]
  rw [hz] at h
  simp only [sub_zero] at h
  change inProbability (unitSampleLaw K) (fun N ω => dot c
    (((N : ℝ) • sampleVariance members (design K ω) (response K ω) - trueTarget K N).mulVec c)) at h
  simp_rw [GP0182B2b_quad_sub, GP0182B2b_quad_smul] at h
  have hd := WeightedConsistency.inProbability_deterministic (unitSampleLaw K)
    (fun N => dot c ((trueTarget K N).mulVec c) - dot c ((limitingTarget K).mulVec c))
    (by simpa only [sub_self] using
      (GP0182B2b_trueTarget_contrast_limit K hK c).sub_const (dot c ((limitingTarget K).mulVec c)))
  simpa only [sub_add_sub_cancel] using WeightedConsistency.inProbability_add (unitSampleLaw K) h hd

theorem GP0182B2b_variance_bad {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (c : Vec k)
    (hc : 0 < dot c ((limitingTarget K).mulVec c)) :
    Tendsto (fun N : ℕ => (unitSampleLaw K N {ω |
      dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c) ≤ 0}).toReal)
      atTop (𝓝 0) := by
  let GP0182B2b_unitProb : IsProbabilityMeasure K.μ := hK.1
  let GP0182B2b_sampleProb (N : ℕ) : IsProbabilityMeasure (unitSampleLaw K N) := by
    unfold unitSampleLaw
    infer_instance
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _
    (GP0182B2b_scaled_variance_null K hK c (dot c ((limitingTarget K).mulVec c)) hc)
  intro N
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro ω hω
  change dot c ((limitingTarget K).mulVec c) ≤
    ‖(N : ℝ) * dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c) -
      dot c ((limitingTarget K).mulVec c)‖
  have hn := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hω
  rw [Real.norm_eq_abs]
  linarith [neg_le_abs ((N : ℝ) * dot c
    ((sampleVariance members (design K ω) (response K ω)).mulVec c) -
      dot c ((limitingTarget K).mulVec c))]

theorem GP0182B2b_numerator_clt {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (c : Vec k)
    [IsProbabilityMeasure K.μ] :
    TendstoInDistribution (fun (N : ℕ) (ω : ℕ → U) =>
      Real.sqrt N * dot c (coefficientError K (GP0182B2b_prefix N ω)))
      atTop id (fun _ => GP0182B2b_product K.μ)
      (gaussianReal 0 (dot c ((limitingTarget K).mulVec c)).toNNReal) := by
  let a := (populationGram K)⁻¹.mulVec c
  let h := fun uv : U × U => dot a (populationScore K uv.1 uv.2)
  have hd := GP0182B2b_contrast_score K hK a
  have hclt := GP0182B2b_dyad_clt K.μ h hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
  have hν : 4 * (∫ u, (GP0182B2b_rowIntegral (μ := K.μ) h u)^2 ∂K.μ) =
      dot c ((limitingTarget K).mulVec c) := GP0182B2b_contrast_variance K hK c
  rw [hν] at hclt
  have hm (N : ℕ) : Measurable (fun ω : Fin N → U =>
      Real.sqrt N * dot c (coefficientError K ω) -
        Real.sqrt N * GP0182B2b_dyadAverage h ω) :=
    ((GP0182B2b_measurable_statistics K hK c N).1.const_mul _).sub
      ((GP0182B2b_dyadAverage_measurable h hd.1 N).const_mul _)
  have hdiff := GP0182B2b_prefix_inProbability K.μ
    (fun N (ω : Fin N → U) => Real.sqrt N * dot c (coefficientError K ω) -
      Real.sqrt N * GP0182B2b_dyadAverage h ω) hm (GP0182B2b_bread_approximation K hK c)
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ _ hclt hdiff
    (fun N => (((GP0182B2b_measurable_statistics K hK c N).1.comp
      (GP0182B2b_prefix_measurable N)).const_mul _).aemeasurable)

theorem GP0182B2b_pivot_weak {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (c : Vec k)
    (hc : 0 < dot c ((limitingTarget K).mulVec c)) :
    weakLimit (unitSampleLaw K) (fun N ω =>
      dot c (coefficientError K ω) /
        Real.sqrt (dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c)))
      (gaussianReal 0 1) := by
  let GP0182B2b_unitProb : IsProbabilityMeasure K.μ := hK.1
  let GP0182B2b_sampleProb (N : ℕ) : IsProbabilityMeasure (unitSampleLaw K N) := by
    unfold unitSampleLaw
    infer_instance
  let x := fun N (ω : Fin N → U) => dot c (coefficientError K ω)
  let v := fun N (ω : Fin N → U) =>
    dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c)
  let t := dot c ((limitingTarget K).mulVec c)
  have ht : 0 < t := hc
  have hx (N : ℕ) : Measurable (x N) := (GP0182B2b_measurable_statistics K hK c N).1
  have hv (N : ℕ) : Measurable (v N) := (GP0182B2b_measurable_statistics K hK c N).2
  let W := fun N (ω : Fin N → U) => (Real.sqrt ((N : ℝ)*v N ω))⁻¹
  have hWm (N : ℕ) : Measurable (W N) := ((hv N).const_mul (N : ℝ)).sqrt.inv
  have hφ : ContinuousAt (fun z : ℝ => (Real.sqrt z)⁻¹) t :=
    Real.continuous_sqrt.continuousAt.inv₀ (Real.sqrt_pos.mpr ht).ne'
  have hW : inProbability (unitSampleLaw K) (fun N ω => W N ω - (Real.sqrt t)⁻¹) :=
    WeightedConsistency.inProbability_continuousAt (unitSampleLaw K)
      (f := fun N ω => (N : ℝ)*v N ω) (x := t) (φ := fun z : ℝ => (Real.sqrt z)⁻¹)
      hφ (GP0182B2b_scaled_variance_null K hK c)
  have hW0 := GP0182B2b_prefix_inProbability K.μ
    (fun N ω => W N ω - (Real.sqrt t)⁻¹)
    (fun N => (hWm N).sub measurable_const) hW
  have hWi : TendstoInMeasure (GP0182B2b_product K.μ)
      (fun N ω => W N (GP0182B2b_prefix N ω)) atTop (fun _ => (Real.sqrt t)⁻¹) := by
    rw [tendstoInMeasure_iff_measureReal_norm] at hW0 ⊢
    simpa only [sub_zero] using hW0
  have hp := (GP0182B2b_numerator_clt K hK c).continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.1*p.2) (by fun_prop) hWi
    (fun N => ((hWm N).comp (GP0182B2b_prefix_measurable N)).aemeasurable)
  have hsq : NNReal.mk ((Real.sqrt t)^2) (sq_nonneg _) = t.toNNReal := by
    apply NNReal.eq
    change (Real.sqrt t)^2 = (t.toNNReal : ℝ)
    rw [Real.sq_sqrt ht.le, Real.coe_toNNReal t ht.le]
  have htnn : t.toNNReal ≠ 0 := by
    simpa only [ne_eq, Real.toNNReal_eq_zero, not_le] using ht
  have hl := gaussianReal_div_const
    (HasLaw.id : HasLaw id (gaussianReal 0 t.toNNReal) (gaussianReal 0 t.toNNReal))
    (Real.sqrt t)
  rw [zero_div, hsq, div_self htnn] at hl
  have hl' : HasLaw (fun z : ℝ => z * (Real.sqrt t)⁻¹) (gaussianReal 0 1)
      (gaussianReal 0 t.toNNReal) := by
    simpa only [div_eq_mul_inv, id_eq] using hl
  have hp01 : TendstoInDistribution
      (fun (N : ℕ) (ω : ℕ → U) => (Real.sqrt N*x N (GP0182B2b_prefix N ω))*W N (GP0182B2b_prefix N ω))
      atTop id (fun _ => GP0182B2b_product K.μ) (gaussianReal 0 1) := by
    refine ⟨hp.forall_aemeasurable, measurable_id.aemeasurable, ?_⟩
    have hmap : (gaussianReal 0 (dot c ((limitingTarget K).mulVec c)).toNNReal).map
        (fun z : ℝ => z * (Real.sqrt t)⁻¹) = gaussianReal 0 1 := hl'.map_eq
    simpa only [id_eq, hmap, Measure.map_id] using hp.tendsto
  have hT : TendstoInDistribution
      (fun (N : ℕ) (ω : ℕ → U) => x N (GP0182B2b_prefix N ω) / Real.sqrt (v N (GP0182B2b_prefix N ω)))
      atTop id (fun _ => GP0182B2b_product K.μ) (gaussianReal 0 1) := by
    refine ⟨fun N => (((hx N).div (hv N).sqrt).comp
      (GP0182B2b_prefix_measurable N)).aemeasurable, measurable_id.aemeasurable, ?_⟩
    apply hp01.tendsto.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    apply Subtype.ext
    apply Measure.map_congr
    apply Eventually.of_forall
    intro ω
    have hs : Real.sqrt (N : ℝ) ≠ 0 := by
      apply (Real.sqrt_pos.mpr _).ne'
      exact_mod_cast (by omega : 0 < N)
    change (Real.sqrt N*x N (GP0182B2b_prefix N ω)) *
      (Real.sqrt ((N : ℝ)*v N (GP0182B2b_prefix N ω)))⁻¹ = _
    rw [Real.sqrt_mul (Nat.cast_nonneg N), _root_.mul_inv_rev]
    calc
      _ = (Real.sqrt N * (Real.sqrt N)⁻¹) *
          (x N (GP0182B2b_prefix N ω) * (Real.sqrt (v N (GP0182B2b_prefix N ω)))⁻¹) := by ring
      _ = _ := by simp only [mul_inv_cancel₀ hs, one_mul, div_eq_mul_inv]
  refine ⟨fun N => ((hx N).div (hv N).sqrt).aemeasurable, inferInstance, ?_⟩
  intro g
  have hh := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hT.forall_aemeasurable hT.aemeasurable_limit).mp hT g
  have he (N : ℕ) :
      (∫ ω, g (x N (GP0182B2b_prefix N ω) / Real.sqrt (v N (GP0182B2b_prefix N ω)))
        ∂GP0182B2b_product K.μ) =
      ∫ ω, g (x N ω / Real.sqrt (v N ω)) ∂unitSampleLaw K N :=
    GP0182B2b_prefix_integral K.μ N _
      (g.continuous.measurable.comp ((hx N).div (hv N).sqrt))
  change Tendsto (fun N => ∫ ω, g (x N (GP0182B2b_prefix N ω) /
    Real.sqrt (v N (GP0182B2b_prefix N ω))) ∂GP0182B2b_product K.μ)
      atTop (𝓝 (∫ z, g z ∂gaussianReal 0 1)) at hh
  simpa only [he] using hh

theorem contrast_coverage_corrected_proof {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (c : Vec k)
    (hc : 0 < dot c ((limitingTarget K).mulVec c)) (α : ℝ) (hα : 0 < α ∧ α < 1) :
    Tendsto (fun N : ℕ => (unitSampleLaw K N {ω |
      0 ≤ dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c) ∧
      |dot c (coefficientError K ω)| ≤ normalQuantile (1-α/2) *
        Real.sqrt (dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c))}).toReal)
      atTop (𝓝 (1-α)) := by
  exact GP0182B2b_coverage_from_pivot K hK c (GP0182B2b_pivot_weak K hK c hc)
    (GP0182B2b_variance_bad K hK c hc) α hα

end AronowAudit.P018.Wave1
