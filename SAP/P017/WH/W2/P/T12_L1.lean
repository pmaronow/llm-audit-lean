import SAP.P017.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P017.WH.W2.P.T12_L1

open MeasureTheory ProbabilityTheory Set AronowAudit.P017
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

private theorem uniform_measurable (n : ℕ) : Measurable (rareUniform n) := by
  unfold rareUniform
  exact measurable_fract.comp (by fun_prop)

private theorem mean_measurable (n : ℕ) : Measurable (smallNormalMean n) := by
  unfold smallNormalMean sampleMean
  fun_prop

private theorem flag_measurable (p : ℕ → ℝ) (n : ℕ) : Measurable (rareFlag p n) := by
  exact measurable_const.ite
    (measurableSet_lt (uniform_measurable n) measurable_const) measurable_const

private theorem clip_measurable (n : ℕ) : Measurable (smallNormalClip n) := by
  unfold smallNormalClip clipReal
  exact measurable_const.min (measurable_const.max (mean_measurable n))

private theorem estimator_measurable (p : ℕ → ℝ) (n : ℕ) :
    Measurable (rareEstimator p n) := by
  exact (clip_measurable n).add (measurable_const.mul (flag_measurable p n))

private theorem remainder_measurable (p : ℕ → ℝ) (n : ℕ) :
    Measurable (rareRemainder p n) := by
  exact measurable_const.mul
    (((clip_measurable n).sub (mean_measurable n)).add
      (measurable_const.mul (flag_measurable p n)))

private theorem scaled_mean_law (n : ℕ) (hn : 1 ≤ n) :
    (iidSamples slowPopulation).map (fun s => sqrtN n * smallNormalMean n s) =
      gaussianReal 0 1 := by
  have hmain := AronowAudit.P017.Wave1.arbitrary_outlier_sequence_proof
    slowP (fun n _ => AronowAudit.P017.slow_probability_positive_limit.1 n)
      AronowAudit.P017.slow_probability_positive_limit.2
  rcases hmain with ⟨_, _, _, _, _, _, hseq, _, _, _⟩
  rcases hseq n hn with ⟨_, _, _, hscaled, _⟩
  exact hscaled

private theorem mean_law (n : ℕ) (hn : 1 ≤ n) :
    (iidSamples slowPopulation).map (smallNormalMean n) =
      gaussianReal 0 (1 / (n : ℝ≥0)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < sqrtN n := Real.sqrt_pos.mpr hnR
  have hs2 : sqrtN n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hcomp : (fun s => (sqrtN n * smallNormalMean n s) / sqrtN n) =
      smallNormalMean n := by
    funext s
    field_simp [hs.ne']
  calc
    (iidSamples slowPopulation).map (smallNormalMean n) =
        (iidSamples slowPopulation).map
          (fun s => (sqrtN n * smallNormalMean n s) / sqrtN n) := by
      exact congrArg (fun f : (ℕ → ℝ × (ℝ × (ℝ × ℝ))) → ℝ =>
        (iidSamples slowPopulation).map f) hcomp.symm
    _ = ((iidSamples slowPopulation).map
        (fun s => sqrtN n * smallNormalMean n s)).map (fun x : ℝ => x / sqrtN n) := by
      change (iidSamples slowPopulation).map
          ((fun x : ℝ => x / sqrtN n) ∘
            (fun s => sqrtN n * smallNormalMean n s)) = _
      exact (Measure.map_map (by fun_prop)
        (measurable_const.mul (mean_measurable n))).symm
    _ = gaussianReal 0 (1 / (n : ℝ≥0)) := by
      rw [scaled_mean_law n hn, gaussianReal_map_div_const]
      simp only [zero_div]
      congr 1
      apply NNReal.eq
      simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_one, NNReal.coe_natCast]
      rw [hs2]

private theorem mean_second (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun s => smallNormalMean n s ^ 2) (iidSamples slowPopulation) ∧
    (∫ s, smallNormalMean n s ^ 2 ∂iidSamples slowPopulation) = 1 / (n : ℝ) := by
  have hi : Integrable (fun x : ℝ => x ^ 2)
      (gaussianReal 0 (1 / (n : ℝ≥0))) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1 / (n : ℝ≥0)) 2).integrable_sq
  have hi' : Integrable (fun x : ℝ => x ^ 2)
      ((iidSamples slowPopulation).map (smallNormalMean n)) :=
    (mean_law n hn).symm ▸ hi
  refine ⟨hi'.comp_measurable (mean_measurable n), ?_⟩
  rw [← integral_map (f := fun x : ℝ => x ^ 2) (mean_measurable n).aemeasurable
      (by fun_prop), mean_law n hn]
  have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ))
    (v := (1 / (n : ℝ≥0)))
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hv
  simpa only [sub_zero, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast] using hv

private theorem mean_tail (n : ℕ) (hn : 1 ≤ n) :
    pr (iidSamples slowPopulation)
      {s | |smallNormalMean n s| > 1 / 2} ≤ 4 / (n : ℝ) := by
  let Q := iidSamples slowPopulation
  let C := {s | 1 / 2 < |smallNormalMean n s|}
  have hmC : MeasurableSet C := measurableSet_lt measurable_const
    (by simpa only [Real.norm_eq_abs] using (mean_measurable n).norm)
  have hi : Integrable (C.indicator (fun _ => (1 / 4 : ℝ))) Q :=
    (integrable_const _).indicator hmC
  have hp (s) : C.indicator (fun _ => (1 / 4 : ℝ)) s ≤ smallNormalMean n s ^ 2 := by
    by_cases hs : s ∈ C
    · rw [Set.indicator_of_mem hs]
      have hh := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (abs_nonneg _)).mpr hs.le
      norm_num only [sq_abs, one_div, inv_pow, Nat.reducePow] at hh ⊢
      exact hh
    · rw [Set.indicator_of_notMem hs]
      exact sq_nonneg _
  have hh := integral_mono hi (mean_second n hn).1 hp
  rw [(mean_second n hn).2] at hh
  simp only [integral_indicator_const _ hmC, smul_eq_mul] at hh
  change pr Q C ≤ _
  unfold pr
  calc
    Q.real C ≤ 4 * (1 / (n : ℝ)) := by linarith
    _ = 4 / (n : ℝ) := by ring

private theorem flag_cases (p : ℕ → ℝ) (n : ℕ)
    (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) :
    rareFlag p n s = 0 ∨ rareFlag p n s = 1 := by
  unfold rareFlag
  split_ifs <;> simp

private theorem estimator_zero_case (p : ℕ → ℝ) (n : ℕ)
    (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) (hs : rareFlag p n s = 0) :
    rareEstimator p n s - AronowAudit.P017.clipReal 0 1 (rareEstimator p n s) = 0 := by
  have hh : rareEstimator p n s = smallNormalClip n s := by
    simp only [rareEstimator, hs, mul_zero, add_zero]
  rw [hh]
  exact sub_eq_zero.mpr (rare_estimator_finite (smallNormalMean n s)).1.symm

private theorem estimator_one_case (p : ℕ → ℝ) (n : ℕ)
    (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) (hs : rareFlag p n s = 1) :
    rareEstimator p n s - AronowAudit.P017.clipReal 0 1 (rareEstimator p n s) =
      smallNormalClip n s + 9 := by
  have hf := rare_estimator_finite (smallNormalMean n s)
  have hh : rareEstimator p n s = smallNormalClip n s + 10 := by
    simp only [rareEstimator, hs, mul_one]
  have hclip : AronowAudit.P017.clipReal 0 1 (smallNormalClip n s + 10) = 1 := by
    simpa only [smallNormalClip, SAP.P017.clipReal, AronowAudit.P017.clipReal]
      using hf.2.2.2.1
  rw [hh, hclip]
  ring

private theorem estimator_clip_error_integrable (p : ℕ → ℝ) (n : ℕ) :
    Integrable (fun s =>
      (rareEstimator p n s - AronowAudit.P017.clipReal 0 1 (rareEstimator p n s)) ^ 2)
      (iidSamples slowPopulation) := by
  have hm : Measurable (fun s =>
      rareEstimator p n s - AronowAudit.P017.clipReal 0 1 (rareEstimator p n s)) :=
    (estimator_measurable p n).sub
      (measurable_const.min (measurable_const.max (estimator_measurable p n)))
  have hL : MemLp (fun s =>
      rareEstimator p n s - AronowAudit.P017.clipReal 0 1 (rareEstimator p n s))
      2 (iidSamples slowPopulation) := by
    apply MemLp.of_bound hm.aestronglyMeasurable (19 / 2)
    apply ae_of_all
    intro s
    rw [Real.norm_eq_abs]
    rcases flag_cases p n s with h | h
    · rw [estimator_zero_case p n s h, abs_zero]
      norm_num
    · rw [estimator_one_case p n s h]
      have hb : -(1 / 2 : ℝ) ≤ smallNormalClip n s ∧
          smallNormalClip n s ≤ 1 / 2 := by
        simpa only [smallNormalClip, SAP.P017.clipReal, AronowAudit.P017.clipReal,
          zero_sub, zero_add] using
          AronowAudit.P017.clipReal_bounds 0 (1 / 2) (smallNormalMean n s) (by norm_num)
      rw [abs_of_nonneg (by linarith [hb.1])]
      linarith [hb.2]
  exact hL.integrable_sq

private theorem remainder_square_integrable (p : ℕ → ℝ) (n : ℕ)
    (hn : 1 ≤ n) :
    Integrable (fun s => rareRemainder p n s ^ 2) (iidSamples slowPopulation) := by
  have hm : MemLp (smallNormalMean n) 2 (iidSamples slowPopulation) :=
    (memLp_two_iff_integrable_sq (mean_measurable n).aestronglyMeasurable).mpr
      (mean_second n hn).1
  have hc : MemLp (smallNormalClip n) 2 (iidSamples slowPopulation) := by
    apply MemLp.of_bound (clip_measurable n).aestronglyMeasurable (1 / 2)
    apply ae_of_all
    intro s
    have hb : -(1 / 2 : ℝ) ≤ smallNormalClip n s ∧
        smallNormalClip n s ≤ 1 / 2 := by
      simpa only [smallNormalClip, SAP.P017.clipReal, AronowAudit.P017.clipReal,
        zero_sub, zero_add] using
        AronowAudit.P017.clipReal_bounds 0 (1 / 2) (smallNormalMean n s) (by norm_num)
    exact abs_le.mpr hb
  have hb : MemLp (rareFlag p n) 2 (iidSamples slowPopulation) := by
    apply MemLp.of_bound (flag_measurable p n).aestronglyMeasurable 1
    apply ae_of_all
    intro s
    simp only [rareFlag]
    split_ifs <;> norm_num
  exact (((hc.sub hm).add (hb.const_mul 10)).const_mul (sqrtN n)).integrable_sq

private theorem leaf_proof : SAP.P017.WH.W2.T12_L1 := by
  intro p n hn
  refine ⟨uniform_measurable n, flag_measurable p n, mean_measurable n,
    clip_measurable n, estimator_measurable p n, remainder_measurable p n,
    (mean_second n hn).1, remainder_square_integrable p n hn,
    estimator_clip_error_integrable p n, ?_⟩
  exact mean_tail n hn

end
end SAP.P017.WH.W2.P.T12_L1

theorem SAP.P017.WH.W2.T12_L1_proof : SAP.P017.WH.W2.T12_L1 :=
  SAP.P017.WH.W2.P.T12_L1.leaf_proof
