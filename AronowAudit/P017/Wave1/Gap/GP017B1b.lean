import AronowAudit.P017.P017_Audit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.Independence.InfinitePi

/-!
The logarithmic rare-outlier counterexample. The fractional sum of uniform
coordinates is handled through Haar measure on the unit additive circle.
-/

namespace AronowAudit.P017.Wave1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

private theorem GP017B1b_circle_law :
    uniformHalfOpen01.map (fun x : ℝ => (x : AddCircle (1 : ℝ))) = volume := by
  simpa only [uniformHalfOpen01, restrict_Ico_eq_restrict_Ioc, zero_add] using
    (AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq

private def GP017B1b_rep (z : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.measurableEquivIco (1 : ℝ) 0 z : ℝ)

private theorem GP017B1b_rep_measurable : Measurable GP017B1b_rep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

private theorem GP017B1b_rep_coe (x : ℝ) :
    GP017B1b_rep (x : AddCircle (1 : ℝ)) = Int.fract x := by
  change (AddCircle.equivIco (1 : ℝ) 0 (x : AddCircle (1 : ℝ)) : ℝ) = _
  simpa only [div_one, mul_one] using AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) x

private theorem GP017B1b_rep_law :
    (volume : Measure (AddCircle (1 : ℝ))).map GP017B1b_rep = uniformHalfOpen01 := by
  rw [← GP017B1b_circle_law,
    Measure.map_map GP017B1b_rep_measurable AddCircle.measurable_mk']
  have heq : (fun x : ℝ => GP017B1b_rep (x : AddCircle (1 : ℝ)))
      =ᵐ[uniformHalfOpen01] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    rw [GP017B1b_rep_coe]
    exact Int.fract_eq_self.mpr hx
  change uniformHalfOpen01.map (fun x : ℝ => GP017B1b_rep (x : AddCircle (1 : ℝ))) = _
  rw [Measure.map_congr heq, Measure.map_id]

private theorem GP017B1b_uniform_measurable (n : ℕ) : Measurable (rareUniform n) := by
  unfold rareUniform
  exact measurable_fract.comp (by fun_prop)

private theorem GP017B1b_uniform_law (n : ℕ) (hn : 1 ≤ n) :
    (iidSamples slowPopulation).map (rareUniform n) = uniformHalfOpen01 := by
  let Q := iidSamples slowPopulation
  let X : ℕ → (ℕ → ℝ × (ℝ × (ℝ × ℝ))) → AddCircle (1 : ℝ) :=
    fun i s => ((s i).2.1 : AddCircle (1 : ℝ))
  have hm (i : ℕ) : Measurable (X i) := by
    exact AddCircle.measurable_mk'.comp
      (measurable_fst.comp (measurable_snd.comp (measurable_pi_apply i)))
  have hcoord (i : ℕ) : Q.map (X i) = volume := by
    change (Measure.infinitePi (fun _ : ℕ => slowPopulation)).map
      ((fun w : ℝ × (ℝ × (ℝ × ℝ)) => (w.2.1 : AddCircle (1 : ℝ))) ∘
        (fun s => s i)) = _
    rw [← Measure.map_map
      (show Measurable (fun w : ℝ × (ℝ × (ℝ × ℝ)) => (w.2.1 : AddCircle (1 : ℝ))) by fun_prop)
      (measurable_pi_apply i),
      Measure.infinitePi_map_eval]
    change slowPopulation.map ((fun x : ℝ => (x : AddCircle (1 : ℝ))) ∘
      (fun w : ℝ × (ℝ × (ℝ × ℝ)) => w.2.1)) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop)]
    have hc : slowPopulation.map (fun w => w.2.1) = uniformHalfOpen01 := by
      change slowPopulation.map ((Prod.fst : ℝ × (ℝ × ℝ) → ℝ) ∘ Prod.snd) = _
      rw [← Measure.map_map measurable_fst measurable_snd, slowPopulation,
        Measure.map_snd_prod]
      simp
    rw [hc, GP017B1b_circle_law]
  have hind : iIndepFun X Q :=
    iIndepFun_infinitePi
      (X := fun _ : ℕ => fun w : ℝ × (ℝ × (ℝ × ℝ)) => (w.2.1 : AddCircle (1 : ℝ)))
      (fun _ => by fun_prop)
  have GP017B1b_circleProbability : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    ⟨by simp⟩
  have hadd : ((volume : Measure (AddCircle (1 : ℝ))).prod volume).map
      (fun z => z.1 + z.2) = volume := by
    have h := (measurePreserving_snd (μ := (volume : Measure (AddCircle (1 : ℝ))))).comp
      (measurePreserving_prod_add (volume : Measure (AddCircle (1 : ℝ))) volume)
    exact h.map_eq
  have hsum (k : ℕ) : Q.map (fun s => ∑ i ∈ Finset.range (k + 1), X i s) = volume := by
    induction k with
    | zero => simpa using hcoord 0
    | succ k ih =>
      have hi : IndepFun (fun s => ∑ i ∈ Finset.range (k + 1), X i s) (X (k + 1)) Q := by
        simpa only [Finset.sum_fn] using hind.indepFun_sum_range_succ hm (k + 1)
      have hjoint := hi.map_prod_eq_prod_map_map (by fun_prop) (hm (k + 1)).aemeasurable
      rw [ih, hcoord] at hjoint
      calc
        _ = Q.map ((fun z : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => z.1 + z.2) ∘
            (fun s => (∑ i ∈ Finset.range (k + 1), X i s, X (k + 1) s))) := by
          congr 1; funext s; simp [Finset.sum_range_succ]
        _ = _ := by
          rw [← Measure.map_map (by fun_prop) (by fun_prop), hjoint, hadd]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hsum' := hsum k
  have heq : rareUniform (k + 1) = GP017B1b_rep ∘
      (fun s => ∑ i ∈ Finset.range (k + 1), X i s) := by
    funext s
    rw [Function.comp_apply]
    have hc : (∑ i ∈ Finset.range (k + 1), X i s) =
        ((∑ i ∈ Finset.range (k + 1), (s i).2.1 : ℝ) : AddCircle (1 : ℝ)) := by
      exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _).symm
    rw [hc, GP017B1b_rep_coe]
    rfl
  rw [heq, ← Measure.map_map GP017B1b_rep_measurable (by fun_prop), hsum', GP017B1b_rep_law]


private theorem GP017B1b_effect_law :
    slowPopulation.map slowEffect = slowEffectLaw := by
  have heq : slowEffect = (fun w : ℝ × (ℝ × (ℝ × ℝ)) => w.2.2.1) := by
    funext w; simp [slowEffect, slowY1, slowY0]
  rw [heq]
  change slowPopulation.map (((Prod.fst : ℝ × ℝ → ℝ) ∘
    (Prod.snd : ℝ × (ℝ × ℝ) → ℝ × ℝ)) ∘ Prod.snd) = _
  rw [← Measure.map_map
    (show Measurable ((Prod.fst : ℝ × ℝ → ℝ) ∘ (Prod.snd : ℝ × (ℝ × ℝ) → ℝ × ℝ)) by fun_prop)
    measurable_snd, slowPopulation, Measure.map_snd_prod]
  simp only [measure_univ, one_smul]
  rw [← Measure.map_map measurable_fst measurable_snd, Measure.map_snd_prod]
  simp

private theorem GP017B1b_population :
    Measurable slowEffect ∧ Integrable slowEffect slowPopulation ∧
    populationMean slowPopulation slowEffect = 0 ∧
    effectSupport slowPopulation slowEffect = Icc (-1) 1 ∧
    effectRadius slowPopulation slowEffect = 1 := by
  have hm : Measurable slowEffect := by
    unfold slowEffect slowY1 slowY0; fun_prop
  have hiL : Integrable (fun x : ℝ => x) ((1 / 4 : ℝ≥0∞) • Measure.dirac (-1)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have hiU : Integrable (fun x : ℝ => x) ((1 / 4 : ℝ≥0∞) • Measure.dirac 1) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have hiC : Integrable (fun x : ℝ => x)
      ((1 / 4 : ℝ≥0∞) • volume.restrict (Icc (-1) 1)) :=
    (show Integrable (fun x : ℝ => x) (volume.restrict (Icc (-1) 1)) from
      continuous_id.integrableOn_Icc).smul_measure (by norm_num)
  have hi : Integrable (fun x : ℝ => x) slowEffectLaw :=
    (hiL.add_measure hiU).add_measure hiC
  have hzero : (∫ x in Icc (-1 : ℝ) 1, x) = 0 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      integral_id]
    norm_num
  have hmean : (∫ x : ℝ, x ∂slowEffectLaw) = 0 := by
    rw [slowEffectLaw, integral_add_measure (hiL.add_measure hiU) hiC,
      integral_add_measure hiL hiU]
    norm_num [integral_smul_measure, hzero]
  have hsupp : slowEffectLaw.support = Icc (-1) 1 := by
    apply Set.Subset.antisymm
    · apply Measure.support_subset_of_isClosed isClosed_Icc
      change ∀ᵐ x ∂slowEffectLaw, x ∈ Icc (-1) 1
      simp only [slowEffectLaw, ae_add_measure_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Measure.ae_smul_measure (by simp) _
      · exact Measure.ae_smul_measure (by simp) _
      · exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
    · have hsub : Ioo (-1 : ℝ) 1 ⊆ slowEffectLaw.support := by
        intro x hx
        have hxC : x ∈ (volume.restrict (Icc (-1 : ℝ) 1)).support :=
          Measure.interior_inter_support ⟨by simpa only [interior_Icc] using hx,
            by simp only [Measure.support_eq_univ, mem_univ]⟩
        apply (Measure.mem_support_iff_forall x).mpr
        intro U hU
        have hpos := (Measure.mem_support_iff_forall x).mp hxC U hU
        simp only [slowEffectLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
        exact lt_of_lt_of_le (ENNReal.mul_pos (by norm_num) hpos.ne')
          (le_add_of_nonneg_left zero_le)
      simpa only [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] using
        (closure_minimal hsub Measure.isClosed_support)
  have hmean' : populationMean slowPopulation slowEffect = 0 := by
    unfold populationMean
    calc
      _ = ∫ x : ℝ, x ∂slowPopulation.map slowEffect :=
        (integral_map hm.aemeasurable measurable_id.aestronglyMeasurable).symm
      _ = 0 := by rw [GP017B1b_effect_law, hmean]
  have hsupp' : effectSupport slowPopulation slowEffect = Icc (-1) 1 := by
    rw [effectSupport, GP017B1b_effect_law, hsupp]
  refine ⟨hm, ?_, hmean', hsupp', ?_⟩
  · have hi' : Integrable (fun x : ℝ => x) (slowPopulation.map slowEffect) :=
      GP017B1b_effect_law.symm ▸ hi
    exact hi'.comp_measurable hm
  · have he : ((-1 : ℝ) : EReal) ≤ ((1 : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr (by norm_num)
    have hsup : supportSup (Icc (-1 : ℝ) 1) = ((1 : ℝ) : EReal) := by
      rw [supportSup, EReal.image_coe_Icc, csSup_Icc he]
    have hinf : supportInf (Icc (-1 : ℝ) 1) = ((-1 : ℝ) : EReal) := by
      rw [supportInf, EReal.image_coe_Icc, csInf_Icc he]
    simp only [effectRadius, hsupp', hmean', hsup, hinf, EReal.coe_zero, sub_zero, zero_sub,
      EReal.coe_neg, EReal.coe_one, neg_neg, min_self]
    change ((1 : ℝ) : EReal).toENNReal = 1
    exact (EReal.real_coe_toENNReal 1).trans ENNReal.ofReal_one

private theorem GP017B1b_mean_measurable (n : ℕ) : Measurable (smallNormalMean n) := by
  unfold smallNormalMean sampleMean
  fun_prop

/-- Exact finite Gaussian law of the sample mean for every positive sample size. -/
private theorem GP017B1b_mean_law (n : ℕ) (hn : 1 ≤ n) :
    (iidSamples slowPopulation).map (smallNormalMean n) =
      gaussianReal 0 (1 / (n : ℝ≥0)) := by
  let P := iidSamples slowPopulation
  let X : ℕ → (ℕ → ℝ × (ℝ × (ℝ × ℝ))) → ℝ := fun i s => (s i).1
  have hm (i : ℕ) : Measurable (X i) := measurable_fst.comp (measurable_pi_apply i)
  have hcoord (i : ℕ) : HasLaw (X i) (gaussianReal 0 1) P := by
    refine ⟨(hm i).aemeasurable, ?_⟩
    change (Measure.infinitePi (fun _ : ℕ => slowPopulation)).map
      ((Prod.fst : ℝ × (ℝ × (ℝ × ℝ)) → ℝ) ∘ (fun s => s i)) = _
    rw [← Measure.map_map measurable_fst (measurable_pi_apply i), Measure.infinitePi_map_eval]
    simp [slowPopulation, Measure.map_fst_prod]
  have hind : iIndepFun X P :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (Prod.fst : ℝ × (ℝ × (ℝ × ℝ)) → ℝ)) (fun _ => measurable_fst)
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
  change P.map (smallNormalMean n) = _
  rw [show smallNormalMean n = (fun s => (∑ i ∈ Finset.range n, X i s) / (n : ℝ)) from rfl]
  rw [hscaled.map_eq]
  simp only [zero_div]
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_natCast, NNReal.coe_one]
  field_simp [hnR.ne']
  <;> ring

private theorem GP017B1b_scaled_mean_law (n : ℕ) (hn : 1 ≤ n) :
    (iidSamples slowPopulation).map (fun s => sqrtN n * smallNormalMean n s) = gaussianReal 0 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs2 : sqrtN n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  change (iidSamples slowPopulation).map
    ((fun x : ℝ => sqrtN n * x) ∘ smallNormalMean n) = _
  rw [← Measure.map_map (by fun_prop) (GP017B1b_mean_measurable n),
    GP017B1b_mean_law n hn, gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, NNReal.coe_div, NNReal.coe_natCast]
  rw [hs2]
  field_simp [hnR.ne']

private theorem GP017B1b_mean_second (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun s => smallNormalMean n s ^ 2) (iidSamples slowPopulation) ∧
    (∫ s, smallNormalMean n s ^ 2 ∂iidSamples slowPopulation) = 1 / (n : ℝ) := by
  have hi : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 (1 / (n : ℝ≥0))) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hi' : Integrable (fun x : ℝ => x ^ 2)
      ((iidSamples slowPopulation).map (smallNormalMean n)) :=
    (GP017B1b_mean_law n hn).symm ▸ hi
  refine ⟨hi'.comp_measurable (GP017B1b_mean_measurable n), ?_⟩
  rw [← integral_map (f := fun x : ℝ => x ^ 2) (GP017B1b_mean_measurable n).aemeasurable (by fun_prop),
    GP017B1b_mean_law n hn]
  have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (1 / (n : ℝ≥0)))
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hv
  simpa only [sub_zero, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast] using hv

private theorem GP017B1b_mean_tail (n : ℕ) (hn : 1 ≤ n) :
    pr (iidSamples slowPopulation) {s | 1 / 2 < |smallNormalMean n s|} ≤ 4 / (n : ℝ) := by
  let Q := iidSamples slowPopulation
  let C := {s : ℕ → ℝ × (ℝ × (ℝ × ℝ)) | 1 / 2 < |smallNormalMean n s|}
  have hmC : MeasurableSet C := measurableSet_lt measurable_const
    (by simpa only [Real.norm_eq_abs] using (GP017B1b_mean_measurable n).norm)
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
  have hh := integral_mono hi (GP017B1b_mean_second n hn).1 hp
  rw [(GP017B1b_mean_second n hn).2] at hh
  simp only [integral_indicator_const _ hmC, smul_eq_mul] at hh
  change pr Q C ≤ _
  unfold pr
  calc
    Q.real C ≤ 4 * (1 / (n : ℝ)) := by linarith
    _ = 4 / (n : ℝ) := by ring

private theorem GP017B1b_flag_measurable (p : ℕ → ℝ) (n : ℕ) :
    Measurable (rareFlag p n) := by
  exact measurable_const.ite
    (measurableSet_lt (GP017B1b_uniform_measurable n) measurable_const) measurable_const

private theorem GP017B1b_clip_measurable (n : ℕ) : Measurable (smallNormalClip n) := by
  unfold smallNormalClip clipReal
  exact measurable_const.min (measurable_const.max (GP017B1b_mean_measurable n))

private theorem GP017B1b_estimator_measurable (p : ℕ → ℝ) (n : ℕ) :
    Measurable (rareEstimator p n) := by
  exact (GP017B1b_clip_measurable n).add (measurable_const.mul (GP017B1b_flag_measurable p n))

private theorem GP017B1b_flag_probability (p : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hp : 0 < p n ∧ p n ≤ 1) :
    pr (iidSamples slowPopulation) {s | rareFlag p n s = 1} = p n := by
  have hset : {s | rareFlag p n s = 1} = (rareUniform n) ⁻¹' Iio (p n) := by
    ext s; simp [rareFlag]
  have hint : Iio (p n) ∩ Ico (0 : ℝ) 1 = Ico 0 (p n) := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ico]
    constructor
    · rintro ⟨hxp, hx0, hx1⟩; exact ⟨hx0, hxp⟩
    · rintro ⟨hx0, hxp⟩; exact ⟨hxp, hx0, lt_of_lt_of_le hxp hp.2⟩
  rw [pr, hset, ← map_measureReal_apply (GP017B1b_uniform_measurable n) measurableSet_Iio,
    GP017B1b_uniform_law n hn, Measure.real, uniformHalfOpen01,
    Measure.restrict_apply measurableSet_Iio, hint, Real.volume_Ico, sub_zero,
    ENNReal.toReal_ofReal hp.1.le]

private theorem GP017B1b_failure_set (p : ℕ → ℝ) (n : ℕ) :
    {s | rareEstimator p n s ≠ clipReal 0 1 (rareEstimator p n s)} =
      {s | rareFlag p n s = 1} := by
  ext s
  have hf := rare_estimator_finite (smallNormalMean n s)
  change _ ≠ _ ↔ _
  by_cases h : rareUniform n s < p n
  · simp only [rareEstimator, rareFlag, h, ↓reduceIte, mul_one, mem_setOf_eq]
    change smallNormalClip n s + 10 ≠ clipReal 0 1 (smallNormalClip n s + 10) ↔ True
    rw [show clipReal 0 1 (smallNormalClip n s + 10) = 1 from hf.2.2.2.1]
    have hlo : (19 / 2 : ℝ) ≤ smallNormalClip n s + 10 := hf.2.1
    constructor
    · intro; trivial
    · intro; linarith
  · simp only [rareEstimator, rareFlag, h, ↓reduceIte, mul_zero, add_zero, mem_setOf_eq]
    change smallNormalClip n s ≠ clipReal 0 1 (smallNormalClip n s) ↔ (0 : ℝ) = 1
    rw [show clipReal 0 1 (smallNormalClip n s) = smallNormalClip n s from hf.1]
    norm_num

private theorem GP017B1b_failure_probability (p : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hp : 0 < p n ∧ p n ≤ 1) :
    pr (iidSamples slowPopulation)
      {s | rareEstimator p n s ≠ clipReal 0 1 (rareEstimator p n s)} = p n := by
  rw [GP017B1b_failure_set, GP017B1b_flag_probability p n hn hp]


private theorem GP017B1b_clip_self (n : ℕ) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ)))
    (hs : |smallNormalMean n s| ≤ 1 / 2) :
    smallNormalClip n s = smallNormalMean n s := by
  exact (clipReal_eq_self_iff 0 (1 / 2) _ (by norm_num)).mpr (by simpa only [sub_zero] using hs)

private theorem GP017B1b_flag_zero (p : ℕ → ℝ) (n : ℕ)
    (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) (hs : rareFlag p n s ≠ 1) : rareFlag p n s = 0 := by
  unfold rareFlag at *
  split_ifs at * <;> simp_all

private theorem GP017B1b_rootN (p : ℕ → ℝ)
    (hp : ∀ n : ℕ, 1 ≤ n → 0 < p n ∧ p n ≤ 1) (hplim : Tendsto p atTop (𝓝 0)) :
    RootNNormal (iidSamples slowPopulation) (rareEstimator p) 0 := by
  let Q := iidSamples slowPopulation
  let X := fun n s => sqrtN n * smallNormalMean n s
  let Y := fun n s => sqrtN n * (rareEstimator p n s - 0)
  have hX : TendstoInDistribution X atTop (fun z : ℝ => z) (fun _ => Q) (gaussianReal 0 1) := by
    refine ⟨fun n => (measurable_const.mul (GP017B1b_mean_measurable n)).aemeasurable,
      measurable_id.aemeasurable, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    apply ProbabilityMeasure.toMeasure_injective
    change (gaussianReal 0 1).map id = Q.map (X n)
    rw [Measure.map_id]
    exact (GP017B1b_scaled_mean_law n hn).symm
  have hlim : Tendsto (fun n : ℕ => 4 / (n : ℝ) + p n) atTop (𝓝 0) := by
    have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa only [div_eq_mul_inv, mul_zero, zero_add] using (hi.const_mul 4).add hplim
  have hdiff : TendstoInMeasure Q (Y - X) atTop 0 := by
    rw [tendstoInMeasure_iff_measureReal_norm]
    intro ε hε
    apply squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) _ hlim
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hsub : {s | ε ≤ ‖(Y - X) n s - (0 : (ℕ → ℝ × (ℝ × (ℝ × ℝ))) → ℝ) s‖} ⊆
        {s | 1 / 2 < |smallNormalMean n s|} ∪ {s | rareFlag p n s = 1} := by
      intro s hs
      by_contra hnot
      have hnot' : ¬ 1 / 2 < |smallNormalMean n s| ∧ rareFlag p n s ≠ 1 := by
        simpa only [mem_union, mem_setOf_eq, not_or] using hnot
      have hc := GP017B1b_clip_self n s (le_of_not_gt hnot'.1)
      have hb := GP017B1b_flag_zero p n s hnot'.2
      have hz : (Y - X) n s = 0 := by
        dsimp [Y, X, rareEstimator]
        rw [hc, hb]
        ring
      simp only [mem_setOf_eq, hz, Pi.zero_apply, sub_zero, norm_zero] at hs
      linarith
    calc
      _ ≤ Q.real ({s | 1 / 2 < |smallNormalMean n s|} ∪ {s | rareFlag p n s = 1}) :=
        measureReal_mono hsub
      _ ≤ Q.real {s | 1 / 2 < |smallNormalMean n s|} + Q.real {s | rareFlag p n s = 1} :=
        measureReal_union_le _ _
      _ ≤ 4 / (n : ℝ) + p n := by
        exact add_le_add (GP017B1b_mean_tail n hn)
          (GP017B1b_flag_probability p n hn (hp n hn)).le
  refine ⟨1, by norm_num, ?_⟩
  exact tendstoInDistribution_of_tendstoInMeasure_sub Y (fun z : ℝ => z) hX hdiff
    (fun n => (measurable_const.mul ((GP017B1b_estimator_measurable p n).sub measurable_const)).aemeasurable)

private theorem GP017B1b_remainder_integrable (p : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun s => rareRemainder p n s ^ 2) (iidSamples slowPopulation) := by
  have hm : MemLp (smallNormalMean n) 2 (iidSamples slowPopulation) :=
    (memLp_two_iff_integrable_sq (GP017B1b_mean_measurable n).aestronglyMeasurable).mpr
      (GP017B1b_mean_second n hn).1
  have hc : MemLp (smallNormalClip n) 2 (iidSamples slowPopulation) := by
    apply MemLp.of_bound (GP017B1b_clip_measurable n).aestronglyMeasurable (1 / 2)
    apply ae_of_all
    intro s
    have hb := clipReal_bounds 0 (1 / 2) (smallNormalMean n s) (by norm_num)
    change |clipReal 0 (1 / 2) (smallNormalMean n s)| ≤ 1 / 2
    exact abs_le.mpr ⟨by simpa only [zero_sub] using hb.1, by simpa only [zero_add] using hb.2⟩
  have hb : MemLp (rareFlag p n) 2 (iidSamples slowPopulation) := by
    apply MemLp.of_bound (GP017B1b_flag_measurable p n).aestronglyMeasurable 1
    apply ae_of_all
    intro s
    simp only [rareFlag]
    split_ifs <;> norm_num
  exact (((hc.sub hm).add (hb.const_mul 10)).const_mul (sqrtN n)).integrable_sq

/-- A sufficient lower bound uses only the union bound for the central Gaussian
region and the flag event. -/
private theorem GP017B1b_remainder_lower (p : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hp : 0 < p n ∧ p n ≤ 1) :
    100 * (n : ℝ) * p n - 400 ≤
      ∫ s, rareRemainder p n s ^ 2 ∂iidSamples slowPopulation := by
  let Q := iidSamples slowPopulation
  let E := {s | rareFlag p n s = 1 ∧ |smallNormalMean n s| ≤ 1 / 2}
  let T := {s | 1 / 2 < |smallNormalMean n s|}
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmE : MeasurableSet E :=
    (measurableSet_eq_fun (GP017B1b_flag_measurable p n) measurable_const).inter
      (measurableSet_le (by simpa only [Real.norm_eq_abs] using (GP017B1b_mean_measurable n).norm) measurable_const)
  have hprob : p n ≤ Q.real E + 4 / (n : ℝ) := by
    calc
      p n = Q.real {s | rareFlag p n s = 1} := (GP017B1b_flag_probability p n hn hp).symm
      _ ≤ Q.real (E ∪ T) := by
        refine measureReal_mono ?_ (measure_ne_top _ _)
        intro s hs
        by_cases h : |smallNormalMean n s| ≤ 1 / 2
        · exact Or.inl ⟨hs, h⟩
        · exact Or.inr (lt_of_not_ge h)
      _ ≤ Q.real E + Q.real T := measureReal_union_le _ _
      _ ≤ Q.real E + 4 / (n : ℝ) := add_le_add le_rfl (GP017B1b_mean_tail n hn)
  have hpoint (s) : E.indicator (fun _ => 100 * (n : ℝ)) s ≤ rareRemainder p n s ^ 2 := by
    by_cases hs : s ∈ E
    · rw [Set.indicator_of_mem hs]
      have hc := GP017B1b_clip_self n s hs.2
      simp only [rareRemainder, hc, hs.1, sub_self, zero_add, mul_one, mul_pow, sqrtN,
        Real.sq_sqrt (Nat.cast_nonneg n)]
      norm_num <;> nlinarith
    · rw [Set.indicator_of_notMem hs]
      exact sq_nonneg _
  have hi := integral_mono ((integrable_const (100 * (n : ℝ))).indicator hmE)
    (GP017B1b_remainder_integrable p n hn) hpoint
  rw [integral_indicator_const _ hmE] at hi
  simp only [smul_eq_mul] at hi
  have hmul := mul_le_mul_of_nonneg_left hprob (show 0 ≤ 100 * (n : ℝ) by positivity)
  have hcancel : 100 * (n : ℝ) * (4 / (n : ℝ)) = 400 := by
    field_simp [hnR.ne']
    <;> ring
  rw [mul_add, hcancel] at hmul
  nlinarith

private theorem GP017B1b_dyadic_cofinal :
    Tendsto (fun k : ℕ => 2 ^ k) atTop atTop := by
  exact tendsto_atTop_mono (fun k => (Nat.lt_two_pow_self (n := k)).le) tendsto_id

private theorem GP017B1b_dyadic_growth (α : ℝ) (hα : 0 < α) :
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

private theorem GP017B1b_no_polynomial (α : ℝ) (hα : 0 < α) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, slowP n ≤ C / (n : ℝ) ^ α := by
  rintro ⟨C, hC, hbound⟩
  have hsub := GP017B1b_dyadic_cofinal.eventually hbound
  have hgrowth := (GP017B1b_dyadic_growth α hα).eventually
    (eventually_gt_atTop C)
  obtain ⟨k, hk, hkg⟩ := (hsub.and hgrowth).exists
  have hpos : 0 < ((2 ^ k : ℕ) : ℝ) ^ α := by positivity
  have hupper : ((2 ^ k : ℕ) : ℝ) ^ α * slowP (2 ^ k) ≤ C := by
    have hb := (le_div_iff₀ hpos).mp hk
    nlinarith
  linarith

/-- A concrete positive sequence that is slower than any specified positive null
sequence. The value at zero does not require positivity of the specified rate. -/
private theorem GP017B1b_slower_rate (r : ℕ → ℝ)
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
    change (Real.sqrt (r n))⁻¹ = p n / r n
    rw [hpval]
    have hsquare := Real.sq_sqrt hrpos.le
    field_simp [ne_of_gt hrpos, ne_of_gt hspos]
    nlinarith
  exact ⟨p, hp, hplim, hratio⟩

private theorem GP017B1b_not_small :
    ¬ SmallRemainderMS (iidSamples slowPopulation) (rareRemainder slowP) := by
  intro hsmall
  let E : ℕ → ℝ := fun n => ∫ s, rareRemainder slowP n s ^ 2 ∂iidSamples slowPopulation
  have hE (n : ℕ) : 0 ≤ E n := integral_nonneg (fun s => sq_nonneg _)
  change Tendsto (fun n => sqrtN n * E n) atTop (𝓝 0) at hsmall
  have hlow : ∀ᶠ n : ℕ in atTop,
      100 * (n : ℝ) * slowP n - 400 ≤ sqrtN n * E n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hroot : 1 ≤ sqrtN n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
    have hb := GP017B1b_remainder_lower slowP n hn (slow_probability_positive_limit.1 n)
    have hmul : E n ≤ sqrtN n * E n := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hroot (hE n)
    exact hb.trans hmul
  have hdyadic : Tendsto (fun k : ℕ =>
      100 * ((2 ^ k : ℕ) : ℝ) * slowP (2 ^ k)) atTop atTop := by
    have h := Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 100)
      (GP017B1b_dyadic_growth 1 (by norm_num))
    simpa only [Real.rpow_one, mul_assoc] using h
  have hlarge := hdyadic.eventually (eventually_gt_atTop (401 : ℝ))
  have hupper := (hsmall.comp GP017B1b_dyadic_cofinal).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hlower' := GP017B1b_dyadic_cofinal.eventually hlow
  obtain ⟨k, hk₁, hk₂, hk₃⟩ := (hlarge.and (hupper.and hlower')).exists
  change sqrtN (2 ^ k) * E (2 ^ k) < 1 at hk₂
  linarith

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
  have hp : ∀ n : ℕ, 1 ≤ n → 0 < slowP n ∧ slowP n ≤ 1 :=
    fun n _ => slow_probability_positive_limit.1 n
  have hlim := slow_probability_positive_limit.2
  rcases GP017B1b_population with ⟨hm, hi, hmean, hsupp, hrad⟩
  refine ⟨hp, hlim, GP017B1b_rootN slowP hp hlim, hm, hi, hmean, hsupp, hrad,
    (fun n hn => GP017B1b_failure_probability slowP n hn (hp n hn)),
    slow_probability_numbers.1, slow_probability_numbers.2.1,
    slow_probability_numbers.2.2, GP017B1b_dyadic_growth,
    GP017B1b_no_polynomial, GP017B1b_not_small, ?_⟩
  intro r hr hrlim
  obtain ⟨p, hp', hplim, hratio⟩ := GP017B1b_slower_rate r hr hrlim
  exact ⟨p, hp', hplim, GP017B1b_rootN p hp' hplim,
    (fun n hn => GP017B1b_failure_probability p n hn (hp' n hn)), hratio⟩

end
end AronowAudit.P017.Wave1
