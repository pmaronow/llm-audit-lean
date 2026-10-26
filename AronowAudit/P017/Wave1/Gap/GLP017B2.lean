import AronowAudit.P017.P017_Audit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.Independence.InfinitePi

/-!
The prescribed rare-outlier sequence. The fractional sum uses Haar measure on
the unit circle.
-/

namespace AronowAudit.P017.Wave1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

private theorem arbitrary_outlier_sequence_circle_law :
    uniformHalfOpen01.map (fun x : ℝ => (x : AddCircle (1 : ℝ))) = volume := by
  simpa only [uniformHalfOpen01, restrict_Ico_eq_restrict_Ioc, zero_add] using
    (AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq

private def arbitrary_outlier_sequence_rep (z : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.measurableEquivIco (1 : ℝ) 0 z : ℝ)

private theorem arbitrary_outlier_sequence_rep_measurable : Measurable arbitrary_outlier_sequence_rep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

private theorem arbitrary_outlier_sequence_rep_coe (x : ℝ) :
    arbitrary_outlier_sequence_rep (x : AddCircle (1 : ℝ)) = Int.fract x := by
  change (AddCircle.equivIco (1 : ℝ) 0 (x : AddCircle (1 : ℝ)) : ℝ) = _
  simpa only [div_one, mul_one] using AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) x

private theorem arbitrary_outlier_sequence_rep_law :
    (volume : Measure (AddCircle (1 : ℝ))).map arbitrary_outlier_sequence_rep = uniformHalfOpen01 := by
  rw [← arbitrary_outlier_sequence_circle_law,
    Measure.map_map arbitrary_outlier_sequence_rep_measurable AddCircle.measurable_mk']
  have heq : (fun x : ℝ => arbitrary_outlier_sequence_rep (x : AddCircle (1 : ℝ)))
      =ᵐ[uniformHalfOpen01] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    rw [arbitrary_outlier_sequence_rep_coe]
    exact Int.fract_eq_self.mpr hx
  change uniformHalfOpen01.map (fun x : ℝ => arbitrary_outlier_sequence_rep (x : AddCircle (1 : ℝ))) = _
  rw [Measure.map_congr heq, Measure.map_id]

private theorem arbitrary_outlier_sequence_uniform_measurable (n : ℕ) : Measurable (rareUniform n) := by
  unfold rareUniform
  exact measurable_fract.comp (by fun_prop)

private theorem arbitrary_outlier_sequence_uniform_law (n : ℕ) (hn : 1 ≤ n) :
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
    rw [hc, arbitrary_outlier_sequence_circle_law]
  have hind : iIndepFun X Q :=
    iIndepFun_infinitePi
      (X := fun _ : ℕ => fun w : ℝ × (ℝ × (ℝ × ℝ)) => (w.2.1 : AddCircle (1 : ℝ)))
      (fun _ => by fun_prop)
  have arbitrary_outlier_sequence_circleProbability : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
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
  have heq : rareUniform (k + 1) = arbitrary_outlier_sequence_rep ∘
      (fun s => ∑ i ∈ Finset.range (k + 1), X i s) := by
    funext s
    rw [Function.comp_apply]
    have hc : (∑ i ∈ Finset.range (k + 1), X i s) =
        ((∑ i ∈ Finset.range (k + 1), (s i).2.1 : ℝ) : AddCircle (1 : ℝ)) := by
      exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _).symm
    rw [hc, arbitrary_outlier_sequence_rep_coe]
    rfl
  rw [heq, ← Measure.map_map arbitrary_outlier_sequence_rep_measurable (by fun_prop), hsum', arbitrary_outlier_sequence_rep_law]


private theorem arbitrary_outlier_sequence_effect_law :
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

private theorem arbitrary_outlier_sequence_population :
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
      _ = 0 := by rw [arbitrary_outlier_sequence_effect_law, hmean]
  have hsupp' : effectSupport slowPopulation slowEffect = Icc (-1) 1 := by
    rw [effectSupport, arbitrary_outlier_sequence_effect_law, hsupp]
  refine ⟨hm, ?_, hmean', hsupp', ?_⟩
  · have hi' : Integrable (fun x : ℝ => x) (slowPopulation.map slowEffect) :=
      arbitrary_outlier_sequence_effect_law.symm ▸ hi
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

private theorem arbitrary_outlier_sequence_mean_measurable (n : ℕ) : Measurable (smallNormalMean n) := by
  unfold smallNormalMean sampleMean
  fun_prop

/-- Exact finite Gaussian law, including zero for the unnormalized empty sum. -/
private theorem arbitrary_outlier_sequence_mean_law (n : ℕ) (hn : 1 ≤ n) :
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

private theorem arbitrary_outlier_sequence_scaled_mean_law (n : ℕ) (hn : 1 ≤ n) :
    (iidSamples slowPopulation).map (fun s => sqrtN n * smallNormalMean n s) = gaussianReal 0 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs2 : sqrtN n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  change (iidSamples slowPopulation).map
    ((fun x : ℝ => sqrtN n * x) ∘ smallNormalMean n) = _
  rw [← Measure.map_map (by fun_prop) (arbitrary_outlier_sequence_mean_measurable n),
    arbitrary_outlier_sequence_mean_law n hn, gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, NNReal.coe_div, NNReal.coe_natCast]
  rw [hs2]
  field_simp [hnR.ne']

private theorem arbitrary_outlier_sequence_mean_second (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun s => smallNormalMean n s ^ 2) (iidSamples slowPopulation) ∧
    (∫ s, smallNormalMean n s ^ 2 ∂iidSamples slowPopulation) = 1 / (n : ℝ) := by
  have hi : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 (1 / (n : ℝ≥0))) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hi' : Integrable (fun x : ℝ => x ^ 2)
      ((iidSamples slowPopulation).map (smallNormalMean n)) :=
    (arbitrary_outlier_sequence_mean_law n hn).symm ▸ hi
  refine ⟨hi'.comp_measurable (arbitrary_outlier_sequence_mean_measurable n), ?_⟩
  rw [← integral_map (f := fun x : ℝ => x ^ 2) (arbitrary_outlier_sequence_mean_measurable n).aemeasurable (by fun_prop),
    arbitrary_outlier_sequence_mean_law n hn]
  have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (1 / (n : ℝ≥0)))
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hv
  simpa only [sub_zero, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast] using hv

private theorem arbitrary_outlier_sequence_mean_tail (n : ℕ) (hn : 1 ≤ n) :
    pr (iidSamples slowPopulation) {s | 1 / 2 < |smallNormalMean n s|} ≤ 4 / (n : ℝ) := by
  let Q := iidSamples slowPopulation
  let C := {s : ℕ → ℝ × (ℝ × (ℝ × ℝ)) | 1 / 2 < |smallNormalMean n s|}
  have hmC : MeasurableSet C := measurableSet_lt measurable_const
    (by simpa only [Real.norm_eq_abs] using (arbitrary_outlier_sequence_mean_measurable n).norm)
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
  have hh := integral_mono hi (arbitrary_outlier_sequence_mean_second n hn).1 hp
  rw [(arbitrary_outlier_sequence_mean_second n hn).2] at hh
  simp only [integral_indicator_const _ hmC, smul_eq_mul] at hh
  change pr Q C ≤ _
  unfold pr
  calc
    Q.real C ≤ 4 * (1 / (n : ℝ)) := by linarith
    _ = 4 / (n : ℝ) := by ring

private theorem arbitrary_outlier_sequence_flag_measurable (p : ℕ → ℝ) (n : ℕ) :
    Measurable (rareFlag p n) := by
  exact measurable_const.ite
    (measurableSet_lt (arbitrary_outlier_sequence_uniform_measurable n) measurable_const) measurable_const

private theorem arbitrary_outlier_sequence_clip_measurable (n : ℕ) : Measurable (smallNormalClip n) := by
  unfold smallNormalClip clipReal
  exact measurable_const.min (measurable_const.max (arbitrary_outlier_sequence_mean_measurable n))

private theorem arbitrary_outlier_sequence_estimator_measurable (p : ℕ → ℝ) (n : ℕ) :
    Measurable (rareEstimator p n) := by
  exact (arbitrary_outlier_sequence_clip_measurable n).add (measurable_const.mul (arbitrary_outlier_sequence_flag_measurable p n))

private theorem arbitrary_outlier_sequence_flag_probability (p : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
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
  rw [pr, hset, ← map_measureReal_apply (arbitrary_outlier_sequence_uniform_measurable n) measurableSet_Iio,
    arbitrary_outlier_sequence_uniform_law n hn, Measure.real, uniformHalfOpen01,
    Measure.restrict_apply measurableSet_Iio, hint, Real.volume_Ico, sub_zero,
    ENNReal.toReal_ofReal hp.1.le]

private theorem arbitrary_outlier_sequence_failure_set (p : ℕ → ℝ) (n : ℕ) :
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

private theorem arbitrary_outlier_sequence_failure_probability (p : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hp : 0 < p n ∧ p n ≤ 1) :
    pr (iidSamples slowPopulation)
      {s | rareEstimator p n s ≠ clipReal 0 1 (rareEstimator p n s)} = p n := by
  rw [arbitrary_outlier_sequence_failure_set, arbitrary_outlier_sequence_flag_probability p n hn hp]


private theorem arbitrary_outlier_sequence_clip_self (n : ℕ) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ)))
    (hs : |smallNormalMean n s| ≤ 1 / 2) :
    smallNormalClip n s = smallNormalMean n s := by
  exact (clipReal_eq_self_iff 0 (1 / 2) _ (by norm_num)).mpr (by simpa only [sub_zero] using hs)

private theorem arbitrary_outlier_sequence_flag_zero (p : ℕ → ℝ) (n : ℕ)
    (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) (hs : rareFlag p n s ≠ 1) : rareFlag p n s = 0 := by
  unfold rareFlag at *
  split_ifs at * <;> simp_all

private theorem arbitrary_outlier_sequence_rootN (p : ℕ → ℝ)
    (hp : ∀ n : ℕ, 1 ≤ n → 0 < p n ∧ p n ≤ 1) (hplim : Tendsto p atTop (𝓝 0)) :
    RootNNormal (iidSamples slowPopulation) (rareEstimator p) 0 := by
  let Q := iidSamples slowPopulation
  let X := fun n s => sqrtN n * smallNormalMean n s
  let Y := fun n s => sqrtN n * (rareEstimator p n s - 0)
  have hX : TendstoInDistribution X atTop (fun z : ℝ => z) (fun _ => Q) (gaussianReal 0 1) := by
    refine ⟨fun n => (measurable_const.mul (arbitrary_outlier_sequence_mean_measurable n)).aemeasurable,
      measurable_id.aemeasurable, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    apply ProbabilityMeasure.toMeasure_injective
    change (gaussianReal 0 1).map id = Q.map (X n)
    rw [Measure.map_id]
    exact (arbitrary_outlier_sequence_scaled_mean_law n hn).symm
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
      have hc := arbitrary_outlier_sequence_clip_self n s (le_of_not_gt hnot'.1)
      have hb := arbitrary_outlier_sequence_flag_zero p n s hnot'.2
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
        exact add_le_add (arbitrary_outlier_sequence_mean_tail n hn)
          (arbitrary_outlier_sequence_flag_probability p n hn (hp n hn)).le
  refine ⟨1, by norm_num, ?_⟩
  exact tendstoInDistribution_of_tendstoInMeasure_sub Y (fun z : ℝ => z) hX hdiff
    (fun n => (measurable_const.mul ((arbitrary_outlier_sequence_estimator_measurable p n).sub measurable_const)).aemeasurable)

private theorem arbitrary_outlier_sequence_remainder_integrable (p : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun s => rareRemainder p n s ^ 2) (iidSamples slowPopulation) := by
  have hm : MemLp (smallNormalMean n) 2 (iidSamples slowPopulation) :=
    (memLp_two_iff_integrable_sq (arbitrary_outlier_sequence_mean_measurable n).aestronglyMeasurable).mpr
      (arbitrary_outlier_sequence_mean_second n hn).1
  have hc : MemLp (smallNormalClip n) 2 (iidSamples slowPopulation) := by
    apply MemLp.of_bound (arbitrary_outlier_sequence_clip_measurable n).aestronglyMeasurable (1 / 2)
    apply ae_of_all
    intro s
    have hb := clipReal_bounds 0 (1 / 2) (smallNormalMean n s) (by norm_num)
    change |clipReal 0 (1 / 2) (smallNormalMean n s)| ≤ 1 / 2
    exact abs_le.mpr ⟨by simpa only [zero_sub] using hb.1, by simpa only [zero_add] using hb.2⟩
  have hb : MemLp (rareFlag p n) 2 (iidSamples slowPopulation) := by
    apply MemLp.of_bound (arbitrary_outlier_sequence_flag_measurable p n).aestronglyMeasurable 1
    apply ae_of_all
    intro s
    simp only [rareFlag]
    split_ifs <;> norm_num
  exact (((hc.sub hm).add (hb.const_mul 10)).const_mul (sqrtN n)).integrable_sq


/-- Pull independence back through a measurable map with the specified law. -/
private theorem arbitrary_outlier_sequence_indep_pullback {Ω Ξ α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) (Q : Measure Ξ) (T : Ω → Ξ) (hT : Measurable T)
    (hlaw : P.map T = Q) (f : Ξ → α) (g : Ξ → β)
    (hf : Measurable f) (hg : Measurable g) (hi : IndepFun f g Q) :
    IndepFun (f ∘ T) (g ∘ T) P := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hi ⊢
  intro A B hA hB
  have h := hi A B hA hB
  rw [← hlaw, Measure.map_apply hT ((hf hA).inter (hg hB)),
    Measure.map_apply hT (hf hA), Measure.map_apply hT (hg hB)] at h
  exact h

/-- The entire normal-coordinate vector is independent of the entire vector
of the other coordinates, by regrouping the actual finite product law. -/
private theorem arbitrary_outlier_sequence_flag_independent (p : ℕ → ℝ) (n : ℕ) :
    IndepFun (rareFlag p n) (smallNormalMean n) (iidSamples slowPopulation) := by
  let Q := iidSamples slowPopulation
  let R : (ℕ → ℝ × (ℝ × (ℝ × ℝ))) → (Fin n → ℝ × (ℝ × (ℝ × ℝ))) :=
    fun s i => s i
  let T : (ℕ → ℝ × (ℝ × (ℝ × ℝ))) →
      (Fin n → ℝ) × (Fin n → ℝ × (ℝ × ℝ)) :=
    fun s => (fun i => (s i).1, fun i => (s i).2)
  let ν := uniformHalfOpen01.prod (slowEffectLaw.prod (fairPair 0 1))
  have hR : Q.map R = Measure.pi (fun _ : Fin n => slowPopulation) := by
    have hi : iIndepFun (fun (i : Fin n) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) => s i) Q :=
      (iIndepFun_infinitePi (X := fun _ : ℕ => id) (fun _ => measurable_id)).precomp
        Fin.val_injective
    have h := hi.map_fun_eq_pi_map (fun (i : Fin n) => (measurable_pi_apply (i : ℕ)).aemeasurable)
    simpa only [Q, R, iidSamples, Measure.infinitePi_map_eval] using h
  have hT : Measurable T := by fun_prop
  have hlaw : Q.map T = (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).prod
      (Measure.pi (fun _ : Fin n => ν)) := by
    change Q.map ((MeasurableEquiv.arrowProdEquivProdArrow ℝ (ℝ × (ℝ × ℝ)) (Fin n)) ∘ R) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop), hR]
    exact (measurePreserving_arrowProdEquivProdArrow ℝ (ℝ × (ℝ × ℝ)) (Fin n)
      (fun _ => gaussianReal 0 1) (fun _ => ν)).map_eq
  let f : (Fin n → ℝ) → ℝ := fun x => (∑ i, x i) / (n : ℝ)
  let g : (Fin n → ℝ × (ℝ × ℝ)) → ℝ :=
    fun u => if Int.fract (∑ i, (u i).1) < p n then 1 else 0
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := measurable_const.ite
    (measurableSet_lt (measurable_fract.comp (by fun_prop)) measurable_const) measurable_const
  have hi := arbitrary_outlier_sequence_indep_pullback Q _ T hT hlaw
    (fun z => f z.1) (fun z => g z.2) (by fun_prop) (by fun_prop)
    (indepFun_prod (μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (ν := Measure.pi (fun _ : Fin n => ν)) hf hg)
  have heqf : (fun z => f z.1) ∘ T = smallNormalMean n := by
    funext s
    simp only [Function.comp_apply, f, T, smallNormalMean, sampleMean]
    rw [Fin.sum_univ_eq_sum_range (fun i => (s i).1)]
  have heqg : (fun z => g z.2) ∘ T = rareFlag p n := by
    funext s
    simp only [Function.comp_apply, g, T, rareFlag, rareUniform]
    rw [Fin.sum_univ_eq_sum_range (fun i => (s i).2.1)]
    exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)
  rw [heqf, heqg] at hi
  exact hi.symm

private theorem arbitrary_outlier_sequence_flag_cases (p : ℕ → ℝ) (n : ℕ)
    (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) :
    rareFlag p n s = 0 ∨ rareFlag p n s = 1 := by
  unfold rareFlag
  split_ifs <;> simp

private theorem arbitrary_outlier_sequence_decomposition (p : ℕ → ℝ) (n : ℕ)
    (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) :
    sqrtN n * rareEstimator p n s =
      sqrtN n * smallNormalMean n s + rareRemainder p n s := by
  unfold rareEstimator rareRemainder
  ring


private theorem arbitrary_outlier_sequence_remainder_probability (p : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hp : 0 < p n ∧ p n ≤ 1) (δ : ℝ) (hδ : 0 < δ) :
    pr (iidSamples slowPopulation) {s | |rareRemainder p n s| > δ} ≤
      4 / (n : ℝ) + p n := by
  let Q := iidSamples slowPopulation
  have hsub : {s | |rareRemainder p n s| > δ} ⊆
      {s | 1 / 2 < |smallNormalMean n s|} ∪ {s | rareFlag p n s = 1} := by
    intro s hs
    by_contra hnot
    have hnot' : ¬ 1 / 2 < |smallNormalMean n s| ∧ rareFlag p n s ≠ 1 := by
      simpa only [mem_union, mem_setOf_eq, not_or] using hnot
    have hc := arbitrary_outlier_sequence_clip_self n s (le_of_not_gt hnot'.1)
    have hb := arbitrary_outlier_sequence_flag_zero p n s hnot'.2
    have hz : rareRemainder p n s = 0 := by
      simp only [rareRemainder, hc, hb, sub_self, mul_zero, add_zero]
    simp only [mem_setOf_eq, hz, abs_zero] at hs
    linarith
  calc
    _ ≤ Q.real ({s | 1 / 2 < |smallNormalMean n s|} ∪ {s | rareFlag p n s = 1}) :=
      measureReal_mono hsub
    _ ≤ Q.real {s | 1 / 2 < |smallNormalMean n s|} + Q.real {s | rareFlag p n s = 1} :=
      measureReal_union_le _ _
    _ ≤ 4 / (n : ℝ) + p n :=
      add_le_add (arbitrary_outlier_sequence_mean_tail n hn) (arbitrary_outlier_sequence_flag_probability p n hn hp).le

private theorem arbitrary_outlier_sequence_probability_bound_limit (p : ℕ → ℝ)
    (hplim : Tendsto p atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => 4 / (n : ℝ) + p n) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa only [div_eq_mul_inv, mul_zero, zero_add] using (hi.const_mul 4).add hplim

private theorem arbitrary_outlier_sequence_remainder_littleOp (p : ℕ → ℝ)
    (hp : ∀ n : ℕ, 1 ≤ n → 0 < p n ∧ p n ≤ 1)
    (hplim : Tendsto p atTop (𝓝 0)) :
    LittleOp (iidSamples slowPopulation) (rareRemainder p) (fun _ => 1) := by
  intro δ hδ
  simp only [mul_one]
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _
    (arbitrary_outlier_sequence_probability_bound_limit p hplim)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact arbitrary_outlier_sequence_remainder_probability p n hn (hp n hn) δ hδ

private theorem arbitrary_outlier_sequence_zero_case (p : ℕ → ℝ) (n : ℕ)
    (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) (hs : rareFlag p n s = 0) :
    rareEstimator p n s = smallNormalClip n s ∧
      rareEstimator p n s - clipReal 0 1 (rareEstimator p n s) = 0 := by
  have hh : rareEstimator p n s = smallNormalClip n s := by
    simp only [rareEstimator, hs, mul_zero, add_zero]
  refine ⟨hh, ?_⟩
  rw [hh]
  exact sub_eq_zero.mpr (rare_estimator_finite (smallNormalMean n s)).1.symm

private theorem arbitrary_outlier_sequence_one_case (p : ℕ → ℝ) (n : ℕ)
    (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) (hs : rareFlag p n s = 1) :
    (19 / 2 : ℝ) ≤ rareEstimator p n s ∧ rareEstimator p n s ≤ 21 / 2 ∧
      clipReal 0 1 (rareEstimator p n s) = 1 ∧
      rareEstimator p n s - clipReal 0 1 (rareEstimator p n s) = smallNormalClip n s + 9 := by
  have hf := rare_estimator_finite (smallNormalMean n s)
  have hh : rareEstimator p n s = smallNormalClip n s + 10 := by
    simp only [rareEstimator, hs, mul_one]
  have hclip : clipReal 0 1 (smallNormalClip n s + 10) = 1 := hf.2.2.2.1
  refine ⟨hh ▸ hf.2.1, hh ▸ hf.2.2.1, ?_, ?_⟩
  · rw [hh]; exact hclip
  · rw [hh, hclip]; ring

private theorem arbitrary_outlier_sequence_clip_bounds (n : ℕ) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) :
    -(1 / 2 : ℝ) ≤ smallNormalClip n s ∧ smallNormalClip n s ≤ 1 / 2 := by
  simpa only [smallNormalClip, zero_sub, zero_add] using
    clipReal_bounds 0 (1 / 2) (smallNormalMean n s) (by norm_num)

private theorem arbitrary_outlier_sequence_outside_events (p : ℕ → ℝ) (n : ℕ) :
    {s | rareEstimator p n s ∉ effectSupport slowPopulation slowEffect} = {s | rareFlag p n s = 1} ∧
    {s | |rareEstimator p n s| > 1} = {s | rareFlag p n s = 1} := by
  have hsupp := arbitrary_outlier_sequence_population.2.2.2.1
  rw [hsupp]
  constructor
  · ext s
    simp only [mem_setOf_eq]
    rcases arbitrary_outlier_sequence_flag_cases p n s with h | h
    · have hh := (arbitrary_outlier_sequence_zero_case p n s h).1
      have hb := arbitrary_outlier_sequence_clip_bounds n s
      have hw : rareEstimator p n s ∈ Icc (-1 : ℝ) 1 := by
        rw [hh]; constructor <;> linarith [hb.1, hb.2]
      simp only [hw, not_true_eq_false, h]; norm_num
    · have hb := arbitrary_outlier_sequence_one_case p n s h
      have hw : rareEstimator p n s ∉ Icc (-1 : ℝ) 1 := by
        intro hw; have := hw.2; linarith [hb.1]
      simp [hw, h]
  · ext s
    simp only [mem_setOf_eq]
    rcases arbitrary_outlier_sequence_flag_cases p n s with h | h
    · have hh := (arbitrary_outlier_sequence_zero_case p n s h).1
      have hb := arbitrary_outlier_sequence_clip_bounds n s
      have hw : |rareEstimator p n s| ≤ 1 := by
        rw [hh]; apply abs_le.mpr; constructor <;> linarith [hb.1, hb.2]
      simp only [not_lt.mpr hw, h]; norm_num
    · have hb := arbitrary_outlier_sequence_one_case p n s h
      have hw : 1 < |rareEstimator p n s| := lt_of_lt_of_le (by linarith [hb.1]) (le_abs_self _)
      simp only [hw, h]

private theorem arbitrary_outlier_sequence_support_probability (p : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hp : 0 < p n ∧ p n ≤ 1) :
    pr (iidSamples slowPopulation) {s | rareEstimator p n s ∈ effectSupport slowPopulation slowEffect} =
      1 - p n := by
  have hcompl : {s | rareEstimator p n s ∈ effectSupport slowPopulation slowEffect} =
      {s | rareFlag p n s = 1}ᶜ := by
    rw [← (arbitrary_outlier_sequence_outside_events p n).1]
    ext s; simp
  rw [pr, hcompl, probReal_compl_eq_one_sub
    (measurableSet_eq_fun (arbitrary_outlier_sequence_flag_measurable p n) measurable_const)]
  rw [show (iidSamples slowPopulation).real {s | rareFlag p n s = 1} = p n from
    arbitrary_outlier_sequence_flag_probability p n hn hp]

/-- Integrability of the actual residual follows from its uniform bound. -/
private theorem arbitrary_outlier_sequence_error_integrable (p : ℕ → ℝ) (n : ℕ) :
    Integrable (fun s => (rareEstimator p n s - clipReal 0 1 (rareEstimator p n s)) ^ 2)
      (iidSamples slowPopulation) := by
  have hm : Measurable (fun s => rareEstimator p n s - clipReal 0 1 (rareEstimator p n s)) :=
    (arbitrary_outlier_sequence_estimator_measurable p n).sub
      (measurable_const.min (measurable_const.max (arbitrary_outlier_sequence_estimator_measurable p n)))
  have hL : MemLp (fun s => rareEstimator p n s - clipReal 0 1 (rareEstimator p n s))
      2 (iidSamples slowPopulation) := by
    apply MemLp.of_bound hm.aestronglyMeasurable (19 / 2)
    apply ae_of_all
    intro s
    rw [Real.norm_eq_abs]
    rcases arbitrary_outlier_sequence_flag_cases p n s with h | h
    · rw [(arbitrary_outlier_sequence_zero_case p n s h).2, abs_zero]; norm_num
    · rw [(arbitrary_outlier_sequence_one_case p n s h).2.2.2]
      have hb := arbitrary_outlier_sequence_clip_bounds n s
      rw [abs_of_nonneg (by linarith [hb.1])]
      linarith [hb.2]
  exact hL.integrable_sq

private theorem arbitrary_outlier_sequence_error_pointwise (p : ℕ → ℝ) (n : ℕ)
    (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) :
    {s | rareFlag p n s = 1}.indicator (fun _ => (289 / 4 : ℝ)) s ≤
      (rareEstimator p n s - clipReal 0 1 (rareEstimator p n s)) ^ 2 ∧
    (rareEstimator p n s - clipReal 0 1 (rareEstimator p n s)) ^ 2 ≤
      {s | rareFlag p n s = 1}.indicator (fun _ => (361 / 4 : ℝ)) s := by
  rcases arbitrary_outlier_sequence_flag_cases p n s with h | h
  · have hnot : s ∉ {s | rareFlag p n s = 1} := by simp [h]
    rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hnot,
      (arbitrary_outlier_sequence_zero_case p n s h).2]
    norm_num
  · have hmem : s ∈ {s | rareFlag p n s = 1} := h
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
      (arbitrary_outlier_sequence_one_case p n s h).2.2.2]
    have hb := arbitrary_outlier_sequence_clip_bounds n s
    have hz : 0 ≤ smallNormalClip n s + 9 := by linarith [hb.1]
    constructor
    · have hh := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 17 / 2) hz).mpr
        (show (17 / 2 : ℝ) ≤ smallNormalClip n s + 9 by linarith [hb.1])
      norm_num at hh ⊢; exact hh
    · have hh := (sq_le_sq₀ hz (by norm_num : (0 : ℝ) ≤ 19 / 2)).mpr
        (show smallNormalClip n s + 9 ≤ (19 / 2 : ℝ) by linarith [hb.2])
      norm_num at hh ⊢; exact hh

private theorem arbitrary_outlier_sequence_error_mse (p : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hp : 0 < p n ∧ p n ≤ 1) :
    (289 / 4 : ℝ) * p n ≤
      (∫ s, (rareEstimator p n s - clipReal 0 1 (rareEstimator p n s)) ^ 2 ∂iidSamples slowPopulation) ∧
    (∫ s, (rareEstimator p n s - clipReal 0 1 (rareEstimator p n s)) ^ 2 ∂iidSamples slowPopulation) ≤
      (361 / 4 : ℝ) * p n := by
  let Q := iidSamples slowPopulation
  let E := {s | rareFlag p n s = 1}
  have hmE : MeasurableSet E := measurableSet_eq_fun (arbitrary_outlier_sequence_flag_measurable p n) measurable_const
  have hl := integral_mono ((integrable_const (289 / 4 : ℝ)).indicator hmE)
    (arbitrary_outlier_sequence_error_integrable p n) (fun s => (arbitrary_outlier_sequence_error_pointwise p n s).1)
  have hu := integral_mono (arbitrary_outlier_sequence_error_integrable p n)
    ((integrable_const (361 / 4 : ℝ)).indicator hmE) (fun s => (arbitrary_outlier_sequence_error_pointwise p n s).2)
  rw [integral_indicator_const _ hmE] at hl hu
  simp only [smul_eq_mul] at hl hu
  have hprob : Q.real E = p n := arbitrary_outlier_sequence_flag_probability p n hn hp
  rw [hprob] at hl hu
  exact ⟨by nlinarith [hl], by nlinarith [hu]⟩

/-- Independence gives the sharp factor p_n in the second-moment lower bound. -/
private theorem arbitrary_outlier_sequence_remainder_lower (p : ℕ → ℝ) (n : ℕ) (hn : 4 ≤ n)
    (hp : 0 < p n ∧ p n ≤ 1) :
    100 * ((n : ℝ) - 4) * p n ≤
      ∫ s, rareRemainder p n s ^ 2 ∂iidSamples slowPopulation := by
  let Q := iidSamples slowPopulation
  let F := {s | rareFlag p n s = 1}
  let C := {s | |smallNormalMean n s| ≤ 1 / 2}
  let E := F ∩ C
  have hn1 : 1 ≤ n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hmF : MeasurableSet F := measurableSet_eq_fun (arbitrary_outlier_sequence_flag_measurable p n) measurable_const
  have hmabs : Measurable (fun s => |smallNormalMean n s|) := by
    simpa only [Real.norm_eq_abs] using (arbitrary_outlier_sequence_mean_measurable n).norm
  have hmC : MeasurableSet C := measurableSet_le hmabs measurable_const
  have hmE : MeasurableSet E := hmF.inter hmC
  have hC : 1 - 4 / (n : ℝ) ≤ Q.real C := by
    have hcompl : C = {s | 1 / 2 < |smallNormalMean n s|}ᶜ := by
      ext s; simp [C]
    rw [hcompl, probReal_compl_eq_one_sub
      (measurableSet_lt measurable_const hmabs)]
    have ht := arbitrary_outlier_sequence_mean_tail n hn1
    change Q.real {s | 1 / 2 < |smallNormalMean n s|} ≤ 4 / (n : ℝ) at ht
    linarith
  have hE : Q.real E = p n * Q.real C := by
    have h := (arbitrary_outlier_sequence_flag_independent p n).measure_inter_preimage_eq_mul
      ({1} : Set ℝ) {x : ℝ | |x| ≤ 1 / 2} (measurableSet_singleton 1)
      (measurableSet_le (show Measurable (fun x : ℝ => |x|) by fun_prop) measurable_const)
    have hfpre : rareFlag p n ⁻¹' ({1} : Set ℝ) = F := by
      ext s; simp [F]
    have hcpre : smallNormalMean n ⁻¹' {x : ℝ | |x| ≤ 1 / 2} = C := by
      ext s; simp [C]
    have h' : Q (F ∩ C) = Q F * Q C := by
      simpa only [hfpre, hcpre] using h
    change (Q (F ∩ C)).toReal = p n * (Q C).toReal
    rw [h', ENNReal.toReal_mul]
    have hprob : (Q F).toReal = p n := arbitrary_outlier_sequence_flag_probability p n hn1 hp
    rw [hprob]
  have hpoint (s) : E.indicator (fun _ => 100 * (n : ℝ)) s ≤ rareRemainder p n s ^ 2 := by
    by_cases hs : s ∈ E
    · rw [Set.indicator_of_mem hs]
      have hc := arbitrary_outlier_sequence_clip_self n s hs.2
      have hb : rareFlag p n s = 1 := hs.1
      simp only [rareRemainder, hc, hb, sub_self, zero_add, mul_one, mul_pow, sqrtN,
        Real.sq_sqrt (Nat.cast_nonneg n)]
      norm_num <;> nlinarith
    · rw [Set.indicator_of_notMem hs]
      exact sq_nonneg _
  have hi := integral_mono ((integrable_const (100 * (n : ℝ))).indicator hmE)
    (arbitrary_outlier_sequence_remainder_integrable p n hn1) hpoint
  rw [integral_indicator_const _ hmE] at hi
  simp only [smul_eq_mul] at hi
  rw [hE] at hi
  have hmul := mul_le_mul_of_nonneg_left hC
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) (Nat.cast_nonneg n)) hp.1.le)
  have hcancel : 100 * (n : ℝ) * p n * (1 - 4 / (n : ℝ)) =
      100 * ((n : ℝ) - 4) * p n := by field_simp [hnR.ne']; <;> ring
  rw [hcancel] at hmul
  nlinarith [hi]

private theorem arbitrary_outlier_sequence_scaled_error_littleOp (p : ℕ → ℝ)
    (hp : ∀ n : ℕ, 1 ≤ n → 0 < p n ∧ p n ≤ 1)
    (hplim : Tendsto p atTop (𝓝 0)) :
    LittleOp (iidSamples slowPopulation)
      (fun n s => sqrtN n * (rareEstimator p n s - clipReal 0 1 (rareEstimator p n s)))
      (fun _ => 1) := by
  intro δ hδ
  simp only [mul_one]
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hplim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  calc
    _ ≤ (iidSamples slowPopulation).real {s | rareFlag p n s = 1} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro s hs
      change δ < |sqrtN n * (rareEstimator p n s - clipReal 0 1 (rareEstimator p n s))| at hs
      rcases arbitrary_outlier_sequence_flag_cases p n s with h | h
      · rw [(arbitrary_outlier_sequence_zero_case p n s h).2, mul_zero, abs_zero] at hs
        exact False.elim (not_lt_of_ge hδ.le hs)
      · exact h
    _ = p n := arbitrary_outlier_sequence_flag_probability p n hn (hp n hn)

/-- Exact prescribed-sequence witness, with no restriction on p at index zero. -/
theorem arbitrary_outlier_sequence_proof (p : ℕ → ℝ)
    (hp : ∀ n : ℕ, 1 ≤ n → 0 < p n ∧ p n ≤ 1) (hplim : Tendsto p atTop (𝓝 0)) :
    Measurable slowEffect ∧ Integrable slowEffect slowPopulation ∧
    populationMean slowPopulation slowEffect = 0 ∧
    effectSupport slowPopulation slowEffect = Icc (-1) 1 ∧ effectRadius slowPopulation slowEffect = 1 ∧
    RootNNormal (iidSamples slowPopulation) (rareEstimator p) 0 ∧
    (∀ n : ℕ, 1 ≤ n →
      (iidSamples slowPopulation).map (rareUniform n) = uniformHalfOpen01 ∧
      pr (iidSamples slowPopulation) {s | rareFlag p n s = 1} = p n ∧
      IndepFun (rareFlag p n) (smallNormalMean n) (iidSamples slowPopulation) ∧
      (iidSamples slowPopulation).map (fun s => sqrtN n * smallNormalMean n s) = gaussianReal 0 1 ∧
      (∀ s, sqrtN n * rareEstimator p n s = sqrtN n * smallNormalMean n s + rareRemainder p n s) ∧
      (∀ δ : ℝ, 0 < δ → pr (iidSamples slowPopulation) {s | |rareRemainder p n s| > δ} ≤ 4 / (n : ℝ) + p n) ∧
      {s | rareEstimator p n s ∉ effectSupport slowPopulation slowEffect} = {s | rareFlag p n s = 1} ∧
      {s | |rareEstimator p n s| > 1} = {s | rareFlag p n s = 1} ∧
      {s | rareEstimator p n s ≠ clipReal 0 1 (rareEstimator p n s)} = {s | rareFlag p n s = 1} ∧
      pr (iidSamples slowPopulation) {s | rareEstimator p n s ≠ clipReal 0 1 (rareEstimator p n s)} = p n ∧
      pr (iidSamples slowPopulation) {s | rareEstimator p n s ∈ effectSupport slowPopulation slowEffect} = 1 - p n ∧
      (∀ s, rareFlag p n s = 0 → rareEstimator p n s = smallNormalClip n s ∧
        rareEstimator p n s - clipReal 0 1 (rareEstimator p n s) = 0) ∧
      (∀ s, rareFlag p n s = 1 → (19 / 2 : ℝ) ≤ rareEstimator p n s ∧
        rareEstimator p n s ≤ 21 / 2 ∧ clipReal 0 1 (rareEstimator p n s) = 1 ∧
        rareEstimator p n s - clipReal 0 1 (rareEstimator p n s) = smallNormalClip n s + 9) ∧
      (289 / 4 : ℝ) * p n ≤
        (∫ s, (rareEstimator p n s - clipReal 0 1 (rareEstimator p n s)) ^ 2 ∂iidSamples slowPopulation) ∧
      (∫ s, (rareEstimator p n s - clipReal 0 1 (rareEstimator p n s)) ^ 2 ∂iidSamples slowPopulation) ≤
        (361 / 4 : ℝ) * p n) ∧
    (∀ n : ℕ, 4 ≤ n → (∫ s, rareRemainder p n s ^ 2 ∂iidSamples slowPopulation) ≥
      100 * ((n : ℝ) - 4) * p n) ∧
    LittleOp (iidSamples slowPopulation) (rareRemainder p) (fun _ => 1) ∧
    LittleOp (iidSamples slowPopulation)
      (fun n s => sqrtN n * (rareEstimator p n s - clipReal 0 1 (rareEstimator p n s))) (fun _ => 1) := by
  rcases arbitrary_outlier_sequence_population with ⟨hm, hi, hmean, hsupp, hrad⟩
  refine ⟨hm, hi, hmean, hsupp, hrad, arbitrary_outlier_sequence_rootN p hp hplim, ?_, ?_,
    arbitrary_outlier_sequence_remainder_littleOp p hp hplim, arbitrary_outlier_sequence_scaled_error_littleOp p hp hplim⟩
  · intro n hn
    have hpn := hp n hn
    have hmse := arbitrary_outlier_sequence_error_mse p n hn hpn
    exact ⟨arbitrary_outlier_sequence_uniform_law n hn, arbitrary_outlier_sequence_flag_probability p n hn hpn,
      arbitrary_outlier_sequence_flag_independent p n, arbitrary_outlier_sequence_scaled_mean_law n hn,
      arbitrary_outlier_sequence_decomposition p n, arbitrary_outlier_sequence_remainder_probability p n hn hpn,
      (arbitrary_outlier_sequence_outside_events p n).1, (arbitrary_outlier_sequence_outside_events p n).2,
      arbitrary_outlier_sequence_failure_set p n, arbitrary_outlier_sequence_failure_probability p n hn hpn,
      arbitrary_outlier_sequence_support_probability p n hn hpn, arbitrary_outlier_sequence_zero_case p n, arbitrary_outlier_sequence_one_case p n,
      hmse.1, hmse.2⟩
  · intro n hn
    exact arbitrary_outlier_sequence_remainder_lower p n hn (hp n (by omega))

end
end AronowAudit.P017.Wave1
