import AronowAudit.P018.Wave1.Gap.GP0181B1
import AronowAudit.P018.Wave1.Gap.GP0182B2b
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.CramerWold

noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! Corrected inference and the multivariate Gaussian limit. -/

lemma inferenceB3_limitingTarget_psd {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) : (limitingTarget K).PosSemidef := by
  have hs : (projectionGamma K).IsHermitian := by
    ext a b
    simp only [Matrix.conjTranspose_apply, star_trivial, projectionGamma, meanMat, outer]
    congr 1
    ext u
    ring
  have hp : (projectionGamma K).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hs
    intro c
    change 0 ≤ dot c ((projectionGamma K).mulVec c)
    rw [show dot c ((projectionGamma K).mulVec c) =
      ∫ u, (dot c (projection K u))^2 ∂K.μ from
        GP0182B2b_mean_outer_quad K.μ (projection K)
          (fun a b => (GP0182B2b_projection_memLp K hK a).2.integrable_mul
            (GP0182B2b_projection_memLp K hK b).2) c]
    exact integral_nonneg (fun _ => sq_nonneg _)
  exact (sandwich_positive_semidefinite _ _ (GP0182B2b_inverse_symmetric K hK) hp).smul
    (by norm_num : (0 : ℝ) ≤ 4)

lemma inferenceB3_trueTarget_symmetric {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (N : ℕ) :
    (trueTarget K N).transpose = trueTarget K N := by
  have hv : (varMat (unitSampleLaw K N) (scoreSum K)).transpose =
      varMat (unitSampleLaw K N) (scoreSum K) := by
    ext a b
    exact covariance_comm _ _
  simp only [trueTarget, Matrix.transpose_smul,
    sandwich_symmetric _ _ (GP0182B2b_inverse_symmetric K hK) hv]

lemma inferenceB3_entry_polarization {k : ℕ} (M : Mat k) (hs : M.transpose = M)
    (i j : Fin k) :
    M i j = (dot (Pi.single i 1 + Pi.single j 1)
      (M.mulVec (Pi.single i 1 + Pi.single j 1)) -
      dot (Pi.single i 1) (M.mulVec (Pi.single i 1)) -
      dot (Pi.single j 1) (M.mulVec (Pi.single j 1))) / 2 := by
  classical
  have hs' : M j i = M i j := congrFun (congrFun hs i) j
  simp [dot, Matrix.mulVec, dotProduct, Pi.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib, Pi.single_apply, ite_mul, mul_ite, hs']
  <;> ring

lemma inferenceB3_target_limit {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    Tendsto (trueTarget K) atTop (𝓝 (limitingTarget K)) := by
  classical
  have hv : (limitingTarget K).transpose = limitingTarget K := by
    have hh := (inferenceB3_limitingTarget_psd K hK).isHermitian
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hh
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hh := (((GP0182B2b_trueTarget_contrast_limit K hK (Pi.single i 1 + Pi.single j 1)).sub
    (GP0182B2b_trueTarget_contrast_limit K hK (Pi.single i 1))).sub
    (GP0182B2b_trueTarget_contrast_limit K hK (Pi.single j 1))).div_const 2
  rw [← inferenceB3_entry_polarization _ hv i j] at hh
  exact hh.congr (fun N => (inferenceB3_entry_polarization _
    (inferenceB3_trueTarget_symmetric K hK N) i j).symm)

lemma inferenceB3_gaussian_inner {k : ℕ} (V : Mat k) (hV : V.PosSemidef)
    (c : EuclideanSpace ℝ (Fin k)) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) V).map
      (fun x => inner ℝ c x) = gaussianReal 0 (dot c (V.mulVec c)).toNNReal := by
  let G := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) V
  have hm : (∫ x, inner ℝ c x ∂G) = 0 := by
    have h := (innerSL ℝ c).integral_comp_id_comm
      (μ := G) IsGaussian.integrable_id
    simpa [G] using h
  have hv : variance (fun x => inner ℝ c x) G = dot c (V.mulVec c) := by
    rw [← covarianceBilin_self IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hV]
    rfl
  have h := IsGaussian.map_eq_gaussianReal (μ := G) (innerSL ℝ c)
  change G.map (fun x => inner ℝ c x) =
    gaussianReal (∫ x, inner ℝ c x ∂G) (variance (fun x => inner ℝ c x) G).toNNReal at h
  rwa [hm, hv] at h

lemma inferenceB3_scaled_error_measurable {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (N : ℕ) :
    Measurable (fun ω : Fin N → U => Real.sqrt N • coefficientError K ω) := by
  classical
  have hm : Measurable (@coefficientError U _ k N K) := by
    apply measurable_pi_lambda
    intro a
    simpa [dot, Pi.single_apply, ite_mul] using
      (GP0182B2b_measurable_statistics K hK (Pi.single a 1) N).1
  apply measurable_pi_lambda
  intro a
  change Measurable (fun ω : Fin N → U => Real.sqrt (N : ℝ) * coefficientError K ω a)
  exact ((measurable_pi_apply a).comp hm).const_mul _

lemma inferenceB3_vector_clt {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    ∃ ν : Measure (Vec k), centeredNormalLaw ν (limitingTarget K) ∧
      weakLimit (unitSampleLaw K) (fun N ω => Real.sqrt N • coefficientError K ω) ν := by
  letI : IsProbabilityMeasure K.μ := hK.1
  let V := limitingTarget K
  have hV : V.PosSemidef := inferenceB3_limitingTarget_psd K hK
  let G := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) V
  let ν : Measure (Vec k) := G.map WithLp.ofLp
  have hG : IsProbabilityMeasure G := inferInstance
  have hν : IsProbabilityMeasure ν := by
    dsimp only [ν]
    infer_instance
  let X : ℕ → (ℕ → U) → EuclideanSpace ℝ (Fin k) :=
    fun N ω => WithLp.toLp 2 (Real.sqrt N • coefficientError K (GP0182B2b_prefix N ω))
  have hm (N : ℕ) : Measurable (X N) :=
    (PiLp.continuous_toLp 2 _).measurable.comp
      ((inferenceB3_scaled_error_measurable K hK N).comp (GP0182B2b_prefix_measurable N))
  have hclt : TendstoInDistribution X atTop id (fun _ => GP0182B2b_product K.μ) G := by
    apply (tendstoInDistribution_iff_tendstoInDistribution_inner
      measurable_id.aemeasurable (fun N => (hm N).aemeasurable)).mpr
    intro t
    have ht := GP0182B2b_numerator_clt K hK (WithLp.ofLp t)
    have hfun : (fun N ω => inner ℝ (X N ω) t) =
        (fun (N : ℕ) (ω : ℕ → U) => Real.sqrt N *
          dot (WithLp.ofLp t) (coefficientError K (GP0182B2b_prefix N ω))) := by
      funext N ω
      simp only [X, PiLp.inner_apply, Real.inner_apply, PiLp.toLp_apply,
        Pi.smul_apply, smul_eq_mul, dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    have hmap : G.map (fun x => inner ℝ x t) =
        gaussianReal 0 (dot (WithLp.ofLp t) (V.mulVec (WithLp.ofLp t))).toNNReal := by
      rw [show (fun x => inner ℝ x t) = (fun x => inner ℝ t x) from
        funext (fun x => (real_inner_comm x t).symm)]
      exact inferenceB3_gaussian_inner V hV t
    change TendstoInDistribution (fun N ω => inner ℝ (X N ω) t) atTop
      (fun x => inner ℝ x t) (fun _ => GP0182B2b_product K.μ) G
    rw [hfun]
    refine ⟨ht.forall_aemeasurable, by fun_prop, ?_⟩
    simpa only [Measure.map_id, hmap] using ht.tendsto
  have hvec := hclt.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : Fin k => ℝ))
  refine ⟨ν, ⟨hV, hν, ?_⟩, ?_⟩
  · intro c
    dsimp only [ν]
    rw [Measure.map_map]
    · simp only [Function.comp_def]
      have he : (fun x : EuclideanSpace ℝ (Fin k) => dot c (WithLp.ofLp x)) =
          (fun x => inner ℝ (WithLp.toLp 2 c) x) := by
        funext x
        simp only [dot, PiLp.inner_apply, Real.inner_apply, PiLp.toLp_apply]
      rw [he]
      exact inferenceB3_gaussian_inner V hV (WithLp.toLp 2 c)
    · simp only [dot]
      fun_prop
    · exact (PiLp.continuous_ofLp 2 _).measurable
  · refine ⟨fun N => (inferenceB3_scaled_error_measurable K hK N).aemeasurable, hν, ?_⟩
    intro g
    have hh := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      hvec.forall_aemeasurable hvec.aemeasurable_limit).mp hvec g
    have he (N : ℕ) :
        (∫ ω : ℕ → U, g (Real.sqrt N • coefficientError K (GP0182B2b_prefix N ω))
          ∂GP0182B2b_product K.μ) =
          ∫ ω : Fin N → U, g (Real.sqrt N • coefficientError K ω) ∂unitSampleLaw K N :=
      GP0182B2b_prefix_integral K.μ N _
        (g.continuous.measurable.comp (inferenceB3_scaled_error_measurable K hK N))
    have heν : (∫ x, g x ∂ν) =
        ∫ x : EuclideanSpace ℝ (Fin k), g (WithLp.ofLp x) ∂G :=
      integral_map (PiLp.continuous_ofLp 2 _).measurable.aemeasurable
        g.continuous.measurable.aestronglyMeasurable
    rw [heν]
    change Tendsto (fun N : ℕ => ∫ ω : ℕ → U,
      g (Real.sqrt N • coefficientError K (GP0182B2b_prefix N ω)) ∂GP0182B2b_product K.μ)
      atTop (𝓝 (∫ x : EuclideanSpace ℝ (Fin k), g (WithLp.ofLp x) ∂G)) at hh
    simpa only [he] using hh

theorem inference_corrected_proof {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    (∃ ν : Measure (Vec k), centeredNormalLaw ν (limitingTarget K) ∧
      weakLimit (unitSampleLaw K) (fun N ω => Real.sqrt N • coefficientError K ω) ν) ∧
    Tendsto (trueTarget K) atTop (𝓝 (limitingTarget K)) ∧
    inProbability (unitSampleLaw K) (fun N ω =>
      (N : ℝ) • sampleVariance members (design K ω) (response K ω) - limitingTarget K) ∧
    ∀ c : Vec k, 0 < dot c ((limitingTarget K).mulVec c) →
      weakLimit (unitSampleLaw K) (fun N ω =>
        dot c (coefficientError K ω) /
          Real.sqrt (dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c)))
        (gaussianReal 0 1) ∧
      Tendsto (fun N : ℕ => (unitSampleLaw K N {ω |
        dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c) ≤ 0}).toReal)
        atTop (𝓝 0) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  have hlim := inferenceB3_target_limit K hK
  refine ⟨inferenceB3_vector_clt K hK, hlim, ?_, ?_⟩
  · have hdlim : Tendsto (fun N : ℕ => trueTarget K N - limitingTarget K)
        atTop (𝓝 (0 : Mat k)) := by
      convert hlim.sub_const (limitingTarget K) using 1
      simp
    have hd := WeightedConsistency.inProbability_deterministic (unitSampleLaw K)
      (fun N => trueTarget K N - limitingTarget K) hdlim
    simpa only [sub_add_sub_cancel] using WeightedConsistency.inProbability_add (unitSampleLaw K)
      (GP0182B2b_variance_consistency K hK) hd
  · intro c hc
    exact ⟨GP0182B2b_pivot_weak K hK c hc, GP0182B2b_variance_bad K hK c hc⟩

/-! Exact score projection decomposition. -/

/-! Population normal equations and the first-order projection. -/

lemma spdB3_score_measurable {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    Measurable (fun uv : U × U => populationScore K uv.1 uv.2) := by
  apply measurable_pi_lambda
  intro a
  have hx (b : Fin k) := (measurable_pi_apply b).comp hK.2.1
  exact (hK.2.2.1.sub (Finset.measurable_fun_sum _
    (fun b _ => (hx b).mul_const (populationBeta K b)))).mul (hx a)

lemma spdB3_score_bound {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ uv ∂ K.μ.prod K.μ,
      ∀ a, ‖populationScore K uv.1 uv.2 a‖ ≤ B := by
  obtain ⟨C, hC, hb⟩ := hK.2.2.2.2.1
  let B := (C + (k : ℝ) * C * ‖populationBeta K‖) * C
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  filter_upwards [hb] with uv huv a
  have hdot : |dot (K.X uv.1 uv.2) (populationBeta K)| ≤
      (k : ℝ) * C * ‖populationBeta K‖ := by
    unfold dot
    calc
      _ ≤ ∑ b : Fin k, |K.X uv.1 uv.2 b * populationBeta K b| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _b : Fin k, C * ‖populationBeta K‖ := by
        apply Finset.sum_le_sum
        intro b hb
        rw [abs_mul]
        exact mul_le_mul ((norm_le_pi_norm _ b).trans huv.1)
          (show |populationBeta K b| ≤ ‖populationBeta K‖ from
            norm_le_pi_norm (populationBeta K) b) (abs_nonneg _) hC
      _ = _ := by simp [mul_assoc]
  have he : |populationResidual K uv.1 uv.2| ≤ C + (k : ℝ) * C * ‖populationBeta K‖ :=
    (abs_sub _ _).trans (add_le_add huv.2 hdot)
  change |populationResidual K uv.1 uv.2 * K.X uv.1 uv.2 a| ≤ B
  rw [abs_mul]
  exact mul_le_mul he ((norm_le_pi_norm _ a).trans huv.1) (abs_nonneg _)
    (by positivity)

lemma spdB3_score_memLp {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (a : Fin k) :
    MemLp (fun uv : U × U => populationScore K uv.1 uv.2 a) ∞ (K.μ.prod K.μ) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  obtain ⟨B, hB, hb⟩ := spdB3_score_bound K hK
  exact MemLp.of_bound ((measurable_pi_apply a).comp
    (spdB3_score_measurable K hK)).aestronglyMeasurable B (hb.mono fun uv huv => huv a)

lemma spdB3_score_centered {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    meanVec (K.μ.prod K.μ) (fun uv => populationScore K uv.1 uv.2) = 0 := by
  classical
  letI : IsProbabilityMeasure K.μ := hK.1
  obtain ⟨hxx, hxy⟩ := corrected_pair_products K hK
  have hnormal : (populationGram K).mulVec (populationBeta K) =
      meanVec (K.μ.prod K.μ) (fun uv => score (K.X uv.1 uv.2) (K.Y uv.1 uv.2)) := by
    unfold populationBeta
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hK.2.2.2.2.2.2), Matrix.one_mulVec]
  ext a
  have hid (uv : U × U) : populationScore K uv.1 uv.2 a =
      K.Y uv.1 uv.2 * K.X uv.1 uv.2 a -
        ∑ b, (K.X uv.1 uv.2 a * K.X uv.1 uv.2 b) * populationBeta K b := by
    simp only [populationScore, populationResidual, score, Pi.smul_apply,
      smul_eq_mul, dot, sub_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    ring
  change (∫ uv, populationScore K uv.1 uv.2 a ∂ K.μ.prod K.μ) = 0
  simp_rw [hid]
  rw [integral_sub (hxy a) (integrable_finset_sum _
    (fun b _ => (hxx a b).mul_const _)), integral_finset_sum _
      (fun b _ => (hxx a b).mul_const _)]
  simp_rw [integral_mul_const]
  exact sub_eq_zero.mpr (congrFun hnormal a).symm

lemma spdB3_projection_measurable {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) : Measurable (projection K) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  apply measurable_pi_lambda
  intro a
  exact (((measurable_pi_apply a).comp (spdB3_score_measurable K hK)).stronglyMeasurable.integral_prod_right').measurable

lemma spdB3_projection_memLp {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (a : Fin k) :
    MemLp (fun u => projection K u a) ∞ K.μ := by
  letI : IsProbabilityMeasure K.μ := hK.1
  obtain ⟨B, hB, hb⟩ := spdB3_score_bound K hK
  apply MemLp.of_bound ((measurable_pi_apply a).comp
    (spdB3_projection_measurable K hK)).aestronglyMeasurable B
  have hs := (Measure.ae_ae_of_ae_prod hb)
  filter_upwards [hs] with u hu
  simpa [projection, meanVec] using
    (norm_integral_le_of_norm_le_const (hu.mono fun v hv => hv a))

lemma spdB3_projection_centered {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) : meanVec K.μ (projection K) = 0 := by
  letI : IsProbabilityMeasure K.μ := hK.1
  ext a
  change (∫ u, ∫ v, populationScore K u v a ∂K.μ ∂K.μ) = 0
  rw [← integral_prod _ ((spdB3_score_memLp K hK a).integrable (by simp))]
  exact congrFun (spdB3_score_centered K hK) a

def spdB3_remainder {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (u v : U) : Vec k :=
  populationScore K u v - projection K u - projection K v

lemma spdB3_remainder_measurable {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    Measurable (fun uv : U × U => spdB3_remainder K uv.1 uv.2) :=
  ((spdB3_score_measurable K hK).sub ((spdB3_projection_measurable K hK).comp
    measurable_fst)).sub ((spdB3_projection_measurable K hK).comp measurable_snd)

lemma spdB3_remainder_memLp {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (a : Fin k) :
    MemLp (fun uv : U × U => spdB3_remainder K uv.1 uv.2 a) ∞ (K.μ.prod K.μ) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  exact ((spdB3_score_memLp K hK a).sub
    ((spdB3_projection_memLp K hK a).comp_measurePreserving measurePreserving_fst)).sub
    ((spdB3_projection_memLp K hK a).comp_measurePreserving measurePreserving_snd)

lemma spdB3_remainder_symmetric {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (u v : U) :
    spdB3_remainder K u v = spdB3_remainder K v u := by
  have hs : populationScore K u v = populationScore K v u := by
    simp only [populationScore, populationResidual, (hK.2.2.2.1 u v).1,
      (hK.2.2.2.1 u v).2]
  unfold spdB3_remainder
  rw [hs]
  abel

lemma spdB3_remainder_degenerate {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    ∀ᵐ u ∂K.μ, meanVec K.μ (spdB3_remainder K u) = 0 := by
  letI : IsProbabilityMeasure K.μ := hK.1
  have hsections : ∀ᵐ u ∂K.μ, ∀ a,
      Integrable (fun v => populationScore K u v a) K.μ := by
    apply ae_all_iff.mpr
    intro a
    exact ((spdB3_score_memLp K hK a).integrable (by simp)).prod_right_ae
  filter_upwards [hsections] with u hu
  ext a
  change (∫ v, (populationScore K u v a - projection K u a) - projection K v a ∂K.μ) = 0
  have hi : Integrable (fun v => populationScore K u v a - projection K u a) K.μ :=
    (hu a).sub (integrable_const (projection K u a))
  rw [integral_sub hi
    ((spdB3_projection_memLp K hK a).integrable (by simp)),
    integral_sub (hu a) (integrable_const (projection K u a))]
  have hg := congrFun (spdB3_projection_centered K hK) a
  change (∫ v, projection K v a ∂K.μ) = 0 at hg
  rw [hg, integral_const]
  simp only [probReal_univ, one_smul, sub_zero]
  change projection K u a - projection K u a = 0
  exact sub_self _

lemma spdB3_remainder_centered {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (a : Fin k) :
    (∫ uv : U × U, spdB3_remainder K uv.1 uv.2 a ∂K.μ.prod K.μ) = 0 := by
  letI : IsProbabilityMeasure K.μ := hK.1
  rw [integral_prod _ ((spdB3_remainder_memLp K hK a).integrable (by simp))]
  exact integral_eq_zero_of_ae ((spdB3_remainder_degenerate K hK).mono
    fun u hu => congrFun hu a)

/-! Product-coordinate transport. The pair/triple construction and the
L² argument for shared products follow earlier code by P. M. Aronow and Patrick Lopatto.
Copyright (c) 2026 P. M. Aronow and Patrick Lopatto.
MIT licensed. The cancellation below
allows two different kernels and almost-everywhere section centering.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:
The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.
THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
-/
/- See NOTICE at the repository root for this adapted section. -/

lemma spdB3_pair_preserving {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    MeasurePreserving (fun ω : Fin N → U => (ω i, ω j))
      (Measure.pi (fun _ : Fin N => μ)) (μ.prod μ) := by
  have hi : iIndepFun (fun i : Fin N => fun ω : Fin N → U => ω i)
      (Measure.pi (fun _ : Fin N => μ)) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  rw [(hi.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable,
    (measurePreserving_eval (fun _ : Fin N => μ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin N => μ) j).map_eq]

lemma spdB3_triple_preserving {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ} {i j l : Fin N}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    MeasurePreserving (fun ω : Fin N → U => ((ω i, ω j), ω l))
      (Measure.pi (fun _ : Fin N => μ)) ((μ.prod μ).prod μ) := by
  have hi : iIndepFun (fun i : Fin N => fun ω : Fin N → U => ω i)
      (Measure.pi (fun _ : Fin N => μ)) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  refine ⟨((measurable_pi_apply i).prodMk (measurable_pi_apply j)).prodMk
    (measurable_pi_apply l), ?_⟩
  rw [(hi.indepFun_prodMk (fun i => measurable_pi_apply i) i j l hil hjl).map_prod_eq_prod_map_map
      ((measurable_pi_apply i).aemeasurable.prodMk (measurable_pi_apply j).aemeasurable)
      (measurable_pi_apply l).aemeasurable,
    (spdB3_pair_preserving μ hij).map_eq,
    (measurePreserving_eval (fun _ : Fin N => μ) l).map_eq]

lemma spdB3_integral_comp {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {f : A → B} (hf : MeasurePreserving f μ ν)
    (g : B → ℝ) (hg : Measurable g) :
    (∫ x, g (f x) ∂μ) = ∫ y, g y ∂ν := by
  rw [← hf.map_eq]
  exact (integral_map hf.aemeasurable hg.aestronglyMeasurable).symm

lemma spdB3_shared_zero {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {A B : U × U → ℝ}
    (hA : MemLp A 2 (μ.prod μ)) (hB : MemLp B 2 (μ.prod μ))
    (hcenter : ∀ᵐ u ∂μ, (∫ v, B (u, v) ∂μ) = 0) :
    (∫ z : (U × U) × U, A z.1 * B (z.1.1, z.2) ∂(μ.prod μ).prod μ) = 0 := by
  have h₁ : MemLp (fun z : (U × U) × U => A z.1) 2 ((μ.prod μ).prod μ) :=
    hA.comp_measurePreserving measurePreserving_fst
  have hm : MeasurePreserving (fun z : (U × U) × U => (z.1.1, z.2))
      ((μ.prod μ).prod μ) (μ.prod μ) :=
    measurePreserving_fst.prod (MeasurePreserving.id μ)
  have h₂ := hB.comp_measurePreserving hm
  have hip : Integrable (fun z : (U × U) × U => A z.1 * B (z.1.1, z.2))
      ((μ.prod μ).prod μ) := h₁.integrable_mul h₂
  rw [integral_prod _ hip]
  simp only [integral_const_mul]
  apply integral_eq_zero_of_ae
  have hc : ∀ᵐ uv ∂μ.prod μ, (∫ v, B (uv.1, v) ∂μ) = 0 :=
    measurePreserving_fst.quasiMeasurePreserving.tendsto_ae hcenter
  filter_upwards [hc] with uv huv
  rw [huv, mul_zero]
  rfl

lemma spdB3_shared_sample_zero {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ} {A B : U × U → ℝ}
    (hmA : Measurable A) (hmB : Measurable B)
    (hA : MemLp A 2 (μ.prod μ)) (hB : MemLp B 2 (μ.prod μ))
    (hcenter : ∀ᵐ u ∂μ, (∫ v, B (u, v) ∂μ) = 0)
    {i j l : Fin N} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    (∫ ω : Fin N → U, A (ω i, ω j) * B (ω i, ω l)
      ∂Measure.pi (fun _ : Fin N => μ)) = 0 := by
  have hm : Measurable (fun z : (U × U) × U => A z.1 * B (z.1.1, z.2)) :=
    (hmA.comp measurable_fst).mul (hmB.comp (measurable_fst.fst.prodMk measurable_snd))
  exact (spdB3_integral_comp (spdB3_triple_preserving μ hij hil hjl) _ hm).trans
    (spdB3_shared_zero μ hA hB hcenter)

lemma spdB3_disjoint_sample_zero {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ} {A B : U × U → ℝ}
    (hmA : Measurable A) (hmB : Measurable B)
    (hmeanB : (∫ uv, B uv ∂μ.prod μ) = 0)
    {i j l m : Fin N} (hij : i ≠ j) (hlm : l ≠ m)
    (hil : i ≠ l) (him : i ≠ m) (hjl : j ≠ l) (hjm : j ≠ m) :
    (∫ ω : Fin N → U, A (ω i, ω j) * B (ω l, ω m)
      ∂Measure.pi (fun _ : Fin N => μ)) = 0 := by
  have hi : iIndepFun (fun i : Fin N => fun ω : Fin N → U => ω i)
      (Measure.pi (fun _ : Fin N => μ)) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hd := (hi.indepFun_prodMk_prodMk (fun i => measurable_pi_apply i)
    i j l m hil him hjl hjm).comp hmA hmB
  have he := hd.integral_fun_mul_eq_mul_integral
    (hmA.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))).aestronglyMeasurable
    (hmB.comp ((measurable_pi_apply l).prodMk (measurable_pi_apply m))).aestronglyMeasurable
  simp only [Function.comp_def] at he
  rw [he]
  rw [spdB3_integral_comp (spdB3_pair_preserving μ hlm) B hmB, hmeanB, mul_zero]

lemma spdB3_distinct_pair_product_zero {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ} {A B : U × U → ℝ}
    (hmA : Measurable A) (hmB : Measurable B)
    (hA : MemLp A 2 (μ.prod μ)) (hB : MemLp B 2 (μ.prod μ))
    (hsA : ∀ u v, A (u, v) = A (v, u)) (hsB : ∀ u v, B (u, v) = B (v, u))
    (hcenter : ∀ᵐ u ∂μ, (∫ v, B (u, v) ∂μ) = 0)
    (hmean : (∫ uv, B uv ∂μ.prod μ) = 0)
    {i j l m : Fin N} (hij : i ≠ j) (hlm : l ≠ m)
    (hne : ¬((i = l ∧ j = m) ∨ (i = m ∧ j = l))) :
    (∫ ω : Fin N → U, A (ω i, ω j) * B (ω l, ω m)
      ∂Measure.pi (fun _ : Fin N => μ)) = 0 := by
  by_cases hil : i = l
  · subst l
    have hjm : j ≠ m := fun h => hne (Or.inl ⟨rfl, h⟩)
    exact spdB3_shared_sample_zero μ hmA hmB hA hB hcenter hij hlm hjm
  · by_cases him : i = m
    · subst m
      have hjl : j ≠ l := fun h => hne (Or.inr ⟨rfl, h⟩)
      calc
        _ = ∫ ω : Fin N → U, A (ω i, ω j) * B (ω i, ω l)
            ∂Measure.pi (fun _ : Fin N => μ) := by
          congr 1
          funext ω
          rw [hsB (ω l) (ω i)]
        _ = 0 := spdB3_shared_sample_zero μ hmA hmB hA hB hcenter hij hil hjl
    · by_cases hjl : j = l
      · subst l
        calc
          _ = ∫ ω : Fin N → U, A (ω j, ω i) * B (ω j, ω m)
              ∂Measure.pi (fun _ : Fin N => μ) := by
            congr 1
            funext ω
            rw [hsA (ω i) (ω j)]
          _ = 0 := spdB3_shared_sample_zero μ hmA hmB hA hB hcenter hij.symm hlm him
      · by_cases hjm : j = m
        · subst m
          calc
            _ = ∫ ω : Fin N → U, A (ω j, ω i) * B (ω j, ω l)
                ∂Measure.pi (fun _ : Fin N => μ) := by
              congr 1
              funext ω
              rw [hsA (ω i) (ω j), hsB (ω l) (ω j)]
            _ = 0 := spdB3_shared_sample_zero μ hmA hmB hA hB hcenter hij.symm hlm.symm hil
        · exact spdB3_disjoint_sample_zero μ hmA hmB hmean hij hlm hil him hjl hjm

lemma spdB3_sample_remainder_memLp {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d : Dyad N) (a : Fin k) :
    MemLp (fun ω : Fin N → U => spdB3_remainder K (ω (firstUnit d)) (ω (secondUnit d)) a)
      2 (unitSampleLaw K N) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  exact ((spdB3_remainder_memLp K hK a).mono_exponent (by simp)).comp_measurePreserving
    (corrected_pair_preserving K d)

lemma spdB3_sample_projection_memLp {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (i : Fin N) (a : Fin k) :
    MemLp (fun ω : Fin N → U => projection K (ω i) a) 2 (unitSampleLaw K N) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  exact ((spdB3_projection_memLp K hK a).mono_exponent (by simp)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin N => K.μ) i)

lemma spdB3_remainder_covariance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d f : Dyad N) (a b : Fin k) :
    covariance
      (fun ω : Fin N → U => spdB3_remainder K (ω (firstUnit d)) (ω (secondUnit d)) a)
      (fun ω : Fin N → U => spdB3_remainder K (ω (firstUnit f)) (ω (secondUnit f)) b)
      (unitSampleLaw K N) =
      if d = f then ∫ uv : U × U, spdB3_remainder K uv.1 uv.2 a *
        spdB3_remainder K uv.1 uv.2 b ∂K.μ.prod K.μ else 0 := by
  classical
  letI : IsProbabilityMeasure K.μ := hK.1
  have hm (a : Fin k) : Measurable (fun uv : U × U => spdB3_remainder K uv.1 uv.2 a) :=
    (measurable_pi_apply a).comp (spdB3_remainder_measurable K hK)
  have hs (a : Fin k) (u v : U) : spdB3_remainder K u v a = spdB3_remainder K v u a :=
    congrFun (spdB3_remainder_symmetric K hK u v) a
  rw [covariance_eq_sub (spdB3_sample_remainder_memLp K hK d a)
    (spdB3_sample_remainder_memLp K hK f b)]
  rw [corrected_pair_integral K d _ (hm a), spdB3_remainder_centered K hK a,
    zero_mul, sub_zero]
  by_cases hdf : d = f
  · subst f
    rw [if_pos rfl]
    exact corrected_pair_integral K d _ ((hm a).mul (hm b))
  · rw [if_neg hdf]
    apply spdB3_distinct_pair_product_zero K.μ (hm a) (hm b)
      ((spdB3_remainder_memLp K hK a).mono_exponent (by simp))
      ((spdB3_remainder_memLp K hK b).mono_exponent (by simp)) (hs a) (hs b)
      ((spdB3_remainder_degenerate K hK).mono fun u hu => congrFun hu b)
      (spdB3_remainder_centered K hK b) (printed_endpoints_lt d).ne (printed_endpoints_lt f).ne
    intro hp
    apply hdf
    apply Subtype.ext
    change members d = members f
    rw [printed_members_endpoints d, printed_members_endpoints f]
    rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂]
    · rw [h₁, h₂, Finset.pair_comm]

lemma spdB3_projection_covariance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (i j : Fin N) (a b : Fin k) :
    covariance (fun ω : Fin N → U => projection K (ω i) a)
      (fun ω : Fin N → U => projection K (ω j) b) (unitSampleLaw K N) =
      if i = j then projectionGamma K a b else 0 := by
  classical
  letI : IsProbabilityMeasure K.μ := hK.1
  have hm (a : Fin k) : Measurable (fun u => projection K u a) :=
    (measurable_pi_apply a).comp (spdB3_projection_measurable K hK)
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, covariance_eq_sub (spdB3_sample_projection_memLp K hK i a)
      (spdB3_sample_projection_memLp K hK i b)]
    change (∫ ω : Fin N → U, projection K (ω i) a * projection K (ω i) b
      ∂Measure.pi (fun _ : Fin N => K.μ)) -
      (∫ ω : Fin N → U, projection K (ω i) a ∂Measure.pi (fun _ : Fin N => K.μ)) *
      (∫ ω : Fin N → U, projection K (ω i) b ∂Measure.pi (fun _ : Fin N => K.μ)) =
        ∫ u, projection K u a * projection K u b ∂K.μ
    rw [spdB3_integral_comp (measurePreserving_eval (fun _ : Fin N => K.μ) i) _ (hm a)]
    have hz := congrFun (spdB3_projection_centered K hK) a
    change (∫ u, projection K u a ∂K.μ) = 0 at hz
    rw [hz, zero_mul, sub_zero]
    exact spdB3_integral_comp (measurePreserving_eval (fun _ : Fin N => K.μ) i) _
      ((hm a).mul (hm b))
  · rw [if_neg hij]
    have hi : iIndepFun (fun i : Fin N => fun ω : Fin N → U => ω i)
        (unitSampleLaw K N) := iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
    exact ((hi.indepFun hij).comp (hm a) (hm b)).covariance_eq_zero
      (spdB3_sample_projection_memLp K hK i a) (spdB3_sample_projection_memLp K hK j b)

lemma spdB3_unit_pair_product_zero {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {g : U → ℝ} {B : U × U → ℝ}
    (hg : MemLp g 2 μ) (hB : MemLp B 2 (μ.prod μ))
    (hcenter : ∀ᵐ u ∂μ, (∫ v, B (u, v) ∂μ) = 0) :
    (∫ uv : U × U, g uv.1 * B uv ∂μ.prod μ) = 0 := by
  have hip : Integrable (fun uv : U × U => g uv.1 * B uv) (μ.prod μ) :=
    (hg.comp_measurePreserving measurePreserving_fst).integrable_mul hB
  rw [integral_prod _ hip]
  simp only [integral_const_mul]
  exact integral_eq_zero_of_ae (hcenter.mono fun u hu => by
    change g u * (∫ v, B (u, v) ∂μ) = 0
    rw [hu, mul_zero])

lemma spdB3_projection_remainder_covariance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (i : Fin N) (d : Dyad N) (a b : Fin k) :
    covariance (fun ω : Fin N → U => projection K (ω i) a)
      (fun ω : Fin N → U => spdB3_remainder K (ω (firstUnit d)) (ω (secondUnit d)) b)
      (unitSampleLaw K N) = 0 := by
  letI : IsProbabilityMeasure K.μ := hK.1
  have hmG : Measurable (fun u => projection K u a) :=
    (measurable_pi_apply a).comp (spdB3_projection_measurable K hK)
  have hmR : Measurable (fun uv : U × U => spdB3_remainder K uv.1 uv.2 b) :=
    (measurable_pi_apply b).comp (spdB3_remainder_measurable K hK)
  have hzero : (∫ uv : U × U, projection K uv.1 a * spdB3_remainder K uv.1 uv.2 b
      ∂K.μ.prod K.μ) = 0 :=
    spdB3_unit_pair_product_zero K.μ
      ((spdB3_projection_memLp K hK a).mono_exponent (by simp))
      ((spdB3_remainder_memLp K hK b).mono_exponent (by simp))
      ((spdB3_remainder_degenerate K hK).mono fun u hu => congrFun hu b)
  by_cases hi : i = firstUnit d ∨ i = secondUnit d
  · rw [covariance_eq_sub (spdB3_sample_projection_memLp K hK i a)
      (spdB3_sample_remainder_memLp K hK d b),
      corrected_pair_integral K d _ hmR, spdB3_remainder_centered K hK b,
      mul_zero, sub_zero]
    rcases hi with rfl | rfl
    · exact (corrected_pair_integral K d _ ((hmG.comp measurable_fst).mul hmR)).trans hzero
    · calc
        _ = ∫ ω : Fin N → U, projection K (ω (secondUnit d)) a *
            spdB3_remainder K (ω (secondUnit d)) (ω (firstUnit d)) b
              ∂unitSampleLaw K N := by
          congr 1
          funext ω
          simp only [Pi.mul_apply]
          rw [spdB3_remainder_symmetric K hK (ω (firstUnit d)) (ω (secondUnit d))]
        _ = ∫ uv : U × U, projection K uv.1 a * spdB3_remainder K uv.1 uv.2 b
              ∂K.μ.prod K.μ :=
          spdB3_integral_comp (spdB3_pair_preserving K.μ (printed_endpoints_lt d).ne.symm) _
            ((hmG.comp measurable_fst).mul hmR)
        _ = 0 := hzero
  · have hi' := not_or.mp hi
    have hind : iIndepFun (fun i : Fin N => fun ω : Fin N → U => ω i)
        (unitSampleLaw K N) := iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
    have hp := (hind.indepFun_prodMk (fun i => measurable_pi_apply i)
      (firstUnit d) (secondUnit d) i (Ne.symm hi'.1) (Ne.symm hi'.2)).symm.comp hmG hmR
    exact hp.covariance_eq_zero (spdB3_sample_projection_memLp K hK i a)
      (spdB3_sample_remainder_memLp K hK d b)

lemma spdB3_projection_sum_variance {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (N : ℕ) :
    varMat (unitSampleLaw K N) (fun ω => ∑ i, projection K (ω i)) =
      (N : ℝ) • projectionGamma K := by
  classical
  letI : IsProbabilityMeasure K.μ := hK.1
  ext a b
  simp only [varMat, covMat, Finset.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [covariance_fun_sum_fun_sum (fun i => spdB3_sample_projection_memLp K hK i a)
    (fun i => spdB3_sample_projection_memLp K hK i b)]
  simp [spdB3_projection_covariance K hK]

lemma spdB3_remainder_sum_variance {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (N : ℕ) :
    varMat (unitSampleLaw K N) (fun ω => ∑ d : Dyad N,
      spdB3_remainder K (ω (firstUnit d)) (ω (secondUnit d))) =
      Dreal N • meanMat (K.μ.prod K.μ) (fun uv =>
        outer (spdB3_remainder K uv.1 uv.2) (spdB3_remainder K uv.1 uv.2)) := by
  classical
  letI : IsProbabilityMeasure K.μ := hK.1
  ext a b
  simp only [varMat, covMat, Finset.sum_apply, Matrix.smul_apply, smul_eq_mul, meanMat, outer]
  rw [covariance_fun_sum_fun_sum (fun d => spdB3_sample_remainder_memLp K hK d a)
    (fun d => spdB3_sample_remainder_memLp K hK d b)]
  simp [spdB3_remainder_covariance K hK, printed_card_real, printed_dyads_card_real]

lemma spdB3_sum_cross_covariance {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (N : ℕ) (a b : Fin k) :
    covariance (fun ω : Fin N → U => ∑ i, projection K (ω i) a)
      (fun ω : Fin N → U => ∑ d : Dyad N,
        spdB3_remainder K (ω (firstUnit d)) (ω (secondUnit d)) b) (unitSampleLaw K N) = 0 := by
  letI : IsProbabilityMeasure K.μ := hK.1
  rw [covariance_fun_sum_fun_sum (fun i => spdB3_sample_projection_memLp K hK i a)
    (fun d => spdB3_sample_remainder_memLp K hK d b)]
  simp [spdB3_projection_remainder_covariance K hK]

lemma spdB3_score_sum_decomposition {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (hN : 2 ≤ N) (ω : Fin N → U) :
    (Dreal N)⁻¹ • scoreSum K ω =
      (2 / (N : ℝ)) • (∑ i, projection K (ω i)) +
      (Dreal N)⁻¹ • (∑ d : Dyad N,
        spdB3_remainder K (ω (firstUnit d)) (ω (secondUnit d))) := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hc : (Dreal N)⁻¹ * ((N : ℝ) - 1) = 2 / (N : ℝ) := by
    unfold Dreal
    field_simp [hn0, hn1]
  ext a
  simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul]
  have hs : scoreSum K ω a =
      ((N : ℝ) - 1) * (∑ i, projection K (ω i) a) +
      ∑ d : Dyad N, spdB3_remainder K (ω (firstUnit d)) (ω (secondUnit d)) a := by
    rw [← printed_pair_add (fun i => projection K (ω i) a), ← Finset.sum_add_distrib]
    simp only [scoreSum, Finset.sum_apply, design, epsilon, populationScore, spdB3_remainder,
      Pi.sub_apply]
    apply Finset.sum_congr rfl
    intro d hd
    abel
  rw [hs, mul_add, ← mul_assoc, hc]

lemma spdB3_score_average_variance {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (N : ℕ) (hN : 2 ≤ N) :
    varMat (unitSampleLaw K N) (fun ω => (Dreal N)⁻¹ • scoreSum K ω) =
      (4 / (N : ℝ)) • projectionGamma K +
        (Dreal N)⁻¹ • meanMat (K.μ.prod K.μ) (fun uv =>
          outer (spdB3_remainder K uv.1 uv.2) (spdB3_remainder K uv.1 uv.2)) := by
  classical
  letI : IsProbabilityMeasure K.μ := hK.1
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd : Dreal N ≠ 0 := ne_of_gt (printed_Dpos hN)
  have hfun : (fun ω : Fin N → U => (Dreal N)⁻¹ • scoreSum K ω) =
      fun ω => (2 / (N : ℝ)) • (∑ i, projection K (ω i)) +
        (Dreal N)⁻¹ • (∑ d : Dyad N,
          spdB3_remainder K (ω (firstUnit d)) (ω (secondUnit d))) :=
    funext (spdB3_score_sum_decomposition K hK hN)
  rw [hfun]
  ext a b
  have hG (a : Fin k) : MemLp (fun ω : Fin N → U => ∑ i, projection K (ω i) a)
      2 (unitSampleLaw K N) := memLp_finsetSum _
        (fun i _ => spdB3_sample_projection_memLp K hK i a)
  have hR (a : Fin k) : MemLp (fun ω : Fin N → U => ∑ d : Dyad N,
      spdB3_remainder K (ω (firstUnit d)) (ω (secondUnit d)) a) 2 (unitSampleLaw K N) :=
    memLp_finsetSum _ (fun d _ => spdB3_sample_remainder_memLp K hK d a)
  simp only [varMat, covMat, Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul, Matrix.add_apply, Matrix.smul_apply]
  change covariance
    ((fun ω : Fin N → U => (2 / (N : ℝ)) * ∑ i, projection K (ω i) a) +
      (fun ω => (Dreal N)⁻¹ * ∑ d : Dyad N,
        spdB3_remainder K (ω (firstUnit d)) (ω (secondUnit d)) a))
    ((fun ω : Fin N → U => (2 / (N : ℝ)) * ∑ i, projection K (ω i) b) +
      (fun ω => (Dreal N)⁻¹ * ∑ d : Dyad N,
        spdB3_remainder K (ω (firstUnit d)) (ω (secondUnit d)) b))
    (unitSampleLaw K N) = _
  rw [covariance_add_left ((hG a).const_mul (2 / (N : ℝ))) ((hR a).const_mul (Dreal N)⁻¹)
    (((hG b).const_mul (2 / (N : ℝ))).add ((hR b).const_mul (Dreal N)⁻¹)),
    covariance_add_right ((hG a).const_mul (2 / (N : ℝ)))
      ((hG b).const_mul (2 / (N : ℝ))) ((hR b).const_mul (Dreal N)⁻¹),
    covariance_add_right ((hR a).const_mul (Dreal N)⁻¹)
      ((hG b).const_mul (2 / (N : ℝ))) ((hR b).const_mul (Dreal N)⁻¹)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  rw [spdB3_sum_cross_covariance K hK N a b,
    covariance_comm (fun ω : Fin N → U => ∑ d : Dyad N,
      spdB3_remainder K (ω (firstUnit d)) (ω (secondUnit d)) a),
    spdB3_sum_cross_covariance K hK N b a]
  have hGG := congrFun (congrFun (spdB3_projection_sum_variance K hK N) a) b
  have hRR := congrFun (congrFun (spdB3_remainder_sum_variance K hK N) a) b
  simp only [varMat, covMat, Finset.sum_apply, Matrix.smul_apply, smul_eq_mul] at hGG hRR
  rw [hGG, hRR]
  field_simp [hn.ne', hd]
  <;> ring

theorem score_projection_decomposition_proof {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    let r := fun u v => populationScore K u v-projection K u-projection K v
    meanVec K.μ (projection K) = 0 ∧
    (∀ᵐ u ∂ K.μ, meanVec K.μ (r u) = 0) ∧
    (∀ N : ℕ, 2 ≤ N → ∀ ω : Fin N → U,
      (Dreal N)⁻¹ • scoreSum K ω =
        (2/(N : ℝ)) • (∑ i, projection K (ω i)) +
        (Dreal N)⁻¹ • (∑ d : Dyad N, r (ω (firstUnit d)) (ω (secondUnit d)))) ∧
    (∀ N : ℕ, 2 ≤ N → varMat (unitSampleLaw K N) (fun ω => (Dreal N)⁻¹ • scoreSum K ω) =
      (4/(N : ℝ)) • projectionGamma K +
        (Dreal N)⁻¹ • meanMat (K.μ.prod K.μ) (fun uv => outer (r uv.1 uv.2) (r uv.1 uv.2))) := by
  exact ⟨spdB3_projection_centered K hK, spdB3_remainder_degenerate K hK,
    fun N hN ω => spdB3_score_sum_decomposition K hK hN ω,
    spdB3_score_average_variance K hK⟩

end AronowAudit.P018.Wave1
