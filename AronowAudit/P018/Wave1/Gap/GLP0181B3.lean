import AronowAudit.P018.P018_Audit
import AronowAudit.P018.Wave1.WeightedConsistency.G1
import AronowAudit.P018.Wave1.WeightedConsistency.G2
import AronowAudit.P018.Wave1.WeightedConsistency.G4
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecificLimits.Basic

/-! Proof of P018-T2, with the full design conditional covariance retained. -/
noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open WeightedConsistency in
lemma vc3_pair_preserving {U : Type*} [MeasurableSpace U] (μ : Measure U)
    [IsProbabilityMeasure μ] {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    MeasurePreserving (fun ω : Fin N → U => (ω i, ω j))
      (Measure.pi (fun _ => μ)) (μ.prod μ) :=
  ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), g1_proof μ i j hij⟩

lemma vc3_dyad_preserving {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) [IsProbabilityMeasure K.μ] (d : Dyad N) :
    MeasurePreserving (fun ω : Fin N → U => (ω (firstUnit d), ω (secondUnit d)))
      (unitSampleLaw K N) (K.μ.prod K.μ) :=
  vc3_pair_preserving K.μ _ _ (WeightedConsistency.firstUnit_ne_secondUnit d)

instance vc3_sample_probability {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) [IsProbabilityMeasure K.μ] :
    IsProbabilityMeasure (unitSampleLaw K N) := by
  unfold unitSampleLaw
  infer_instance

lemma vc3_pair_residual_measurable {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    Measurable (fun uv : U × U => populationResidual K uv.1 uv.2) := by
  exact hK.2.2.1.sub (Finset.measurable_sum _ (fun a _ =>
    ((measurable_pi_apply a).comp hK.2.1).mul_const _))

lemma vc3_pair_score_measurable {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (a : Fin k) :
    Measurable (fun uv : U × U => populationScore K uv.1 uv.2 a) :=
  (vc3_pair_residual_measurable K hK).mul ((measurable_pi_apply a).comp hK.2.1)

lemma vc3_pair_bounds {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ uv ∂ K.μ.prod K.μ,
      (∀ a, |K.X uv.1 uv.2 a| ≤ C) ∧ |populationResidual K uv.1 uv.2| ≤ C := by
  obtain ⟨B, hB, hb⟩ := hK.2.2.2.2.1
  let E : ℝ := B + ∑ a : Fin k, B * |populationBeta K a|
  have hE : 0 ≤ E := add_nonneg hB (Finset.sum_nonneg (fun _ _ =>
    mul_nonneg hB (abs_nonneg _)))
  refine ⟨B + E, add_nonneg hB hE, ?_⟩
  filter_upwards [hb] with uv huv
  have hx (a : Fin k) : |K.X uv.1 uv.2 a| ≤ B :=
    (norm_le_pi_norm (K.X uv.1 uv.2) a).trans huv.1
  constructor
  · intro a
    exact (hx a).trans (le_add_of_nonneg_right hE)
  · have he : |populationResidual K uv.1 uv.2| ≤ E := by
      calc
        _ ≤ |K.Y uv.1 uv.2| + |∑ a : Fin k,
            K.X uv.1 uv.2 a * populationBeta K a| := abs_sub _ _
        _ ≤ B + ∑ a : Fin k, |K.X uv.1 uv.2 a * populationBeta K a| :=
          add_le_add huv.2 (Finset.abs_sum_le_sum_abs _ _)
        _ ≤ E := by
          apply add_le_add (le_refl B)
          apply Finset.sum_le_sum
          intro a ha
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hx a) (abs_nonneg _)
    exact he.trans (le_add_of_nonneg_left hB)

lemma vc3_pair_X_lp {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (a : Fin k) (p : ℝ≥0∞) :
    MemLp (fun uv : U × U => K.X uv.1 uv.2 a) p (K.μ.prod K.μ) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  obtain ⟨C, hC, hb⟩ := vc3_pair_bounds K hK
  exact MemLp.of_bound ((measurable_pi_apply a).comp hK.2.1).aestronglyMeasurable C
    (hb.mono (fun uv huv => huv.1 a))

lemma vc3_pair_residual_lp {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (p : ℝ≥0∞) :
    MemLp (fun uv : U × U => populationResidual K uv.1 uv.2) p (K.μ.prod K.μ) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  obtain ⟨C, hC, hb⟩ := vc3_pair_bounds K hK
  exact MemLp.of_bound (vc3_pair_residual_measurable K hK).aestronglyMeasurable C
    (hb.mono (fun uv huv => huv.2))

lemma vc3_pair_score_lp {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (a : Fin k) (p : ℝ≥0∞) :
    MemLp (fun uv : U × U => populationScore K uv.1 uv.2 a) p (K.μ.prod K.μ) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  obtain ⟨C, hC, hb⟩ := vc3_pair_bounds K hK
  apply MemLp.of_bound (vc3_pair_score_measurable K hK a).aestronglyMeasurable (C*C)
  filter_upwards [hb] with uv huv
  change |populationResidual K uv.1 uv.2 * K.X uv.1 uv.2 a| ≤ C*C
  rw [abs_mul]
  exact mul_le_mul huv.2 (huv.1 a) (abs_nonneg _) hC

lemma vc3_design_measurable {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) : Measurable (@design U _ k N K) := by
  apply measurable_pi_lambda
  intro d
  have hp : Measurable (fun ω : Fin N → U => (ω (firstUnit d), ω (secondUnit d))) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  simpa only [Function.comp_def, design] using hK.2.1.comp hp

lemma vc3_X_lp {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d : Dyad N) (a : Fin k) (p : ℝ≥0∞) :
    MemLp (fun ω => design K ω d a) p (unitSampleLaw K N) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  exact (vc3_pair_X_lp K hK a p).comp_measurePreserving (vc3_dyad_preserving K d)

lemma vc3_epsilon_lp {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d : Dyad N) (p : ℝ≥0∞) :
    MemLp (fun ω => epsilon K ω d) p (unitSampleLaw K N) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  exact (vc3_pair_residual_lp K hK p).comp_measurePreserving (vc3_dyad_preserving K d)

lemma vc3_score_lp {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d : Dyad N) (a : Fin k) (p : ℝ≥0∞) :
    MemLp (fun ω => score (design K ω d) (epsilon K ω d) a) p (unitSampleLaw K N) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  exact (vc3_pair_score_lp K hK a p).comp_measurePreserving (vc3_dyad_preserving K d)

lemma vc3_population_mean {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    meanVec (K.μ.prod K.μ) (fun uv => populationScore K uv.1 uv.2) = 0 := by
  letI : IsProbabilityMeasure K.μ := hK.1
  let β := populationBeta K
  have hy : MemLp (fun uv : U × U => K.Y uv.1 uv.2) 2 (K.μ.prod K.μ) := by
    obtain ⟨B, hB, hb⟩ := hK.2.2.2.2.1
    exact MemLp.of_bound hK.2.2.1.aestronglyMeasurable B (hb.mono (fun _ h => h.2))
  have hxy (a : Fin k) : Integrable
      (fun uv : U × U => K.Y uv.1 uv.2 * K.X uv.1 uv.2 a) (K.μ.prod K.μ) :=
    hy.integrable_mul (vc3_pair_X_lp K hK a 2)
  have hxx (a b : Fin k) : Integrable
      (fun uv : U × U => (K.X uv.1 uv.2 a * K.X uv.1 uv.2 b) * β b)
        (K.μ.prod K.μ) :=
    ((vc3_pair_X_lp K hK a 2).integrable_mul (vc3_pair_X_lp K hK b 2)).mul_const (β b)
  have hid (a : Fin k) (uv : U × U) :
      populationScore K uv.1 uv.2 a = K.Y uv.1 uv.2 * K.X uv.1 uv.2 a -
        ∑ b, (K.X uv.1 uv.2 a * K.X uv.1 uv.2 b) * β b := by
    simp only [populationScore, populationResidual, score, Pi.smul_apply, smul_eq_mul,
      dot, sub_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    ring
  ext a
  change (∫ uv, populationScore K uv.1 uv.2 a ∂ K.μ.prod K.μ) = 0
  simp_rw [hid]
  rw [integral_sub (hxy a) (integrable_finset_sum univ (fun b _ => hxx a b)),
    integral_finset_sum univ (fun b _ => hxx a b)]
  simp_rw [integral_mul_const]
  have he : (populationGram K).mulVec β =
      meanVec (K.μ.prod K.μ) (fun uv => score (K.X uv.1 uv.2) (K.Y uv.1 uv.2)) := by
    dsimp [β, populationBeta]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hK.2.2.2.2.2.2), Matrix.one_mulVec]
  exact sub_eq_zero.mpr (congrFun he a).symm

lemma vc3_dyad_mean {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d : Dyad N) :
    meanVec (unitSampleLaw K N) (fun ω => score (design K ω d) (epsilon K ω d)) = 0 := by
  letI : IsProbabilityMeasure K.μ := hK.1
  ext a
  have hm := vc3_dyad_preserving K d
  change (∫ ω, populationScore K (ω (firstUnit d)) (ω (secondUnit d)) a
    ∂ unitSampleLaw K N) = 0
  have hi : (∫ ω, populationScore K (ω (firstUnit d)) (ω (secondUnit d)) a
      ∂ unitSampleLaw K N) = ∫ uv, populationScore K uv.1 uv.2 a ∂ K.μ.prod K.μ := by
    rw [← hm.map_eq]
    exact (integral_map hm.aemeasurable
      (vc3_pair_score_measurable K hK a).aestronglyMeasurable).symm
  change (∫ ω, populationScore K (ω (firstUnit d)) (ω (secondUnit d)) a
    ∂ unitSampleLaw K N) = _ at hi
  rw [hi]
  exact congrFun (vc3_population_mean K hK) a

lemma vc3_disjoint_covariance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d f : Dyad N) (hdf : ¬overlap d f) :
    covMat (unitSampleLaw K N)
      (fun ω => score (design K ω d) (epsilon K ω d))
      (fun ω => score (design K ω f) (epsilon K ω f)) = 0 := by
  letI : IsProbabilityMeasure K.μ := hK.1
  ext a b
  apply WeightedConsistency.g2_proof K.μ (members d) (members f)
  · exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hdf)
  · have hp : Measurable (fun ω : Fin N → U => (ω (firstUnit d), ω (secondUnit d))) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact (vc3_pair_score_measurable K hK a).comp hp
  · have hp : Measurable (fun ω : Fin N → U => (ω (firstUnit f), ω (secondUnit f))) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact (vc3_pair_score_measurable K hK b).comp hp
  · intro ω ω' he
    change populationScore K (ω (firstUnit d)) (ω (secondUnit d)) a = _
    rw [he _ (WeightedConsistency.firstUnit_mem d), he _ (WeightedConsistency.secondUnit_mem d)]
    rfl
  · intro ω ω' he
    change populationScore K (ω (firstUnit f)) (ω (secondUnit f)) b = _
    rw [he _ (WeightedConsistency.firstUnit_mem f), he _ (WeightedConsistency.secondUnit_mem f)]
    rfl
  · exact vc3_score_lp K hK d a 2
  · exact vc3_score_lp K hK f b 2

lemma vc3_disjoint_moment {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d f : Dyad N) (hdf : ¬overlap d f) :
    meanMat (unitSampleLaw K N) (fun ω => outer
      (score (design K ω d) (epsilon K ω d))
      (score (design K ω f) (epsilon K ω f))) = 0 := by
  letI : IsProbabilityMeasure K.μ := hK.1
  ext a b
  have hz1 := congrFun (vc3_dyad_mean K hK d) a
  have hz2 := congrFun (vc3_dyad_mean K hK f) b
  have hc := congrFun (congrFun (vc3_disjoint_covariance K hK d f hdf) a) b
  change covariance (fun ω => score (design K ω d) (epsilon K ω d) a)
    (fun ω => score (design K ω f) (epsilon K ω f) b) _ = 0 at hc
  rw [covariance_eq_sub (vc3_score_lp K hK d a 2) (vc3_score_lp K hK f b 2)] at hc
  change (∫ ω, score (design K ω d) (epsilon K ω d) a ∂ unitSampleLaw K N) = 0 at hz1
  change (∫ ω, score (design K ω f) (epsilon K ω f) b ∂ unitSampleLaw K N) = 0 at hz2
  change (∫ ω, score (design K ω d) (epsilon K ω d) a *
    score (design K ω f) (epsilon K ω f) b ∂unitSampleLaw K N) = 0
  change (∫ ω, score (design K ω d) (epsilon K ω d) a *
    score (design K ω f) (epsilon K ω f) b ∂unitSampleLaw K N) - _ = 0 at hc
  simpa only [hz1, hz2, zero_mul, sub_zero] using hc

lemma vc3_corrected_expand {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    correctedSigma K N = ∑ d : Dyad N, ∑ f : Dyad N,
      if overlap d f then meanMat (unitSampleLaw K N) (fun ω => outer
        (score (design K ω d) (epsilon K ω d))
        (score (design K ω f) (epsilon K ω f))) else 0 := by
  letI : IsProbabilityMeasure K.μ := hK.1
  have hi (d f : Dyad N) (a b : Fin k) : Integrable
      (fun ω => (if overlap d f then outer (score (design K ω d) (epsilon K ω d))
        (score (design K ω f) (epsilon K ω f)) else 0) a b) (unitSampleLaw K N) := by
    by_cases h : overlap d f
    · simp only [h, if_true]
      exact (vc3_score_lp K hK d a 2).integrable_mul (vc3_score_lp K hK f b 2)
    · simp only [h, if_false, Matrix.zero_apply]
      exact integrable_zero _ _ _
  ext a b
  simp only [correctedSigma, meanMat, meat, Matrix.sum_apply, Finset.sum_apply]
  change (∫ ω, ∑ d : Dyad N, ∑ f : Dyad N,
    (if overlap d f then outer (score (design K ω d) (epsilon K ω d))
      (score (design K ω f) (epsilon K ω f)) else 0) a b ∂unitSampleLaw K N) = _
  rw [integral_finsetSum univ (fun d _ => integrable_finset_sum univ (fun f _ => hi d f a b))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [integral_finsetSum univ (fun f _ => hi d f a b)]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases h : overlap d f
  · simp only [h, if_true]
    rfl
  · simp only [h, if_false, Matrix.zero_apply, integral_zero]

lemma vc3_sparse_variance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    varMat (unitSampleLaw K N) (scoreSum K) = correctedSigma K N := by
  letI : IsProbabilityMeasure K.μ := hK.1
  rw [vc3_corrected_expand K hK]
  exact variance_sparse_identity (unitSampleLaw K N) members
    (fun d ω => score (design K ω d) (epsilon K ω d))
    (fun d a => vc3_score_lp K hK d a 2) (vc3_dyad_mean K hK)
    (vc3_disjoint_covariance K hK)

lemma vc3_integrable_top {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : MemLp f ∞ μ) : Integrable f μ :=
  hf.integrable (by simp)

lemma vc3_design_le {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    @designSigma U _ k N K ≤ (inferInstance : MeasurableSpace (Fin N → U)) :=
  (vc3_design_measurable K hK).comap_le

lemma vc3_design_coordinate {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (d : Dyad N) (a : Fin k) :
    StronglyMeasurable[designSigma K] (fun ω => design K ω d a) := by
  have hx : @Measurable (Fin N → U) (Dyad N → Vec k) (designSigma K)
      inferInstance (design K) := comap_measurable (design K)
  exact ((measurable_pi_apply a).comp ((measurable_pi_apply d).comp hx)).stronglyMeasurable

lemma vc3_condmean_top {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d : Dyad N) :
    MemLp (conditionalResidualMean K d) ∞ (unitSampleLaw K N) :=
  (vc3_epsilon_lp K hK d ∞).condExp (by simp)

lemma vc3_condscore_top {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d : Dyad N) (a : Fin k) :
    MemLp (fun ω => score (design K ω d) (conditionalResidualMean K d ω) a)
      ∞ (unitSampleLaw K N) :=
  (vc3_condmean_top K hK d).mul (vc3_X_lp K hK d a ∞)

lemma vc3_score_projection {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d : Dyad N) (a : Fin k) :
    (unitSampleLaw K N)[(fun ω => score (design K ω d) (epsilon K ω d) a) | designSigma K]
      =ᵐ[unitSampleLaw K N]
        (fun ω => score (design K ω d) (conditionalResidualMean K d ω) a) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  exact condExp_mul_of_stronglyMeasurable_right (vc3_design_coordinate K d a)
    (vc3_integrable_top (vc3_score_lp K hK d a ∞))
    (vc3_integrable_top (vc3_epsilon_lp K hK d ∞))

/- The scalar conditional projection calculation uses only the pull-out and tower
   properties of conditional expectation. -/
lemma vc3_total_covariance {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    {X Y A B : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ)
    (hcX : μ[X | m] =ᵐ[μ] A) (hcY : μ[Y | m] =ᵐ[μ] B) :
    covariance X Y μ = (∫ ω, (X ω - A ω) * (Y ω - B ω) ∂μ) +
      covariance A B μ := by
  have hAm : AEStronglyMeasurable[m] A μ :=
    stronglyMeasurable_condExp.aestronglyMeasurable.congr hcX
  have hBm : AEStronglyMeasurable[m] B μ :=
    stronglyMeasurable_condExp.aestronglyMeasurable.congr hcY
  have hp (F G H : Ω → ℝ) (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
      (hGm : AEStronglyMeasurable[m] G μ) (hc : μ[F | m] =ᵐ[μ] H) :
      (∫ ω, F ω * G ω ∂μ) = ∫ ω, H ω * G ω ∂μ := by
    have h := condExp_mul_of_aestronglyMeasurable_right hGm
      (hF.integrable_mul hG) (hF.integrable (by norm_num))
    calc
      _ = ∫ ω, μ[F*G | m] ω ∂μ := (integral_condExp hm).symm
      _ = ∫ ω, μ[F | m] ω * G ω ∂μ := integral_congr_ae h
      _ = _ := integral_congr_ae (hc.mul (Filter.EventuallyEq.rfl))
  have hp1 := hp X B A hX hB hBm hcX
  have hp2 : (∫ ω, A ω * Y ω ∂μ) = ∫ ω, A ω * B ω ∂μ := by
    simpa only [mul_comm] using hp Y A B hY hA hAm hcY
  have hmA : (∫ ω, A ω ∂μ) = ∫ ω, X ω ∂μ :=
    (integral_congr_ae hcX.symm).trans (integral_condExp hm)
  have hmB : (∫ ω, B ω ∂μ) = ∫ ω, Y ω ∂μ :=
    (integral_congr_ae hcY.symm).trans (integral_condExp hm)
  have hfun : (fun ω => (X ω-A ω)*(Y ω-B ω)) =
      (X*Y-A*Y)-(X*B-A*B) := by
    funext ω
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  rw [hfun]
  change covariance X Y μ = (∫ ω,
    (X*Y-A*Y) ω - (X*B-A*B) ω ∂μ) + covariance A B μ
  rw [integral_sub
    ((hX.integrable_mul hY).sub (hA.integrable_mul hY))
    ((hX.integrable_mul hB).sub (hA.integrable_mul hB))]
  simp only [Pi.sub_apply]
  rw [integral_sub (hX.integrable_mul hY) (hA.integrable_mul hY),
    integral_sub (hX.integrable_mul hB) (hA.integrable_mul hB)]
  rw [covariance_eq_sub hX hY, covariance_eq_sub hA hB]
  simp only [Pi.mul_apply]
  rw [hp1, hp2, hmA, hmB]
  ring

lemma vc3_covariance_psd {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} (F : Ω → Vec k)
    (hF : ∀ a, MemLp (fun ω => F ω a) 2 μ) : (varMat μ F).PosSemidef := by
  have h := generic_score_meat_psd μ
    (fun ω (_ : Unit) => F ω - meanVec μ F) ()
    (fun a => (hF a).sub (memLp_const _))
  exact h

lemma vc3_condterm_entry {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d f : Dyad N) (a b : Fin k) :
    conditionalTerm K d f a b =
      ∫ ω, (score (design K ω d) (epsilon K ω d) a -
          score (design K ω d) (conditionalResidualMean K d ω) a) *
        (score (design K ω f) (epsilon K ω f) b -
          score (design K ω f) (conditionalResidualMean K f ω) b) ∂unitSampleLaw K N := by
  letI : IsProbabilityMeasure K.μ := hK.1
  let P := unitSampleLaw K N
  let A : (Fin N → U) → ℝ := fun ω => design K ω d a * design K ω f b
  let Z : (Fin N → U) → ℝ := fun ω =>
    (epsilon K ω d-conditionalResidualMean K d ω) *
    (epsilon K ω f-conditionalResidualMean K f ω)
  have hA : StronglyMeasurable[designSigma K] A :=
    (vc3_design_coordinate K d a).mul (vc3_design_coordinate K f b)
  have hAlp : MemLp A ∞ P := (vc3_X_lp K hK d a ∞).mul (vc3_X_lp K hK f b ∞)
  have hZlp : MemLp Z ∞ P :=
    ((vc3_epsilon_lp K hK d ∞).sub (vc3_condmean_top K hK d)).mul
      ((vc3_epsilon_lp K hK f ∞).sub (vc3_condmean_top K hK f))
  have hpull := condExp_mul_of_stronglyMeasurable_left hA
    (vc3_integrable_top (hAlp.mul hZlp)) (vc3_integrable_top hZlp)
  have hi : (∫ ω, A ω * Z ω ∂P) = ∫ ω, A ω * P[Z | designSigma K] ω ∂P := by
    change (∫ ω, (A*Z) ω ∂P) = _
    rw [← integral_condExp (vc3_design_le K hK) (μ := P) (f := A*Z)]
    exact integral_congr_ae hpull
  calc
    _ = ∫ ω, A ω * P[Z | designSigma K] ω ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      change (conditionalResidualCov K d f ω) *
        (design K ω d a * design K ω f b) = _
      exact mul_comm _ _
    _ = ∫ ω, A ω * Z ω ∂P := hi.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with ω
      dsimp [A, Z, score]
      ring

lemma vc3_conditional_decomposition {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    let M := varMat (unitSampleLaw K N) (fun ω => ∑ d : Dyad N,
      score (design K ω d) (conditionalResidualMean K d ω))
    varMat (unitSampleLaw K N) (scoreSum K) =
      (∑ d : Dyad N, ∑ f : Dyad N, conditionalTerm K d f) + M ∧
    M.PosSemidef ∧
    (varMat (unitSampleLaw K N) (scoreSum K) =
      (∑ d : Dyad N, ∑ f : Dyad N, conditionalTerm K d f) ↔ M = 0) ∧
    varMat (unitSampleLaw K N) (scoreSum K) - printedSigma K N =
      M + (∑ d : Dyad N, ∑ f : Dyad N, if ¬overlap d f then conditionalTerm K d f else 0) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  let P := unitSampleLaw K N
  let q : Dyad N → (Fin N → U) → Vec k :=
    fun d ω => score (design K ω d) (epsilon K ω d)
  let r : Dyad N → (Fin N → U) → Vec k :=
    fun d ω => score (design K ω d) (conditionalResidualMean K d ω)
  have hq (d : Dyad N) (a : Fin k) : MemLp (fun ω => q d ω a) 2 P :=
    vc3_score_lp K hK d a 2
  have hr (d : Dyad N) (a : Fin k) : MemLp (fun ω => r d ω a) 2 P :=
    (vc3_condscore_top K hK d a).mono_exponent (by simp)
  have hpair (d f : Dyad N) :
      covMat P (q d) (q f) = conditionalTerm K d f + covMat P (r d) (r f) := by
    ext a b
    rw [Matrix.add_apply, vc3_condterm_entry K hK]
    exact vc3_total_covariance P (designSigma K) (vc3_design_le K hK)
      (hq d a) (hq f b) (hr d a) (hr f b)
      (vc3_score_projection K hK d a) (vc3_score_projection K hK f b)
  have hdecomp : varMat P (scoreSum K) =
      (∑ d : Dyad N, ∑ f : Dyad N, conditionalTerm K d f) +
        varMat P (fun ω => ∑ d, r d ω) := by
    change varMat P (fun ω => ∑ d, q d ω) = _
    rw [variance_sum_identity P q hq, variance_sum_identity P r hr]
    simp_rw [hpair, Finset.sum_add_distrib]
  have hsplit : (∑ d : Dyad N, ∑ f : Dyad N, conditionalTerm K d f) =
      printedSigma K N +
        (∑ d : Dyad N, ∑ f : Dyad N, if ¬overlap d f then conditionalTerm K d f else 0) := by
    unfold printedSigma
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro f hf
    by_cases h : overlap d f <;> simp [h]
  refine ⟨hdecomp, ?_, ?_, ?_⟩
  · apply vc3_covariance_psd
    intro a
    simpa only [Finset.sum_apply] using memLp_finsetSum univ (fun d _ => hr d a)
  · rw [hdecomp]
    simp only [add_eq_left]
    rfl
  · rw [hdecomp, hsplit]
    abel

def vc3_other {N : ℕ} (i : Fin N) (d : Dyad N) : Fin N :=
  if firstUnit d = i then secondUnit d else firstUnit d

lemma vc3_members_other {N : ℕ} (i : Fin N) (d : Dyad N) (hi : i ∈ members d) :
    members d = {i, vc3_other i d} := by
  rw [WeightedConsistency.members_eq_endpoints] at hi ⊢
  simp only [mem_insert, mem_singleton] at hi
  dsimp [vc3_other]
  rcases hi with hi | hi
  · simp [hi.symm]
  · by_cases h : firstUnit d = i
    · simp [h, hi.symm]
    · simp [h, hi.symm, pair_comm]

lemma vc3_other_ne {N : ℕ} (i : Fin N) (d : Dyad N) (hi : i ∈ members d) :
    i ≠ vc3_other i d := by
  apply Finset.card_pair_eq_two_iff.mp
  rw [← vc3_members_other i d hi, members_card]

lemma vc3_incident_count {N : ℕ} (i : Fin N) :
    (∑ d : Dyad N, if i ∈ members d then (1 : ℝ) else 0) = (N : ℝ)-1 := by
  classical
  let s : Finset (Dyad N) := univ.filter (fun d => i ∈ members d)
  have hs : (∑ d ∈ s, (1 : ℝ)) = ∑ j ∈ (univ : Finset (Fin N)).erase i, (1 : ℝ) := by
    apply Finset.sum_bij (fun d _ => vc3_other i d)
    · intro d hd
      exact mem_erase.mpr ⟨(vc3_other_ne i d (mem_filter.mp hd).2).symm, mem_univ _⟩
    · intro d hd f hf hdf
      apply Subtype.ext
      change members d = members f
      rw [vc3_members_other i d (mem_filter.mp hd).2,
        vc3_members_other i f (mem_filter.mp hf).2, hdf]
    · intro j hj
      have hji : j ≠ i := (mem_erase.mp hj).1
      let d : Dyad N := ⟨{i,j}, by simp [dyads, Finset.mem_powersetCard, hji.symm]⟩
      have hdi : i ∈ members d := by simp [d, members]
      refine ⟨d, by simp [s, hdi], ?_⟩
      have hmem : vc3_other i d ∈ members d := by
        rw [vc3_members_other i d hdi]
        simp
      change vc3_other i d ∈ ({i,j} : Finset (Fin N)) at hmem
      rcases mem_insert.mp hmem with h | h
      · exact False.elim ((vc3_other_ne i d hdi) h.symm)
      · exact mem_singleton.mp h
    · intro d hd
      rfl
  have hN : 1 ≤ N := by have := i.isLt; omega
  have hc : ((N-1 : ℕ) : ℝ) = (N : ℝ)-1 := by rw [Nat.cast_sub hN]; norm_num
  simpa [s, Finset.sum_filter, Finset.card_erase_of_mem, hc] using hs

lemma vc3_overlap_row {N : ℕ} (d : Dyad N) :
    (∑ f : Dyad N, if overlap d f then (1 : ℝ) else 0) = 2*(N : ℝ)-3 := by
  classical
  have hint (f : Dyad N) : ((members d ∩ members f).card : ℝ) =
      ∑ i ∈ members d, if i ∈ members f then (1 : ℝ) else 0 := by
    have he : (members d).filter (fun i => i ∈ members f) = members d ∩ members f := by
      ext i
      simp
    simp [← Finset.sum_filter, he]
  have hsum : (∑ f : Dyad N, ((members d ∩ members f).card : ℝ)) = 2*((N : ℝ)-1) := by
    simp_rw [hint]
    rw [Finset.sum_comm]
    simp_rw [vc3_incident_count]
    simp [members_card]
    ring
  have hsplit : (∑ f : Dyad N, ((members d ∩ members f).card : ℝ)) =
      (∑ f : Dyad N, if overlap d f then (1 : ℝ) else 0) + 1 := by
    simp_rw [intersection_count members members_card (fun d f h => Subtype.ext h)]
    simp [Finset.sum_add_distrib, overlap]
  linarith

lemma vc3_card_real (N : ℕ) : (Fintype.card (Dyad N) : ℝ) = Dreal N := by
  rw [number_of_dyads]
  exact Nat.cast_choose_two ℝ N

lemma vc3_score_symmetric {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (u v : U) :
    populationScore K u v = populationScore K v u := by
  simp only [populationScore, populationResidual, (hK.2.2.2.1 u v).1,
    (hK.2.2.2.1 u v).2]

lemma vc3_score_at_members {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d : Dyad N) (i j : Fin N)
    (hij : i ≠ j) (hd : members d = {i,j}) (ω : Fin N → U) :
    score (design K ω d) (epsilon K ω d) = populationScore K (ω i) (ω j) := by
  have he : ({firstUnit d, secondUnit d} : Set (Fin N)) = {i,j} := by
    have hh := (WeightedConsistency.members_eq_endpoints d).symm.trans hd
    have hh' := congrArg (fun s : Finset (Fin N) => (s : Set (Fin N))) hh
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hh'
  rcases Set.pair_eq_pair_iff.mp he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · change populationScore K (ω (firstUnit d)) (ω (secondUnit d)) = _
    rw [h₁,h₂]
  · change populationScore K (ω (firstUnit d)) (ω (secondUnit d)) = _
    rw [h₁,h₂, vc3_score_symmetric K hK]

lemma vc3_triple_preserving {U : Type*} [MeasurableSpace U] (μ : Measure U)
    [IsProbabilityMeasure μ] {N : ℕ} (i j l : Fin N)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    MeasurePreserving (fun ω : Fin N → U => ((ω i, ω j), ω l))
      (Measure.pi (fun _ => μ)) ((μ.prod μ).prod μ) := by
  have hind : iIndepFun (fun i : Fin N => fun ω : Fin N → U => ω i)
      (Measure.pi (fun _ => μ)) := iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  refine ⟨((measurable_pi_apply i).prodMk (measurable_pi_apply j)).prodMk (measurable_pi_apply l), ?_⟩
  rw [(hind.indepFun_prodMk (fun i => measurable_pi_apply i) i j l hil hjl).map_prod_eq_prod_map_map
    ((measurable_pi_apply i).aemeasurable.prodMk (measurable_pi_apply j).aemeasurable)
    (measurable_pi_apply l).aemeasurable, (vc3_pair_preserving μ i j hij).map_eq,
    (measurePreserving_eval (fun _ : Fin N => μ) l).map_eq]

lemma vc3_shared_integral {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (a b : Fin k) :
    (∫ z : (U × U) × U,
      populationScore K z.1.1 z.1.2 a * populationScore K z.1.1 z.2 b
      ∂ (K.μ.prod K.μ).prod K.μ) = projectionGamma K a b := by
  letI : IsProbabilityMeasure K.μ := hK.1
  have h₁ : MemLp (fun z : (U × U) × U => populationScore K z.1.1 z.1.2 a)
      2 ((K.μ.prod K.μ).prod K.μ) :=
    (vc3_pair_score_lp K hK a 2).comp_measurePreserving measurePreserving_fst
  have hm : MeasurePreserving (fun z : (U × U) × U => (z.1.1,z.2))
      ((K.μ.prod K.μ).prod K.μ) (K.μ.prod K.μ) :=
    measurePreserving_fst.prod (MeasurePreserving.id K.μ)
  have h₂ : MemLp (fun z : (U × U) × U => populationScore K z.1.1 z.2 b)
      2 ((K.μ.prod K.μ).prod K.μ) :=
    (vc3_pair_score_lp K hK b 2).comp_measurePreserving hm
  have hi : Integrable (fun z : (U × U) × U =>
      populationScore K z.1.1 z.1.2 a * populationScore K z.1.1 z.2 b)
      ((K.μ.prod K.μ).prod K.μ) := h₁.integrable_mul h₂
  have hp : Integrable (fun uv : U × U =>
      populationScore K uv.1 uv.2 a * projection K uv.1 b) (K.μ.prod K.μ) := by
    simpa only [integral_const_mul, projection, meanVec] using hi.integral_prod_left
  rw [integral_prod _ hi]
  simp only [integral_const_mul]
  change (∫ uv : U × U, populationScore K uv.1 uv.2 a * projection K uv.1 b
    ∂K.μ.prod K.μ) = _
  rw [integral_prod _ hp]
  simp only [integral_mul_const]
  rfl

lemma vc3_projection_lp {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (a : Fin k) :
    MemLp (fun u => projection K u a) 2 K.μ := by
  letI : IsProbabilityMeasure K.μ := hK.1
  obtain ⟨C, hC, hb⟩ := vc3_pair_bounds K hK
  have hg : Measurable (fun u => projection K u a) :=
    (vc3_pair_score_measurable K hK a).stronglyMeasurable.integral_prod_right'.measurable
  apply MemLp.of_bound hg.aestronglyMeasurable (C*C)
  filter_upwards [Measure.ae_ae_of_ae_prod hb] with u hu
  have hh : ∀ᵐ v ∂K.μ, ‖populationScore K u v a‖ ≤ C*C := by
    filter_upwards [hu] with v hv
    change |populationResidual K u v * K.X u v a| ≤ C*C
    rw [abs_mul]
    exact mul_le_mul hv.2 (hv.1 a) (abs_nonneg _) hC
  simpa only [projection, meanVec, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hh

lemma vc3_projection_psd {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) : (projectionGamma K).PosSemidef := by
  letI : IsProbabilityMeasure K.μ := hK.1
  exact generic_score_meat_psd K.μ (fun u (_ : Unit) => projection K u) ()
    (vc3_projection_lp K hK)

lemma vc3_same_moment {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d : Dyad N) :
    meanMat (unitSampleLaw K N) (fun ω => outer
      (score (design K ω d) (epsilon K ω d))
      (score (design K ω d) (epsilon K ω d))) = scoreH K := by
  letI : IsProbabilityMeasure K.μ := hK.1
  ext a b
  have hm := vc3_dyad_preserving K d
  change (∫ ω, populationScore K (ω (firstUnit d)) (ω (secondUnit d)) a *
    populationScore K (ω (firstUnit d)) (ω (secondUnit d)) b ∂unitSampleLaw K N) =
    ∫ uv, populationScore K uv.1 uv.2 a * populationScore K uv.1 uv.2 b ∂K.μ.prod K.μ
  rw [← hm.map_eq]
  exact (integral_map hm.aemeasurable
    ((vc3_pair_score_measurable K hK a).mul
      (vc3_pair_score_measurable K hK b)).aestronglyMeasurable).symm

lemma vc3_overlap_moment {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d f : Dyad N)
    (hne : d ≠ f) (hov : overlap d f) :
    meanMat (unitSampleLaw K N) (fun ω => outer
      (score (design K ω d) (epsilon K ω d))
      (score (design K ω f) (epsilon K ω f))) = projectionGamma K := by
  letI : IsProbabilityMeasure K.μ := hK.1
  obtain ⟨i, hi⟩ := hov
  obtain ⟨hid, hif⟩ := Finset.mem_inter.mp hi
  let j := vc3_other i d
  let l := vc3_other i f
  have hij : i ≠ j := vc3_other_ne i d hid
  have hil : i ≠ l := vc3_other_ne i f hif
  have hjl : j ≠ l := by
    intro h
    apply hne
    apply Subtype.ext
    change members d = members f
    rw [vc3_members_other i d hid, vc3_members_other i f hif]
    exact congrArg (fun x => ({i,x} : Finset (Fin N))) h
  have hm := vc3_triple_preserving K.μ i j l hij hil hjl
  ext a b
  change (∫ ω, score (design K ω d) (epsilon K ω d) a *
    score (design K ω f) (epsilon K ω f) b ∂unitSampleLaw K N) = _
  calc
    _ = ∫ ω, populationScore K (ω i) (ω j) a *
        populationScore K (ω i) (ω l) b ∂unitSampleLaw K N := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [vc3_score_at_members K hK d i j hij (vc3_members_other i d hid),
        vc3_score_at_members K hK f i l hil (vc3_members_other i f hif)]
    _ = ∫ z : (U × U) × U, populationScore K z.1.1 z.1.2 a *
        populationScore K z.1.1 z.2 b ∂(K.μ.prod K.μ).prod K.μ := by
      rw [← hm.map_eq]
      have hg : Measurable (fun z : (U × U) × U =>
          populationScore K z.1.1 z.1.2 a * populationScore K z.1.1 z.2 b) :=
        ((vc3_pair_score_measurable K hK a).comp measurable_fst).mul
          ((vc3_pair_score_measurable K hK b).comp (measurable_fst.fst.prodMk measurable_snd))
      exact (integral_map hm.aemeasurable hg.aestronglyMeasurable).symm
    _ = _ := vc3_shared_integral K hK a b

lemma vc3_closed_covariance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    correctedSigma K N = (Dreal N) • scoreH K +
      ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) • projectionGamma K := by
  classical
  rw [vc3_corrected_expand K hK]
  ext a b
  have hterm (d f : Dyad N) :
      (if overlap d f then meanMat (unitSampleLaw K N) (fun ω => outer
        (score (design K ω d) (epsilon K ω d))
        (score (design K ω f) (epsilon K ω f))) else 0) a b =
      (if f=d then scoreH K a b else 0) +
      (if overlap d f then projectionGamma K a b else 0) -
      (if f=d then projectionGamma K a b else 0) := by
    by_cases hfd : f=d
    · subst f
      have hd : overlap d d := by
        change (members d ∩ members d).Nonempty
        rw [inter_self]
        exact card_pos.mp (by rw [members_card]; norm_num)
      simp only [hd, if_true, vc3_same_moment K hK d]
      ring
    · by_cases hov : overlap d f
      · simp only [hov, if_true, hfd, if_false,
          vc3_overlap_moment K hK d f (Ne.symm hfd) hov]
        ring
      · simp only [hov, if_false, hfd, Matrix.zero_apply, zero_add, sub_zero]
  have hrow (d : Dyad N) :
      (∑ f : Dyad N, if overlap d f then projectionGamma K a b else 0) =
        (2*(N : ℝ)-3)*projectionGamma K a b := by
    rw [← vc3_overlap_row d, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro f hf
    split_ifs <;> simp
  simp only [Matrix.sum_apply, Finset.sum_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, hrow]
  simp only [Finset.sum_ite_eq', mem_univ, if_true, Finset.sum_const, card_univ,
    nsmul_eq_mul, vc3_card_real]
  unfold Dreal
  ring

lemma vc3_coefficient_limits :
    Tendsto (fun N : ℕ => 2/((N : ℝ)-1)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => 4*((N : ℝ)-2)/((N : ℝ)-1)) atTop (𝓝 4) := by
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun N : ℕ => 1-(N : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hi
  have hnum : Tendsto (fun N : ℕ => 1-2*(N : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hi.const_mul 2)
  have heq (N : ℕ) (hN : 2 ≤ N) :
      2*(N : ℝ)⁻¹/(1-(N : ℝ)⁻¹) = 2/((N : ℝ)-1) ∧
      4*(1-2*(N : ℝ)⁻¹)/(1-(N : ℝ)⁻¹) = 4*((N : ℝ)-2)/((N : ℝ)-1) := by
    have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hn0 : (N : ℝ) ≠ 0 := by linarith
    have hn1 : (N : ℝ)-1 ≠ 0 := by linarith
    have hd : 1-(N : ℝ)⁻¹ ≠ 0 := by
      intro hzero
      field_simp [hn0] at hzero
      linarith
    constructor <;> field_simp [hn0, hn1, hd] <;> ring
  constructor
  · have h : Tendsto (fun N : ℕ => 2*(N : ℝ)⁻¹/(1-(N : ℝ)⁻¹)) atTop (𝓝 0) := by
      have ht := (hi.const_mul 2).div hden (by norm_num)
      convert ht using 1 <;> norm_num
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact (heq N hN).1
  · have h : Tendsto (fun N : ℕ => 4*(1-2*(N : ℝ)⁻¹)/(1-(N : ℝ)⁻¹)) atTop (𝓝 4) := by
      have ht := (hnum.const_mul 4).div hden (by norm_num)
      convert ht using 1 <;> norm_num
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact (heq N hN).2

lemma vc3_target_limit {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    Tendsto (trueTarget K) atTop (𝓝 (limitingTarget K)) := by
  have ha := vc3_coefficient_limits.1
  have hb := vc3_coefficient_limits.2
  have hh := (ha.smul (tendsto_const_nhds
      (x := sandwich (populationGram K)⁻¹ (scoreH K)))).add
    (hb.smul (tendsto_const_nhds
      (x := sandwich (populationGram K)⁻¹ (projectionGamma K))))
  have h : Tendsto (fun N : ℕ =>
      (2/((N : ℝ)-1)) • sandwich (populationGram K)⁻¹ (scoreH K) +
      (4*((N : ℝ)-2)/((N : ℝ)-1)) • sandwich (populationGram K)⁻¹ (projectionGamma K))
      atTop (𝓝 (limitingTarget K)) := by
    simpa only [zero_smul, zero_add, limitingTarget] using hh
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ)-1 ≠ 0 := by linarith
  have hc1 : (N : ℝ)/(Dreal N)^2 * Dreal N = 2/((N : ℝ)-1) := by
    unfold Dreal
    field_simp [hn0, hn1]
    <;> ring
  have hc2 : (N : ℝ)/(Dreal N)^2 * ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) =
      4*((N : ℝ)-2)/((N : ℝ)-1) := by
    unfold Dreal
    field_simp [hn0, hn1]
    <;> ring
  unfold trueTarget
  rw [vc3_sparse_variance K hK, vc3_closed_covariance K hK]
  simp only [sandwich, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_add, smul_smul, hc1, hc2]

theorem variance_correction_proof {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    (meanVec (K.μ.prod K.μ) (fun uv => populationScore K uv.1 uv.2) = 0) ∧
    (∀ N : ℕ, 2 ≤ N →
      (∀ d : Dyad N, meanVec (unitSampleLaw K N) (fun ω => score (design K ω d) (epsilon K ω d)) = 0) ∧
      (∀ d f : Dyad N, ¬overlap d f →
        meanMat (unitSampleLaw K N) (fun ω => outer (score (design K ω d) (epsilon K ω d))
          (score (design K ω f) (epsilon K ω f))) = 0) ∧
      varMat (unitSampleLaw K N) (scoreSum K) = correctedSigma K N ∧
      let M := varMat (unitSampleLaw K N) (fun ω => ∑ d : Dyad N,
        score (design K ω d) (conditionalResidualMean K d ω))
      varMat (unitSampleLaw K N) (scoreSum K) = (∑ d : Dyad N, ∑ f : Dyad N, conditionalTerm K d f) + M ∧
      M.PosSemidef ∧
      (varMat (unitSampleLaw K N) (scoreSum K) = (∑ d : Dyad N, ∑ f : Dyad N, conditionalTerm K d f) ↔ M = 0) ∧
      varMat (unitSampleLaw K N) (scoreSum K) - printedSigma K N =
        M + (∑ d : Dyad N, ∑ f : Dyad N, if ¬overlap d f then conditionalTerm K d f else 0) ∧
      correctedSigma K N = (Dreal N) • scoreH K +
        ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) • projectionGamma K) ∧
    (projectionGamma K).PosSemidef ∧
    Tendsto (trueTarget K) atTop (𝓝 (limitingTarget K)) := by
  refine ⟨vc3_population_mean K hK, ?_, vc3_projection_psd K hK, vc3_target_limit K hK⟩
  intro N hN
  refine ⟨vc3_dyad_mean K hK, vc3_disjoint_moment K hK, vc3_sparse_variance K hK, ?_⟩
  have hc := vc3_conditional_decomposition (N := N) K hK
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, vc3_closed_covariance K hK⟩

end AronowAudit.P018.Wave1
