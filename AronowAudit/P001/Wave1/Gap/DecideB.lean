import AronowAudit.P001.P001_Foundations
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
Common regularity sets for P001-T12: score measurability, consistency, and asymptotic normality.
-/

open MeasureTheory ProbabilityTheory Filter AronowAudit.P001
open scoped BigOperators ENNReal NNReal Topology Matrix
open scoped Matrix.Norms.Elementwise

namespace AronowAudit.P001.Wave1

noncomputable section
local instance instDecidableDecideB (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false
set_option linter.unusedVariables false

/-- A measurable full-law set transfers to every iid observation, simultaneously. -/
theorem DecideB_ae_all_mem {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → E)
    (hiid : IID μ Z) (S : Set E) (hS : MeasurableSet S)
    (hfull : (μ.map (Z 0)) S = 1) : ∀ᵐ ω ∂μ, ∀ i, Z i ω ∈ S := by
  apply ae_all_iff.mpr
  intro i
  have hbase : ∀ᵐ z ∂μ.map (Z 0), z ∈ S :=
    (mem_ae_iff_prob_eq_one hS).mpr hfull
  rw [← (hiid.2.2 i).map_eq] at hbase
  exact (ae_map_iff (hiid.1 i).aemeasurable hS).mp hbase


/-- Coordinate gradient of the actual average log likelihood. -/
def DecideB_sampleScore {Ω : Type*} {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (n : ℕ) (ω : Ω) (t : Fin τ → ℝ) : Fin τ → ℝ :=
  fun j => (∑ i ∈ Finset.range n, modelScore g (Y i ω) (X i ω) t j) / (n : ℝ)

/-- Finite differentiation of the average criterion on an open regular set. -/
theorem DecideB_sampleScore_eq_fderiv {Ω : Type*} {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (n : ℕ) (ω : Ω) (U : Set (Fin τ → ℝ)) (hU : IsOpen U)
    (hdiff : ∀ i, ContDiffOn ℝ 2 (fun t => Real.log (g (Y i ω) (X i ω) t)) U)
    (t : Fin τ → ℝ) (ht : t ∈ U) (j : Fin τ) :
    DecideB_sampleScore X Y g n ω t j =
      fderiv ℝ (sampleLogLikelihood X Y g n ω) t (Pi.single j 1) := by
  have hd (i : ℕ) : DifferentiableAt ℝ (fun u => Real.log (g (Y i ω) (X i ω) u)) t :=
    ((hdiff i).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)
  have hsum := HasFDerivAt.fun_sum (u := Finset.range n)
    (fun i (_ : i ∈ Finset.range n) => (hd i).hasFDerivAt)
  have hf := (hsum.mul_const (n : ℝ)⁻¹).fderiv
  change _ = fderiv ℝ (fun u => (∑ i ∈ Finset.range n,
    Real.log (g (Y i ω) (X i ω) u)) / (n : ℝ)) t (Pi.single j 1)
  simp only [div_eq_mul_inv]
  rw [hf]
  simp [DecideB_sampleScore, modelScore, div_eq_mul_inv, mul_comm]

/-- Each coordinate score is C¹ on the same open regular set. -/
theorem DecideB_modelScore_contDiffOn {K τ : ℕ}
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (y : ℝ) (x : Fin K → ℝ) (U : Set (Fin τ → ℝ)) (hU : IsOpen U)
    (hdiff : ContDiffOn ℝ 2 (fun t => Real.log (g y x t)) U) (j : Fin τ) :
    ContDiffOn ℝ 1 (fun t => modelScore g y x t j) U := by
  exact (hdiff.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const

/-- The derivative of the average score is exactly the stated sample Hessian. -/
theorem DecideB_sampleHessian_eq_fderiv {Ω : Type*} {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (n : ℕ) (ω : Ω) (U : Set (Fin τ → ℝ)) (hU : IsOpen U)
    (hdiff : ∀ i, ContDiffOn ℝ 2 (fun t => Real.log (g (Y i ω) (X i ω) t)) U)
    (t : Fin τ → ℝ) (ht : t ∈ U) (j k : Fin τ) :
    sampleHessian X Y g n ω t j k =
      fderiv ℝ (fun u => DecideB_sampleScore X Y g n ω u j) t (Pi.single k 1) := by
  have hd (i : ℕ) : DifferentiableAt ℝ (fun u => modelScore g (Y i ω) (X i ω) u j) t :=
    ((DecideB_modelScore_contDiffOn g _ _ U hU (hdiff i) j).differentiableOn
      (by norm_num)).differentiableAt (hU.mem_nhds ht)
  have hsum := HasFDerivAt.fun_sum (u := Finset.range n)
    (fun i (_ : i ∈ Finset.range n) => (hd i).hasFDerivAt)
  have hf := (hsum.mul_const (n : ℝ)⁻¹).fderiv
  change _ = fderiv ℝ (fun u => (∑ i ∈ Finset.range n,
    modelScore g (Y i ω) (X i ω) u j) / (n : ℝ)) t (Pi.single k 1)
  simp only [div_eq_mul_inv]
  rw [hf]
  simp [sampleHessian, modelHessian, div_eq_mul_inv, mul_comm]

/-- Interior log maximizers have zero sample score, on the common smooth event. -/
theorem DecideB_log_maximizer_score_zero {Ω : Type*} {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (n : ℕ) (ω : Ω) (Θ U : Set (Fin τ → ℝ)) (hU : IsOpen U) (hUΘ : U ⊆ Θ)
    (hdiff : ∀ i, ContDiffOn ℝ 2 (fun t => Real.log (g (Y i ω) (X i ω) t)) U)
    (t : Fin τ → ℝ) (ht : t ∈ U)
    (hmax : ∀ u ∈ Θ, sampleLogLikelihood X Y g n ω u ≤ sampleLogLikelihood X Y g n ω t) :
    DecideB_sampleScore X Y g n ω t = 0 := by
  have hlocal : IsLocalMax (sampleLogLikelihood X Y g n ω) t := by
    filter_upwards [hU.mem_nhds ht] with u hu
    exact hmax u (hUΘ hu)
  ext j
  rw [DecideB_sampleScore_eq_fderiv X Y g n ω U hU hdiff t ht j, hlocal.fderiv_eq_zero]
  rfl

/-- Positivity only on the regular neighborhood suffices for product/log comparison. -/
theorem DecideB_product_le_iff_log_le {Ω : Type*} {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (n : ℕ) (hn : 0 < n) (ω : Ω) (t u : Fin τ → ℝ)
    (ht : ∀ i, 0 < g (Y i ω) (X i ω) t)
    (hu : ∀ i, 0 < g (Y i ω) (X i ω) u) :
    sampleLikelihood X Y g n ω t ≤ sampleLikelihood X Y g n ω u ↔
      sampleLogLikelihood X Y g n ω t ≤ sampleLogLikelihood X Y g n ω u := by
  have htp : 0 < sampleLikelihood X Y g n ω t := Finset.prod_pos (fun i _ => ht i)
  have hup : 0 < sampleLikelihood X Y g n ω u := Finset.prod_pos (fun i _ => hu i)
  have heq (v : Fin τ → ℝ) (hv : ∀ i, 0 < g (Y i ω) (X i ω) v) :
      sampleLogLikelihood X Y g n ω v = Real.log (sampleLikelihood X Y g n ω v) / n := by
    simp only [sampleLogLikelihood, sampleMean, sampleLikelihood]
    rw [Real.log_prod (fun i _ => (hv i).ne')]
  rw [heq t ht, heq u hu, div_le_div_iff_of_pos_right (by exact_mod_cast hn)]
  exact (Real.log_le_log_iff htp hup).symm

/-- A derivative on a common measurable regularity set has a Borel version.
The countable difference quotients use only measurable parameter sections. -/
theorem DecideB_measurable_directional_version {E V : Type*} [MeasurableSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : E → V → ℝ) (S : Set E) (hS : MeasurableSet S)
    (U : Set V) (hU : IsOpen U) (t : V) (ht : t ∈ U) (v : V)
    (hm : ∀ u ∈ U, Measurable (fun z => f z u))
    (hd : ∀ z ∈ S, DifferentiableAt ℝ (f z) t) :
    Measurable (S.indicator (fun z => fderiv ℝ (f z) t v)) := by
  let q : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hq : Tendsto q atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_mono
      (fun n : ℕ => le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
      tendsto_natCast_atTop_atTop)
  have hqne : ∀ n, q n ≠ 0 := by intro n; dsimp [q]; positivity
  have hq' : Tendsto q atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hq
      (Eventually.of_forall (fun n => hqne n))
  have hpoints : ∀ᶠ n in atTop, t + q n • v ∈ U := by
    have hl : Tendsto (fun n => t + q n • v) atTop (𝓝 t) := by
      simpa using tendsto_const_nhds.add (hq.smul_const v)
    exact hl (hU.mem_nhds ht)
  let A : ℕ → E → ℝ := fun n => S.indicator (fun z =>
    (q n)⁻¹ * ((if t + q n • v ∈ U then f z (t + q n • v) else f z t) - f z t))
  have hAm (n : ℕ) : Measurable (A n) := by
    apply Measurable.indicator _ hS
    apply Measurable.const_mul
    apply Measurable.sub _ (hm t ht)
    split_ifs with h
    · exact hm _ h
    · exact hm t ht
  apply measurable_of_tendsto_metrizable hAm
  apply tendsto_pi_nhds.mpr
  intro z
  by_cases hz : z ∈ S
  · have hline : HasDerivAt (fun r : ℝ => f z (t + r • v))
        (fderiv ℝ (f z) t v) 0 := by
      have hl : HasDerivAt (fun r : ℝ => t + r • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add t
      exact (hd z hz).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
    have hh := hline.tendsto_slope_zero.comp hq'
    simp only [Set.indicator_of_mem hz]
    apply hh.congr'
    filter_upwards [hpoints] with n hn
    simp [A, hz, hn, smul_eq_mul, Function.comp_apply]
  · simpa [A, hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- The score version is zero off the common regular set. -/
def DecideB_scoreVersion {K τ : ℕ}
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (S : Set ((Fin K → ℝ) × ℝ)) (θ : Fin τ → ℝ) :
    ((Fin K → ℝ) × ℝ) → Fin τ → ℝ :=
  S.indicator (fun xy => modelScore g xy.2 xy.1 θ)

theorem DecideB_scoreVersion_measurable {K τ : ℕ}
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (S : Set ((Fin K → ℝ) × ℝ)) (hS : MeasurableSet S)
    (U : Set (Fin τ → ℝ)) (hU : IsOpen U) (θ : Fin τ → ℝ) (hθ : θ ∈ U)
    (hg : ∀ t ∈ U, Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
    (hdiff : ∀ xy ∈ S, ContDiffOn ℝ 2 (fun t => Real.log (g xy.2 xy.1 t)) U) :
    Measurable (DecideB_scoreVersion g S θ) := by
  apply measurable_pi_lambda
  intro j
  have hd (xy) (hxy : xy ∈ S) :
      DifferentiableAt ℝ (fun t => Real.log (g xy.2 xy.1 t)) θ :=
    ((hdiff xy hxy).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hθ)
  have hm := DecideB_measurable_directional_version
    (fun xy t => Real.log (g xy.2 xy.1 t)) S hS U hU θ hθ (Pi.single j 1)
    (fun t ht => (hg t ht).log) hd
  convert hm using 1
  ext xy
  by_cases h : xy ∈ S <;> simp [DecideB_scoreVersion, modelScore, h]

/-- All iid score vectors have the same measurable observation-space version. -/
theorem DecideB_scoreVersion_iid {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (S : Set ((Fin K → ℝ) × ℝ)) (hS : MeasurableSet S)
    (hfull : (μ.map (fun ω => (X 0 ω, Y 0 ω))) S = 1)
    (θ : Fin τ → ℝ) (hm : Measurable (DecideB_scoreVersion g S θ)) :
    IID μ (fun i ω => DecideB_scoreVersion g S θ (X i ω, Y i ω)) ∧
      (∀ᵐ ω ∂μ, ∀ i, DecideB_scoreVersion g S θ (X i ω, Y i ω) =
        modelScore g (Y i ω) (X i ω) θ) := by
  refine ⟨⟨fun i => hm.comp (hiid.1 i), hiid.2.1.comp (fun _ => _) (fun _ => hm),
    fun i => (hiid.2.2 i).comp hm⟩, ?_⟩
  filter_upwards [DecideB_ae_all_mem μ _ hiid S hS hfull] with ω hω
  intro i
  simp [DecideB_scoreVersion, hω i]

/-- The outer-probability definition of convergence in probability agrees with Mathlib's. -/
theorem DecideB_cp_iff_tendstoInMeasure {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : ℕ → Ω → E) (c : E) :
    CP μ Z c ↔ TendstoInMeasure μ Z atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  rfl

/-- Convergence in distribution implies convergence of integrals of bounded continuous test functions. -/
theorem DecideB_weakLimit_of_tendstoInDistribution {Ω E : Type*}
    [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → E)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (h : TendstoInDistribution Z atTop id (fun _ => μ) ν) : WeakLimit μ Z ν := by
  intro f hf hb
  let F : BoundedContinuousFunction E ℝ := ⟨⟨f, hf⟩, by
    obtain ⟨C, hC⟩ := hb
    exact ⟨2 * C, fun x y => (dist_le_norm_add_norm _ _).trans (by
      simpa only [Real.norm_eq_abs, two_mul] using add_le_add (hC x) (hC y))⟩⟩
  exact (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    h.forall_aemeasurable h.aemeasurable_limit).mp h F

/-- Finite linear combinations of L² coordinates can be multiplied under the integral. -/
theorem DecideB_mean_linear_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {d e : ℕ} (f : Ω → Fin d → ℝ) (g : Ω → Fin e → ℝ)
    (hf : ∀ j, MemLp (fun ω => f ω j) 2 μ)
    (hg : ∀ k, MemLp (fun ω => g ω k) 2 μ) (a : Fin d → ℝ) (b : Fin e → ℝ) :
    mean μ (fun ω => (∑ j, a j * f ω j) * (∑ k, b k * g ω k)) =
      ∑ j, ∑ k, a j * mean μ (fun ω => f ω j * g ω k) * b k := by
  have hterm (j : Fin d) (k : Fin e) :
      Integrable (fun ω => a j * (f ω j * g ω k) * b k) μ :=
    (((hf j).integrable_mul (hg k)).const_mul _).mul_const _
  have he (ω : Ω) :
      (∑ j, a j * f ω j) * (∑ k, b k * g ω k) =
        ∑ j, ∑ k, a j * (f ω j * g ω k) * b k := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold mean
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hterm j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _ => hterm j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_mul_const, integral_const_mul]

instance DecideB_instProbability_normalVectorLaw {d : ℕ} (I : Matrix (Fin d) (Fin d) ℝ) :
    IsProbabilityMeasure (normalVectorLaw I) := by
  unfold normalVectorLaw
  infer_instance

/-- The centered finite-dimensional iid CLT, including singular covariance and d = 0. -/
theorem DecideB_vector_clt_distribution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (s : ℕ → Ω → Fin d → ℝ) (hiid : IID μ s)
    (hs2 : ∀ j, MemLp (fun ω => s 0 ω j) 2 μ)
    (hs0 : ∀ j, mean μ (fun ω => s 0 ω j) = 0)
    (I : Matrix (Fin d) (Fin d) ℝ) (hI : I.PosSemidef)
    (hcov : ∀ j k, I j k = mean μ (fun ω => s 0 ω j * s 0 ω k)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ • (fun j => ∑ i ∈ Finset.range n, s i ω j))
      atTop id (fun _ => μ) (normalVectorLaw I) := by
  let Z : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun n ω =>
    WithLp.toLp 2 ((Real.sqrt n)⁻¹ • (fun j => ∑ i ∈ Finset.range n, s i ω j))
  have hZm (n : ℕ) : Measurable (Z n) := by
    have hm (i : ℕ) (j : Fin d) : Measurable (fun ω => s i ω j) :=
      (measurable_pi_apply j).comp (hiid.1 i)
    exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda
      (fun j => (Finset.measurable_sum _ (fun i _ => hm i j)).const_mul _))
  have hdist : TendstoInDistribution Z atTop id (fun _ => μ)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) I) := by
    apply TendstoInDistribution.of_tendsto_charFun (fun n => (hZm n).aemeasurable)
      measurable_id.aemeasurable
    intro t
    let w : (Fin d → ℝ) → ℝ := fun x => ∑ j, t j * x j
    have hwm : Measurable w := Finset.measurable_sum _
      (fun j _ => (measurable_pi_apply j).const_mul _)
    have hw2 : MemLp (fun ω => w (s 0 ω)) 2 μ :=
      memLp_finsetSum Finset.univ (fun j _ => (hs2 j).const_mul _)
    have hw0 : mean μ (fun ω => w (s 0 ω)) = 0 := by
      unfold mean
      rw [integral_finsetSum Finset.univ (fun j _ =>
        ((hs2 j).integrable (by norm_num)).const_mul _)]
      simp only [integral_const_mul, show ∀ j, (∫ ω, s 0 ω j ∂μ) = 0 from hs0,
        mul_zero, Finset.sum_const_zero]
    have hwvar : variance (fun ω => w (s 0 ω)) μ = t ⬝ᵥ I *ᵥ t := by
      rw [variance_eq_integral hw2.aemeasurable]
      change (∫ ω, (w (s 0 ω) - mean μ (fun ω => w (s 0 ω))) ^ 2 ∂μ) = _
      rw [hw0]
      simp only [sub_zero, pow_two]
      rw [show (∫ ω, w (s 0 ω) * w (s 0 ω) ∂μ) =
        mean μ (fun ω => (∑ j, t j * s 0 ω j) * (∑ k, t k * s 0 ω k)) from rfl,
        DecideB_mean_linear_mul μ (s 0) (s 0) hs2 hs2]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← hcov, mul_assoc]
    have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub
      (X := fun i ω => w (s i ω)) (P := μ)
      (Y := id) (P' := gaussianReal 0 (variance (fun ω => w (s 0 ω)) μ).toNNReal)
      HasLaw.id hw2 (hiid.2.1.comp (fun _ => w) (fun _ => hwm))
      (fun i => (hiid.2.2 i).comp hwm)
    have hh := hclt.tendsto_charFun 1
    have hproj (n : ℕ) :
        (fun ω => (Real.sqrt n)⁻¹ *
          (∑ i ∈ Finset.range n, w (s i ω) - (n : ℝ) * mean μ (fun ω => w (s 0 ω)))) =
        fun ω => inner ℝ (Z n ω) t := by
      ext ω
      simp only [hw0, mul_zero, sub_zero, Z, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, Pi.smul_apply, smul_eq_mul]
      dsimp [w]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    change Tendsto (fun (n : ℕ) => charFun (μ.map (fun ω => (Real.sqrt n)⁻¹ *
      (∑ i ∈ Finset.range n, w (s i ω) - (n : ℝ) * mean μ (fun ω => w (s 0 ω))))) 1)
      atTop (𝓝 (charFun ((gaussianReal 0 (variance (fun ω => w (s 0 ω)) μ).toNNReal).map id) 1)) at hh
    simp_rw [hproj] at hh
    have hvarnn : ((variance (fun ω => w (s 0 ω)) μ).toNNReal : ℝ) =
        t ⬝ᵥ I *ᵥ t := by rw [Real.coe_toNNReal _ (variance_nonneg _ _), hwvar]
    simpa only [Measure.map_id, charFun_map_eq_charFun_map_inner_one (hZm _).aemeasurable,
      charFun_gaussianReal, charFun_multivariateGaussian hI, inner_zero_right,
      Complex.ofReal_zero, Complex.ofReal_one, zero_mul, mul_zero, zero_sub,
      one_pow, mul_one, hvarnn, neg_div] using hh
  have hpi := hdist.continuous_comp
    (g := fun z : EuclideanSpace ℝ (Fin d) => fun j => z j)
    (by fun_prop)
  refine ⟨?_, measurable_id.aemeasurable, ?_⟩
  · simpa only [Function.comp_def, Z, PiLp.toLp_apply] using hpi.forall_aemeasurable
  · convert! hpi.tendsto using 1
    simp only [Measure.map_id, normalVectorLaw, Function.comp_id]


/-- The inverse-information transform of the centered score has covariance I⁻¹. -/
theorem DecideB_inverse_information_clt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (s : ℕ → Ω → Fin d → ℝ) (hiid : IID μ s)
    (hs2 : ∀ j, MemLp (fun ω => s 0 ω j) 2 μ)
    (hs0 : ∀ j, mean μ (fun ω => s 0 ω j) = 0)
    (I : Matrix (Fin d) (Fin d) ℝ) (hI : I.PosDef)
    (hcov : ∀ j k, I j k = mean μ (fun ω => s 0 ω j * s 0 ω k)) :
    TendstoInDistribution (fun (n : ℕ) ω => I⁻¹ *ᵥ
      ((Real.sqrt n)⁻¹ • (fun j => ∑ i ∈ Finset.range n, s i ω j)))
      atTop id (fun _ => μ) (normalVectorLaw I⁻¹) := by
  let A := I⁻¹
  let w : (Fin d → ℝ) → Fin d → ℝ := fun v => A *ᵥ v
  have hwm : Measurable w := by
    apply measurable_pi_lambda
    intro j
    change Measurable (fun v : Fin d → ℝ => ∑ k, A j k * v k)
    exact Finset.measurable_sum _ (fun k _ => (measurable_pi_apply k).const_mul _)
  have hwiid : IID μ (fun i ω => w (s i ω)) :=
    ⟨fun i => hwm.comp (hiid.1 i), hiid.2.1.comp (fun _ => w) (fun _ => hwm),
      fun i => (hiid.2.2 i).comp hwm⟩
  have hw2 (j : Fin d) : MemLp (fun ω => w (s 0 ω) j) 2 μ :=
    memLp_finsetSum Finset.univ (fun k _ => (hs2 k).const_mul _)
  have hw0 (j : Fin d) : mean μ (fun ω => w (s 0 ω) j) = 0 := by
    change (∫ ω, ∑ k, A j k * s 0 ω k ∂μ) = 0
    rw [integral_finsetSum Finset.univ (fun k _ =>
      ((hs2 k).integrable (by norm_num)).const_mul _)]
    simp only [integral_const_mul, show ∀ k, (∫ ω, s 0 ω k ∂μ) = 0 from hs0,
      mul_zero, Finset.sum_const_zero]
  have hsym : Aᵀ = A := hI.inv.isHermitian.isSymm
  have hcovw (j k : Fin d) : A j k = mean μ (fun ω => w (s 0 ω) j * w (s 0 ω) k) := by
    rw [show mean μ (fun ω => w (s 0 ω) j * w (s 0 ω) k) =
      mean μ (fun ω => (∑ l, A j l * s 0 ω l) * (∑ m, A k m * s 0 ω m)) from rfl,
      DecideB_mean_linear_mul μ (s 0) (s 0) hs2 hs2]
    simp only [← hcov]
    have he : (∑ l, ∑ m, A j l * I l m * A k m) = (A * I * Aᵀ) j k := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [he, hsym]
    have hu : IsUnit I.det := I.isUnit_iff_isUnit_det.mp hI.isUnit
    dsimp [A]
    rw [I.nonsing_inv_mul hu, Matrix.one_mul]
  have hclt := DecideB_vector_clt_distribution μ (fun i ω => w (s i ω)) hwiid hw2 hw0
    A hI.inv.posSemidef hcovw
  apply hclt.congr _ (Filter.EventuallyEq.refl _ _)
  intro n
  apply Filter.Eventually.of_forall
  intro ω
  ext j
  simp only [w, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The normalization is valid also for the empty sample. -/
theorem DecideB_sqrt_div_nat (n : ℕ) : Real.sqrt n / n = (Real.sqrt n)⁻¹ := by
  by_cases hn : n = 0
  · simp [hn]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hs : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  field_simp
  simpa [pow_two] using Real.sq_sqrt (Nat.cast_nonneg n)


/-- A coordinate bound gives an operator-norm bound for a real linear functional. -/
theorem DecideB_functional_norm_le {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ)
    (b : ℝ) (hb : 0 ≤ b) (h : ∀ k, |L (Pi.single k 1)| ≤ b) :
    ‖L‖ ≤ (d : ℝ) * b := by
  apply L.opNorm_le_bound (by positivity)
  intro v
  have hv : v = ∑ k, v k • Pi.single k (1 : ℝ) := by
    ext k
    simp [Pi.single_apply]
  calc
    ‖L v‖ = ‖∑ k, v k * L (Pi.single k 1)‖ := by
      conv_lhs => rw [hv]
      simp
    _ ≤ ∑ k, ‖v k * L (Pi.single k 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin d, ‖v‖ * b := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm v k) (h k) (norm_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * b * ‖v‖ := by simp; ring

/-- A mean-value bound for a vector gradient. No common multivariate mean-value
point is assumed: the scalar theorem is applied separately to each coordinate. -/
theorem DecideB_gradient_remainder_bound {d : ℕ}
    (F : (Fin d → ℝ) → Fin d → ℝ) (J : Matrix (Fin d) (Fin d) ℝ)
    (U : Set (Fin d → ℝ)) (hconv : Convex ℝ U)
    (x y : Fin d → ℝ) (hx : x ∈ U) (hy : y ∈ U)
    (hd : ∀ t ∈ U, ∀ j, DifferentiableAt ℝ (fun u => F u j) t)
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ t ∈ U, ∀ j k, |fderiv ℝ (fun u => F u j) t (Pi.single k 1) - J j k| ≤ b) :
    ‖F y - F x - J *ᵥ (y - x)‖ ≤ (d : ℝ) * b * ‖y - x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  let L : (Fin d → ℝ) →L[ℝ] ℝ :=
    ∑ k, J j k • (ContinuousLinearMap.proj k : (Fin d → ℝ) →L[ℝ] ℝ)
  have hL (v : Fin d → ℝ) : L v = ∑ k, J j k * v k := by simp [L]
  let f : (Fin d → ℝ) → ℝ := fun t => F t j - L t
  have hfd (t : Fin d → ℝ) (ht : t ∈ U) : DifferentiableAt ℝ f t :=
    (hd t ht j).sub L.differentiableAt
  have hfnorm (t : Fin d → ℝ) (ht : t ∈ U) : ‖fderiv ℝ f t‖ ≤ (d : ℝ) * b := by
    apply DecideB_functional_norm_le _ b hb
    intro k
    rw [(hfd t ht).hasFDerivAt.fderiv]
    have he : fderiv ℝ f t = fderiv ℝ (fun u => F u j) t - L :=
      ((hd t ht j).hasFDerivAt.sub L.hasFDerivAt).fderiv
    rw [he]
    simpa [hL, Pi.single_apply] using hbound t ht j k
  have h := hconv.norm_image_sub_le_of_norm_fderiv_le hfd hfnorm hx hy
  change ‖F y j - F x j - ∑ k, J j k * (y k - x k)‖ ≤ _
  convert h using 2
  dsimp [f]
  rw [hL y, hL x]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

/-- Sup norm versus the sum of coordinate squares. -/
theorem DecideB_norm_sq_le_sum_sq {d : ℕ} (v : Fin d → ℝ) :
    ‖v‖ ^ 2 ≤ ∑ k, (v k) ^ 2 := by
  have hs : 0 ≤ ∑ k, (v k) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : ‖v‖ ≤ Real.sqrt (∑ k, (v k) ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro k
    rw [Real.norm_eq_abs, Real.le_sqrt (abs_nonneg _) hs]
    simpa only [sq_abs] using
      (Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin d))) => sq_nonneg (v k))
        (Finset.mem_univ k))
  nlinarith [Real.sq_sqrt hs, norm_nonneg v, Real.sqrt_nonneg (∑ k, (v k) ^ 2)]

/-- A measurable matrix built from the score at truth and the estimation error.
It equals the information matrix plus a small rank-one correction. -/
def DecideB_scoreMatrix {d : ℕ} (I : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k => I j k + (u j - (I *ᵥ v) j) * v k / (∑ l, (v l) ^ 2)

theorem DecideB_scoreMatrix_mulVec {d : ℕ} (I : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (hv : v ≠ 0) : DecideB_scoreMatrix I u v *ᵥ v = u := by
  have hp : 0 < ∑ l, (v l) ^ 2 :=
    lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hv)) (DecideB_norm_sq_le_sum_sq v)
  ext j
  simp only [DecideB_scoreMatrix, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]
  have he : (∑ k, ((u j - ∑ x, I j x * v x) * v k / (∑ l, v l ^ 2)) * v k) =
      u j - ∑ x, I j x * v x := by
    calc
      _ = (u j - ∑ x, I j x * v x) * (∑ k, v k ^ 2) / (∑ l, v l ^ 2) := by
        simp only [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := mul_div_cancel_right₀ _ hp.ne'
  rw [he]
  ring

theorem DecideB_scoreMatrix_zero {d : ℕ} (I : Matrix (Fin d) (Fin d) ℝ)
    (u : Fin d → ℝ) : DecideB_scoreMatrix I u 0 = I := by
  ext j k
  simp [DecideB_scoreMatrix]

/-- Small score linearization error implies a small matrix correction. -/
theorem DecideB_scoreMatrix_bound {d : ℕ} (I : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hrem : ‖u - I *ᵥ v‖ ≤ b * ‖v‖) :
    ∀ j k, |DecideB_scoreMatrix I u v j k - I j k| ≤ b := by
  intro j k
  by_cases hv : v = 0
  · simp [hv, DecideB_scoreMatrix_zero, hb]
  have hp : 0 < ∑ l, (v l) ^ 2 :=
    lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hv)) (DecideB_norm_sq_le_sum_sq v)
  simp only [DecideB_scoreMatrix, add_sub_cancel_left, abs_div, abs_mul,
    abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  calc
    |u j - (I *ᵥ v) j| * |v k| ≤ ‖u - I *ᵥ v‖ * ‖v‖ :=
      mul_le_mul (norm_le_pi_norm (u - I *ᵥ v) j) (norm_le_pi_norm v k)
        (abs_nonneg _) (norm_nonneg _)
    _ ≤ b * ‖v‖ * ‖v‖ := mul_le_mul_of_nonneg_right hrem (norm_nonneg _)
    _ ≤ b * (∑ l, (v l) ^ 2) := by
      rw [mul_assoc, ← pow_two]
      exact mul_le_mul_of_nonneg_left (DecideB_norm_sq_le_sum_sq v) hb

/-- Two outer-probability controls suffice for localization; no measurability
of the control sequences or of the events is assumed. -/
theorem DecideB_cp_of_two_controls {Ω E F G : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [PseudoMetricSpace F] [PseudoMetricSpace G]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → E) (z : E) (A : ℕ → Ω → F) (a : F) (B : ℕ → Ω → G) (b : G)
    (hA : CP μ A a) (hB : CP μ B b)
    (hlocal : ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧
      ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, dist (A n ω) a < α → dist (B n ω) b < β →
        dist (Z n ω) z < ε) : CP μ Z z := by
  intro ε hε
  obtain ⟨α, hα, β, hβ, hl⟩ := hlocal ε hε
  have hbound : ∀ᶠ n in atTop, prob μ {ω | ε ≤ dist (Z n ω) z} ≤
      prob μ {ω | α ≤ dist (A n ω) a} + prob μ {ω | β ≤ dist (B n ω) b} := by
    filter_upwards [hl] with n hn
    calc
      _ ≤ prob μ ({ω | α ≤ dist (A n ω) a} ∪ {ω | β ≤ dist (B n ω) b}) := by
        apply ENNReal.toReal_mono (measure_ne_top μ _)
        apply measure_mono_ae
        filter_upwards [hn] with ω hω
        intro hz
        by_contra h
        have ha : dist (A n ω) a < α := lt_of_not_ge (fun ha => h (Or.inl ha))
        have hb : dist (B n ω) b < β := lt_of_not_ge (fun hb => h (Or.inr hb))
        exact (not_lt_of_ge hz) (hω ha hb)
      _ ≤ _ := measureReal_union_le _ _
  exact squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) hbound
    (by simpa only [zero_add] using (hA α hα).add (hB β hβ))

theorem DecideB_sampleScore_contDiffOn {Ω : Type*} {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (n : ℕ) (ω : Ω) (U : Set (Fin τ → ℝ)) (hU : IsOpen U)
    (hdiff : ∀ i, ContDiffOn ℝ 2 (fun t => Real.log (g (Y i ω) (X i ω) t)) U)
    (j : Fin τ) : ContDiffOn ℝ 1 (fun t => DecideB_sampleScore X Y g n ω t j) U :=
  (ContDiffOn.sum (fun i (_ : i ∈ Finset.range n) =>
    DecideB_modelScore_contDiffOn g _ _ U hU (hdiff i) j)).div_const _

/-- Uniform Hessian control and consistency imply convergence of the
measurable score-based linearization matrix. -/
theorem DecideB_scoreMatrix_cp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (θ : Fin τ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hdiff : ∀ᵐ ω ∂μ, ∀ i, ContDiffOn ℝ 2
      (fun t => Real.log (g (Y i ω) (X i ω) t)) (Metric.ball θ δ))
    (I : Matrix (Fin τ) (Fin τ) ℝ)
    (hHinfo : populationHessian μ (X 0) (Y 0) g θ = -I)
    (hHcont : ContinuousAt (populationHessian μ (X 0) (Y 0) g) θ)
    (ΔH : ℕ → Ω → ℝ)
    (hHbound : ∀ n ω t, t ∈ Metric.ball θ δ → ∀ j k,
      |sampleHessian X Y g n ω t j k - populationHessian μ (X 0) (Y 0) g t j k| ≤ ΔH n ω)
    (hHlim : CP μ ΔH 0) (that : ℕ → Ω → Fin τ → ℝ)
    (hconsistent : CP μ that θ)
    (hzero : ∀ n, ∀ᵐ ω ∂μ, that n ω ∈ Metric.ball θ δ →
      DecideB_sampleScore X Y g n ω (that n ω) = 0) :
    CP μ (fun n ω => DecideB_scoreMatrix I (DecideB_sampleScore X Y g n ω θ)
      (that n ω - θ)) I := by
  apply DecideB_cp_of_two_controls μ _ I ΔH 0 that θ hHlim hconsistent
  intro ε hε
  let b : ℝ := ε / (4 * ((τ : ℝ) + 1))
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨r, hr, hc⟩ := Metric.continuousAt_iff.mp hHcont b hb
  let ρ : ℝ := min r δ
  have hρ : 0 < ρ := lt_min hr hδ
  refine ⟨b, hb, ρ, hρ, Eventually.of_forall (fun n => ?_)⟩
  filter_upwards [hdiff, hzero n] with ω hω hz
  intro hΔ ht
  have hΔ' : ΔH n ω < b := by
    have h := hΔ
    rw [Real.dist_eq, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  have hsmall : that n ω ∈ Metric.ball θ ρ := ht
  have hsub : Metric.ball θ ρ ⊆ Metric.ball θ δ :=
    Metric.ball_subset_ball (min_le_right r δ)
  have hs : DecideB_sampleScore X Y g n ω (that n ω) = 0 := hz (hsub hsmall)
  have hdiff' (i : ℕ) : ContDiffOn ℝ 2
      (fun t => Real.log (g (Y i ω) (X i ω) t)) (Metric.ball θ ρ) :=
    (hω i).mono hsub
  have hJ (t : Fin τ → ℝ) (htt : t ∈ Metric.ball θ ρ) (j k : Fin τ) :
      |fderiv ℝ (fun u => DecideB_sampleScore X Y g n ω u j) t (Pi.single k 1) - (-I) j k| ≤ 2 * b := by
    rw [← DecideB_sampleHessian_eq_fderiv X Y g n ω (Metric.ball θ ρ)
      Metric.isOpen_ball hdiff' t htt j k]
    have hpop : |populationHessian μ (X 0) (Y 0) g t j k - (-I) j k| < b := by
      have hc' := hc (lt_of_lt_of_le htt (min_le_left r δ))
      rw [hHinfo, dist_eq_norm] at hc'
      exact lt_of_le_of_lt
        ((norm_le_pi_norm ((populationHessian μ (X 0) (Y 0) g t - -I) j) k).trans
          (norm_le_pi_norm (populationHessian μ (X 0) (Y 0) g t - -I) j)) hc'
    calc
      _ ≤ |sampleHessian X Y g n ω t j k - populationHessian μ (X 0) (Y 0) g t j k| +
          |populationHessian μ (X 0) (Y 0) g t j k - (-I) j k| := abs_sub_le _ _ _
      _ ≤ ΔH n ω + b := add_le_add (hHbound n ω t (hsub htt) j k) hpop.le
      _ ≤ 2 * b := by linarith
  have hrem := DecideB_gradient_remainder_bound (DecideB_sampleScore X Y g n ω) (-I)
    (Metric.ball θ ρ) (convex_ball θ ρ) θ (that n ω) (Metric.mem_ball_self hρ) hsmall
    (fun t htt j => ((DecideB_sampleScore_contDiffOn X Y g n ω _ Metric.isOpen_ball hdiff' j).differentiableOn
      (by norm_num)).differentiableAt (Metric.isOpen_ball.mem_nhds htt))
    (2 * b) (by positivity) hJ
  have hrem' : ‖DecideB_sampleScore X Y g n ω θ - I *ᵥ (that n ω - θ)‖ ≤
      ((τ : ℝ) * (2 * b)) * ‖that n ω - θ‖ := by
    rw [hs, zero_sub, Matrix.neg_mulVec, sub_neg_eq_add] at hrem
    convert hrem using 1
    rw [← norm_neg]
    congr 1
    abel
  have hcorr := DecideB_scoreMatrix_bound I (DecideB_sampleScore X Y g n ω θ)
    (that n ω - θ) ((τ : ℝ) * (2 * b)) (by positivity) hrem'
  rw [dist_eq_norm]
  have hnorm : ‖DecideB_scoreMatrix I (DecideB_sampleScore X Y g n ω θ) (that n ω - θ) - I‖ ≤
      (τ : ℝ) * (2 * b) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro k
    exact hcorr j k
  apply lt_of_le_of_lt hnorm
  dsimp [b]
  have htau : (0 : ℝ) ≤ τ := Nat.cast_nonneg _
  field_simp
  nlinarith

theorem DecideB_matrix_inv_measurable {d : ℕ} :
    Measurable (fun A : Matrix (Fin d) (Fin d) ℝ => A⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable

/-- Slutsky applied to an asymptotically exact invertible score equation.
The local equation is used only where the error is small. -/
theorem DecideB_linearized_normal_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (v q : ℕ → Ω → Fin d → ℝ)
    (hv : ∀ n, AEMeasurable (v n) μ) (hconsistent : CP μ v 0)
    (I : Matrix (Fin d) (Fin d) ℝ) (hI : I.PosDef)
    (B : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hBm : ∀ n, AEMeasurable (B n) μ) (hB : CP μ B I)
    (δ : ℝ) (hδ : 0 < δ)
    (heq : ∀ n, ∀ᵐ ω ∂μ, ‖v n ω‖ < δ → B n ω *ᵥ v n ω = q n ω)
    (hW : TendstoInDistribution
      (fun (n : ℕ) ω => I⁻¹ *ᵥ (Real.sqrt n • q n ω)) atTop id
      (fun _ => μ) (normalVectorLaw I⁻¹)) :
    WeakLimit μ (fun n ω => Real.sqrt n • v n ω) (normalVectorLaw I⁻¹) := by
  have hu : IsUnit I.det := I.isUnit_iff_isUnit_det.mp hI.isUnit
  have hcinv : ContinuousAt (fun A : Matrix (Fin d) (Fin d) ℝ => A⁻¹) I :=
    continuousAt_matrix_inv I (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hu.ne_zero)
  have hBinv : CP μ (fun n ω => (B n ω)⁻¹) I⁻¹ :=
    probability_convergence_continuous_at μ B I _ hB hcinv
  have hBinvm (n : ℕ) : AEMeasurable (fun ω => (B n ω)⁻¹) μ :=
    DecideB_matrix_inv_measurable.comp_aemeasurable (hBm n)
  let P : ℕ → Ω → Fin d → ℝ := fun n ω => (B n ω)⁻¹ *ᵥ (Real.sqrt n • q n ω)
  have hproxy : TendstoInDistribution P atTop id (fun _ => μ) (normalVectorLaw I⁻¹) := by
    have hBinv' : TendstoInMeasure μ
        (fun n ω => fun j k => (B n ω)⁻¹ j k) atTop (fun _ => fun j k => I⁻¹ j k) :=
      (DecideB_cp_iff_tendstoInMeasure μ _ _).mp hBinv
    have hBinvm' (n : ℕ) : AEMeasurable (fun ω => fun j k => (B n ω)⁻¹ j k) μ := hBinvm n
    have hsl := hW.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun z : (Fin d → ℝ) × (Fin d → Fin d → ℝ) => Matrix.of z.2 *ᵥ (I *ᵥ z.1))
      (by fun_prop) hBinv' hBinvm'
    apply hsl.congr _ _
    · intro n
      apply Filter.Eventually.of_forall
      intro ω
      dsimp [P]
      rw [Matrix.mulVec_mulVec (Real.sqrt n • q n ω) I I⁻¹,
        I.mul_nonsing_inv hu, Matrix.one_mulVec]
      rfl
    · apply Filter.Eventually.of_forall
      intro w
      change I⁻¹ *ᵥ (I *ᵥ w) = w
      rw [Matrix.mulVec_mulVec, I.nonsing_inv_mul hu, Matrix.one_mulVec]
  have hdet : CP μ (fun n ω => (B n ω).det) I.det :=
    probability_convergence_continuous_at μ B I Matrix.det hB continuous_id.matrix_det.continuousAt
  have hdiff : CP μ (fun n ω => Real.sqrt n • v n ω - P n ω) 0 := by
    apply DecideB_cp_of_two_controls μ _ 0 (fun n ω => (B n ω).det) I.det v 0 hdet hconsistent
    intro ε hε
    refine ⟨I.det / 2, by linarith [hI.det_pos], δ, hδ, Eventually.of_forall (fun n => ?_)⟩
    filter_upwards [heq n] with ω hω
    intro hdetω hvω
    have hdetnz : (B n ω).det ≠ 0 := by
      rw [Real.dist_eq] at hdetω
      have hh := (abs_lt.mp hdetω).1
      linarith [hI.det_pos]
    have hq := hω (by simpa only [dist_zero_right] using hvω)
    have hlin : (B n ω)⁻¹ *ᵥ q n ω = v n ω := by
      rw [← hq, Matrix.mulVec_mulVec, (B n ω).nonsing_inv_mul (isUnit_iff_ne_zero.mpr hdetnz),
        Matrix.one_mulVec]
    have hp : P n ω = Real.sqrt n • v n ω := by
      dsimp [P]
      rw [Matrix.mulVec_smul, hlin]
    simp only [hp, sub_self, dist_self]
    exact hε
  apply DecideB_weakLimit_of_tendstoInDistribution μ _ _
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ id hproxy
    ((DecideB_cp_iff_tendstoInMeasure μ _ _).mp hdiff)
  intro n
  apply aemeasurable_pi_lambda
  intro j
  change AEMeasurable (fun ω => Real.sqrt n * v n ω j) μ
  exact ((measurable_pi_apply j).comp_aemeasurable (hv n)).const_mul _

theorem DecideB_scoreMatrix_measurable {d : ℕ} (I : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => DecideB_scoreMatrix I z.1 z.2) := by
  apply Measurable.of_eval_matrix
  intro j k
  dsimp [DecideB_scoreMatrix, Matrix.mulVec, dotProduct]
  fun_prop

/-- Normality core, with the local score equation supplied by either form of maximization. -/
theorem DecideB_local_score_normal_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (θ : Fin τ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hg : ∀ t ∈ Metric.ball θ δ,
      Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
    (S : Set ((Fin K → ℝ) × ℝ)) (hS : MeasurableSet S)
    (hfull : (μ.map (fun ω => (X 0 ω, Y 0 ω))) S = 1)
    (hdiff : ∀ xy ∈ S, ContDiffOn ℝ 2
      (fun t => Real.log (g xy.2 xy.1 t)) (Metric.ball θ δ))
    (hs2 : ∀ j, MemLp (fun ω => modelScore g (Y 0 ω) (X 0 ω) θ j) 2 μ)
    (hs0 : ∀ j, mean μ (fun ω => modelScore g (Y 0 ω) (X 0 ω) θ j) = 0)
    (hinfo : (informationMatrix μ (X 0) (Y 0) g θ).PosDef)
    (hHinfo : populationHessian μ (X 0) (Y 0) g θ = -informationMatrix μ (X 0) (Y 0) g θ)
    (hHcont : ContinuousAt (populationHessian μ (X 0) (Y 0) g) θ)
    (ΔH : ℕ → Ω → ℝ)
    (hHbound : ∀ n ω t, t ∈ Metric.ball θ δ → ∀ j k,
      |sampleHessian X Y g n ω t j k - populationHessian μ (X 0) (Y 0) g t j k| ≤ ΔH n ω)
    (hHlim : CP μ ΔH 0) (that : ℕ → Ω → Fin τ → ℝ)
    (hmeas : ∀ n, Measurable (that n)) (hconsistent : CP μ that θ)
    (hzero : ∀ n, ∀ᵐ ω ∂μ, that n ω ∈ Metric.ball θ δ →
      DecideB_sampleScore X Y g n ω (that n ω) = 0) :
    WeakLimit μ (fun n ω => Real.sqrt n • (that n ω - θ))
      (normalVectorLaw (informationMatrix μ (X 0) (Y 0) g θ)⁻¹) := by
  let I := informationMatrix μ (X 0) (Y 0) g θ
  let s : ℕ → Ω → Fin τ → ℝ :=
    fun i ω => DecideB_scoreVersion g S θ (X i ω, Y i ω)
  obtain ⟨hsiid, heq⟩ := DecideB_scoreVersion_iid μ X Y hiid g S hS hfull θ
    (DecideB_scoreVersion_measurable g S hS _ Metric.isOpen_ball θ (Metric.mem_ball_self hδ) hg hdiff)
  have hs (j : Fin τ) : (fun ω => s 0 ω j) =ᵐ[μ]
      fun ω => modelScore g (Y 0 ω) (X 0 ω) θ j := by
    filter_upwards [heq] with ω hω
    exact congrFun (hω 0) j
  have h2 (j : Fin τ) : MemLp (fun ω => s 0 ω j) 2 μ := (memLp_congr_ae (hs j)).mpr (hs2 j)
  have h0 (j : Fin τ) : mean μ (fun ω => s 0 ω j) = 0 :=
    (integral_congr_ae (hs j)).trans (hs0 j)
  have hcov (j k : Fin τ) : I j k = mean μ (fun ω => s 0 ω j * s 0 ω k) := by
    apply integral_congr_ae
    filter_upwards [hs j, hs k] with ω hj hk
    rw [hj, hk]
  let q : ℕ → Ω → Fin τ → ℝ := fun n ω => DecideB_sampleScore X Y g n ω θ
  let v : ℕ → Ω → Fin τ → ℝ := fun n ω => that n ω - θ
  let B : ℕ → Ω → Matrix (Fin τ) (Fin τ) ℝ := fun n ω => DecideB_scoreMatrix I (q n ω) (v n ω)
  have hqm (n : ℕ) : AEMeasurable (q n) μ := by
    have hm : Measurable (fun ω => fun j => (∑ i ∈ Finset.range n, s i ω j) / (n : ℝ)) := by
      apply measurable_pi_lambda
      intro j
      exact (Finset.measurable_sum _ (fun i _ =>
        (measurable_pi_apply j).comp (hsiid.1 i))).div_const _
    apply hm.aemeasurable.congr
    filter_upwards [heq] with ω hω
    ext j
    change (∑ i ∈ Finset.range n, s i ω j) / (n : ℝ) = _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (hω i) j
  have hvm (n : ℕ) : AEMeasurable (v n) μ := (hmeas n).aemeasurable.sub_const θ
  have hBm (n : ℕ) : AEMeasurable (B n) μ :=
    (DecideB_scoreMatrix_measurable I).comp_aemeasurable ((hqm n).prodMk (hvm n))
  have hv : CP μ v 0 := by
    simpa only [sub_self] using probability_convergence_continuous_at μ that θ
      (fun t => t - θ) hconsistent (continuous_id.sub continuous_const).continuousAt
  have hdiffae : ∀ᵐ ω ∂μ, ∀ i, ContDiffOn ℝ 2
      (fun t => Real.log (g (Y i ω) (X i ω) t)) (Metric.ball θ δ) := by
    filter_upwards [DecideB_ae_all_mem μ _ hiid S hS hfull] with ω hω
    exact fun i => hdiff _ (hω i)
  have hB : CP μ B I := DecideB_scoreMatrix_cp μ X Y g θ δ hδ hdiffae I
    hHinfo hHcont ΔH hHbound hHlim that hconsistent hzero
  have hlinear (n : ℕ) : ∀ᵐ ω ∂μ, ‖v n ω‖ < δ → B n ω *ᵥ v n ω = q n ω := by
    filter_upwards [hzero n] with ω hω
    intro hvδ
    by_cases hv0 : v n ω = 0
    · have ht : that n ω = θ := sub_eq_zero.mp hv0
      have hq0 : q n ω = 0 := by
        have hz := hω (by simpa only [ht] using Metric.mem_ball_self hδ)
        simpa only [q, ht] using hz
      simp only [hv0, Matrix.mulVec_zero, hq0]
    · exact DecideB_scoreMatrix_mulVec I (q n ω) (v n ω) hv0
  apply DecideB_linearized_normal_limit μ v q hvm hv I hinfo B hBm hB δ hδ hlinear
  have hclt := DecideB_inverse_information_clt μ s hsiid h2 h0 I hinfo hcov
  apply hclt.congr _ (Filter.EventuallyEq.refl _ _)
  intro n
  filter_upwards [heq] with ω hω
  congr 1
  ext j
  simp only [Pi.smul_apply, smul_eq_mul, q, DecideB_sampleScore]
  have he : (∑ i ∈ Finset.range n, s i ω j) =
      ∑ i ∈ Finset.range n, modelScore g (Y i ω) (X i ω) θ j := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (hω i) j
  rw [he]
  calc
    _ = (Real.sqrt n / n) * (∑ i ∈ Finset.range n, modelScore g (Y i ω) (X i ω) θ j) := by
      rw [DecideB_sqrt_div_nat]
    _ = _ := by ring


theorem identified_mixture_ml_normal_efficiency_supporting_common_regular_set {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {M K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (p : (Fin τ → ℝ) → Fin M → ℝ)
   (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (Θ : Set (Fin τ → ℝ)) (θ : Fin τ → ℝ) (δ : ℝ) (hδ : 0 < δ)
   (hinterior : Metric.ball θ δ⊆Θ)
   (hp : ∀ t∈Θ,(∀ m,0 ≤ p t m) ∧ (∑ m,p t m)=1)
   (hg : ∀ t∈Θ,∀ m,Measurable (fun xy : (Fin K → ℝ) × ℝ => g m xy.2 xy.1 t))
   (hnonneg : ∀ t∈Θ,∀ m y x,0 ≤ g m y x t)
   (hnorm : ∀ t∈Θ,∀ m x,(∫⁻ y,ENNReal.ofReal (g m y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=conditionalModelLaw νX κ (mixtureFamily p g) θ)
   (S : Set ((Fin K → ℝ) × ℝ)) (hS : MeasurableSet S)
   (hSfull : (μ.map (fun ω => (X 0 ω,Y 0 ω))) S = 1)
   (hpositive : ∀ xy ∈ S,∀ t∈Metric.ball θ δ,
     0 < mixtureFamily p g xy.2 xy.1 t)
   (hdiff : ∀ xy ∈ S,ContDiffOn ℝ 2
     (fun t => Real.log (mixtureFamily p g xy.2 xy.1 t)) (Metric.ball θ δ))
   (hs2 : ∀ j,MemLp (fun ω => modelScore (mixtureFamily p g) (Y 0 ω) (X 0 ω) θ j) 2 μ)
   (hszero : ∀ j,mean μ (fun ω => modelScore (mixtureFamily p g) (Y 0 ω) (X 0 ω) θ j)=0)
   (hinfo : (informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ).PosDef)
   (hHinfo : populationHessian μ (X 0) (Y 0) (mixtureFamily p g) θ=
     -informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ)
   (hHcont : ContinuousAt (populationHessian μ (X 0) (Y 0) (mixtureFamily p g)) θ)
   (hHi : ∀ t∈Metric.ball θ δ,∀ j k,
     Integrable (fun ω => modelHessian (mixtureFamily p g) (Y 0 ω) (X 0 ω) t j k) μ)
   (ΔH : ℕ → Ω → ℝ) (hHbound : ∀ n ω t,t∈Metric.ball θ δ → ∀ j k,
     |sampleHessian X Y (mixtureFamily p g) n ω t j k-
       populationHessian μ (X 0) (Y 0) (mixtureFamily p g) t j k| ≤ ΔH n ω)
   (hHlim : CP μ ΔH 0)
   (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n,Measurable (that n))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → sampleLogLikelihood X Y (mixtureFamily p g) n ω t ≤ 
     sampleLogLikelihood X Y (mixtureFamily p g) n ω (that n ω))
   (hconsistent : CP μ that θ) :
   WeakLimit μ (fun n ω => Real.sqrt n • (that n ω-θ))
     (normalVectorLaw (informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ)⁻¹) := by

  apply DecideB_local_score_normal_limit μ X Y hiid (mixtureFamily p g) θ δ hδ
    ?_ S hS hSfull hdiff hs2 hszero hinfo hHinfo hHcont ΔH hHbound hHlim
    that hmeas hconsistent ?_
  · intro t ht
    simpa only [mixtureFamily] using Finset.measurable_sum Finset.univ
      (fun m _ => (hg t (hinterior ht) m).const_mul (p t m))
  · intro n
    filter_upwards [DecideB_ae_all_mem μ (fun i ω => (X i ω, Y i ω)) hiid S hS hSfull] with ω hω
    intro ht
    exact DecideB_log_maximizer_score_zero X Y (mixtureFamily p g) n ω Θ (Metric.ball θ δ)
      Metric.isOpen_ball hinterior (fun i => hdiff _ (hω i)) (that n ω) ht
      (fun t htt => hmax n ω t htt)


theorem product_identified_mixture_ml_normal_limit_common_regular_set {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {M K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (p : (Fin τ → ℝ) → Fin M → ℝ)
   (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (Θ : Set (Fin τ → ℝ)) (θ : Fin τ → ℝ) (δ : ℝ) (hδ : 0 < δ)
   (hinterior : Metric.ball θ δ⊆Θ)
   (hp : ∀ t∈Θ,(∀ m,0 ≤ p t m) ∧ (∑ m,p t m)=1)
   (hg : ∀ t∈Θ,∀ m,Measurable (fun xy : (Fin K → ℝ) × ℝ => g m xy.2 xy.1 t))
   (hnonneg : ∀ t∈Θ,∀ m y x,0 ≤ g m y x t)
   (hnorm : ∀ t∈Θ,∀ m x,(∫⁻ y,ENNReal.ofReal (g m y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=conditionalModelLaw νX κ (mixtureFamily p g) θ)
   (S : Set ((Fin K → ℝ) × ℝ)) (hS : MeasurableSet S)
   (hSfull : (μ.map (fun ω => (X 0 ω,Y 0 ω))) S = 1)
   (hpositive : ∀ xy ∈ S,∀ t∈Metric.ball θ δ,
     0 < mixtureFamily p g xy.2 xy.1 t)
   (hdiff : ∀ xy ∈ S,ContDiffOn ℝ 2
     (fun t => Real.log (mixtureFamily p g xy.2 xy.1 t)) (Metric.ball θ δ))
   (hs2 : ∀ j,MemLp (fun ω => modelScore (mixtureFamily p g) (Y 0 ω) (X 0 ω) θ j) 2 μ)
   (hszero : ∀ j,mean μ (fun ω => modelScore (mixtureFamily p g) (Y 0 ω) (X 0 ω) θ j)=0)
   (hinfo : (informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ).PosDef)
   (hHinfo : populationHessian μ (X 0) (Y 0) (mixtureFamily p g) θ=
     -informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ)
   (hHcont : ContinuousAt (populationHessian μ (X 0) (Y 0) (mixtureFamily p g)) θ)
   (hHi : ∀ t∈Metric.ball θ δ,∀ j k,
     Integrable (fun ω => modelHessian (mixtureFamily p g) (Y 0 ω) (X 0 ω) t j k) μ)
   (ΔH : ℕ → Ω → ℝ) (hHbound : ∀ n ω t,t∈Metric.ball θ δ → ∀ j k,
     |sampleHessian X Y (mixtureFamily p g) n ω t j k-
       populationHessian μ (X 0) (Y 0) (mixtureFamily p g) t j k| ≤ ΔH n ω)
   (hHlim : CP μ ΔH 0)
   (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n,Measurable (that n))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → sampleLikelihood X Y (mixtureFamily p g) n ω t ≤ 
     sampleLikelihood X Y (mixtureFamily p g) n ω (that n ω))
   (hconsistent : CP μ that θ) :
   WeakLimit μ (fun n ω => Real.sqrt n • (that n ω-θ))
     (normalVectorLaw (informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ)⁻¹) := by

  apply DecideB_local_score_normal_limit μ X Y hiid (mixtureFamily p g) θ δ hδ
    ?_ S hS hSfull hdiff hs2 hszero hinfo hHinfo hHcont ΔH hHbound hHlim
    that hmeas hconsistent ?_
  · intro t ht
    simpa only [mixtureFamily] using Finset.measurable_sum Finset.univ
      (fun m _ => (hg t (hinterior ht) m).const_mul (p t m))
  · intro n
    filter_upwards [DecideB_ae_all_mem μ (fun i ω => (X i ω, Y i ω)) hiid S hS hSfull] with ω hω
    intro ht
    by_cases hn : n = 0
    · subst n
      ext j
      simp [DecideB_sampleScore]
    apply DecideB_log_maximizer_score_zero X Y (mixtureFamily p g) n ω
      (Metric.ball θ δ) (Metric.ball θ δ) Metric.isOpen_ball (Set.Subset.refl _)
      (fun i => hdiff _ (hω i)) (that n ω) ht
    intro t htt
    apply (DecideB_product_le_iff_log_le X Y (mixtureFamily p g) n
      (Nat.pos_of_ne_zero hn) ω t (that n ω)
      (fun i => hpositive _ (hω i) t htt)
      (fun i => hpositive _ (hω i) (that n ω) ht)).mp
    exact hmax n ω t (hinterior htt)

/-- Compact uniform-log consistency with a common measurable positivity set.
This discharges the consistency part needed before the product normal limit. -/
theorem DecideB_product_mle_consistency {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (Θ : Set (Fin τ → ℝ)) (hc : IsCompact Θ) (θ : Fin τ → ℝ) (hθ : θ ∈ Θ)
    (S : Set ((Fin K → ℝ) × ℝ)) (hS : MeasurableSet S)
    (hfull : (μ.map (fun ω => (X 0 ω, Y 0 ω))) S = 1)
    (hpositive : ∀ xy ∈ S, 0 < g xy.2 xy.1 θ)
    (hM : ContinuousOn (expectedLogLikelihood μ (X 0) (Y 0) g) Θ)
    (hunique : ∀ t ∈ Θ,
      expectedLogLikelihood μ (X 0) (Y 0) g t ≤ expectedLogLikelihood μ (X 0) (Y 0) g θ ∧
      (expectedLogLikelihood μ (X 0) (Y 0) g t = expectedLogLikelihood μ (X 0) (Y 0) g θ → t = θ))
    (that : ℕ → Ω → Fin τ → ℝ) (hthat : ∀ n ω, that n ω ∈ Θ)
    (hmax : ∀ n ω t, t ∈ Θ → sampleLikelihood X Y g n ω t ≤ sampleLikelihood X Y g n ω (that n ω))
    (Δ : ℕ → Ω → ℝ) (hΔ : CP μ Δ 0)
    (hbound : ∀ n ω t, t ∈ Θ →
      |sampleLogLikelihood X Y g n ω t - expectedLogLikelihood μ (X 0) (Y 0) g t| ≤ Δ n ω) :
    CP μ that θ := by
  have hp : ∀ᵐ ω ∂μ, ∀ i, 0 < g (Y i ω) (X i ω) θ := by
    filter_upwards [DecideB_ae_all_mem μ _ hiid S hS hfull] with ω hω
    exact fun i => hpositive _ (hω i)
  exact product_mle_consistency_core μ X Y g Θ hc θ hθ hM hunique that hthat hp
    (fun n ω => hmax n ω θ hθ) Δ hbound hΔ

end
end AronowAudit.P001.Wave1
