import AronowAudit.Shared.MapTailB.QuantileL2
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Adapters from the exact P022 hypotheses to fixed-level quantile convergence. -/

namespace AronowAudit.P022.Wave1

open MeasureTheory ProbabilityTheory Causalean.Stat Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

/-- Each row has a nonempty population. -/
instance TailB_instNeZero_population (S : ExperimentSequence) (q : ℕ) :
    NeZero (S.design q).N := ⟨by have := (S.design q).population_min; omega⟩

/-- The actual coordinate marginal as a probability measure. -/
def TailB_marginalLaw (H : JointLaw) (t : Bool) : ProbabilityMeasure ℝ :=
  H.map (fun p => if t then p.1 else p.2)

/-- The marginal probability CDF equals `lawCDF`. -/
theorem TailB_marginal_cdf (H : JointLaw) (t : Bool) (x : ℝ) :
    cdf (TailB_marginalLaw H t : Measure ℝ) x = lawCDF H t x := by
  cases t
  · exact (TailB_lawCDF_eq_cdf_snd H x).symm
  · exact (TailB_lawCDF_eq_cdf_fst H x).symm

/-- Condition 4 supplies uniformly small finite square tails. -/
theorem TailB_square_tails (S : ExperimentSequence) (hUI : UniformSquareIntegrability S)
    (t : Bool) : ∀ ε > 0, ∃ β : ℝ, 1 < β ∧ ∀ q,
      finiteMean (fun i => if β ≤ rowOutcomes S t q i ^ 2
        then rowOutcomes S t q i ^ 2 else 0) ≤ ε := by
  intro ε hε
  obtain ⟨β, hβ, hb⟩ := ((eventually_gt_atTop (1 : ℝ)).and
    ((hUI t).1.eventually_lt_const hε)).exists
  refine ⟨β, hβ, fun q => ?_⟩
  apply le_trans _ hb.le
  exact le_csSup ((hUI t).2 β) (mem_range_self q)

/-- Weak joint empirical convergence implies weak coordinate convergence. -/
theorem TailB_marginal_weak (S : ExperimentSequence) (H : JointLaw)
    (hw : weakPopulationConvergence S H) (t : Bool) :
    Tendsto (fun q => TailB_empiricalLaw (rowOutcomes S t q)) atTop
      (𝓝 (TailB_marginalLaw H t)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let c : C(ℝ × ℝ, ℝ) := ⟨fun p => if t then p.1 else p.2, by cases t <;> simp <;> fun_prop⟩
  have hh := hw (f.compContinuous c)
  have hm : Measurable (fun p : ℝ × ℝ => if t then p.1 else p.2) := by
    cases t <;> simp <;> fun_prop
  have hi : (∫ x, f x ∂(TailB_marginalLaw H t : Measure ℝ)) =
      ∫ p, f (if t then p.1 else p.2) ∂(H : Measure (ℝ × ℝ)) := by
    exact integral_map hm.aemeasurable f.continuous.measurable.aestronglyMeasurable
  simp only [TailB_integral_empiricalLaw _ _ f.continuous.measurable, hi]
  convert hh using 1
  · funext q
    congr 1
    funext i
    cases t <;> rfl
  · rfl

/-- CDF continuity at a point makes its singleton null. -/
theorem TailB_cdf_singleton_null (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) (hc : ContinuousAt (cdf μ) x) : μ {x} = 0 := by
  rw [← measure_cdf μ, StieltjesFunction.measure_singleton,
    hc.continuousWithinAt.leftLim_eq, sub_self, ENNReal.ofReal_zero]

/-- Conditions 2--3 give pointwise CDF convergence; atom-left values are absent. -/
theorem TailB_population_cdf_tendsto (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (t : Bool) (x : ℝ) :
    Tendsto (fun q => empiricalCDF (rowOutcomes S t q) x) atTop (𝓝 (lawCDF H t x)) := by
  by_cases hc : ContinuousAt (lawCDF H t) x
  · have hw := TailB_marginal_weak S H h.2.2.2.2.2.2.1 t
    have hnull : (TailB_marginalLaw H t : Measure ℝ) (frontier (Iic x)) = 0 := by
      rw [frontier_Iic]
      exact TailB_cdf_singleton_null _ x (by
        have he : (cdf (TailB_marginalLaw H t : Measure ℝ) : ℝ → ℝ) = lawCDF H t :=
          funext (TailB_marginal_cdf H t)
        rwa [he])
    have hh := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hw hnull
    have ht := (ENNReal.tendsto_toReal (measure_ne_top
      (TailB_marginalLaw H t : Measure ℝ) (Iic x))).comp hh
    simpa only [Function.comp_def, ← measureReal_def, ← cdf_eq_real, TailB_cdf_empiricalLaw,
      TailB_marginal_cdf] using ht
  · exact h.2.2.2.2.2.2.2 t x hc

/-- The exact hypotheses imply L2 convergence of both population quantiles. -/
theorem TailB_population_quantile_L2 (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hUI : UniformSquareIntegrability S) (t : Bool) :
    MemLp (quantile (TailB_marginalLaw H t : Measure ℝ)) 2 unifOI ∧
      Tendsto (fun q => eLpNorm
        (quantile (TailB_empiricalLaw (rowOutcomes S t q) : Measure ℝ) -
         quantile (TailB_marginalLaw H t : Measure ℝ)) 2 unifOI) atTop (𝓝 0) := by
  apply TailB_finite_quantile_L2 (fun q => (S.design q).N) (rowOutcomes S t)
    (TailB_marginalLaw H t : Measure ℝ)
  · intro x
    simpa only [TailB_marginal_cdf] using TailB_population_cdf_tendsto S H θ ρ h t x
  · exact TailB_square_tails S hUI t


/-- L2 on the uniform level space is exactly L2 under the quantile's law. -/
theorem TailB_law_memLp_of_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hq : MemLp (quantile μ) 2 unifOI) : MemLp (fun x : ℝ => x) 2 μ := by
  have hh := (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (aemeasurable_quantile_unifOI μ)).mpr hq
  rwa [quantile_map_uniform μ] at hh

/-- Condition 4 and weak convergence supply both coordinate L2 moments. -/
theorem TailB_population_coordinate_memLp (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hUI : UniformSquareIntegrability S) (t : Bool) :
    MemLp (fun p : ℝ × ℝ => if t then p.1 else p.2) 2 (H : Measure (ℝ × ℝ)) := by
  have hm := TailB_law_memLp_of_quantile (TailB_marginalLaw H t : Measure ℝ)
    (TailB_population_quantile_L2 S H θ ρ h hUI t).1
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (show AEMeasurable (fun p : ℝ × ℝ => if t then p.1 else p.2)
      (H : Measure (ℝ × ℝ)) by cases t <;> simp <;> fun_prop)).mp hm

/-- All laws with the specified marginals inherit their coordinate L2 moments. -/
theorem TailB_compatible_coordinate_memLp (H J : JointLaw)
    (hc : J ∈ compatibleLaws H) (t : Bool)
    (hm : MemLp (fun p : ℝ × ℝ => if t then p.1 else p.2) 2
      (H : Measure (ℝ × ℝ))) :
    MemLp (fun p : ℝ × ℝ => if t then p.1 else p.2) 2 (J : Measure (ℝ × ℝ)) := by
  obtain ⟨h1, h0⟩ := (TailB_compatibleLaws_iff_marginals H J).mp hc
  cases t
  · have hmap := (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      measurable_snd.aemeasurable).mpr hm
    rw [← h0] at hmap
    exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      measurable_snd.aemeasurable).mp hmap
  · have hmap := (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      measurable_fst.aemeasurable).mpr hm
    rw [← h1] at hmap
    exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      measurable_fst.aemeasurable).mp hmap

/-- The two moment conclusions of Proposition 1. -/
theorem TailB_proposition1_moments (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hUI : UniformSquareIntegrability S) :
    (∀ J ∈ compatibleLaws H, ∀ t : Bool, ∀ j : ℕ, j ≤ 2 →
      Integrable (fun p : ℝ × ℝ => (if t then p.1 else p.2) ^ j)
        (J : Measure (ℝ × ℝ))) ∧
    (∀ J ∈ compatibleLaws H, Integrable (fun p : ℝ × ℝ => p.1 * p.2)
      (J : Measure (ℝ × ℝ))) := by
  have hm (J : JointLaw) (hc : J ∈ compatibleLaws H) (t : Bool) :=
    TailB_compatible_coordinate_memLp H J hc t
      (TailB_population_coordinate_memLp S H θ ρ h hUI t)
  constructor
  · intro J hc t j hj
    interval_cases j
    · simpa only [pow_zero] using (integrable_const (1 : ℝ))
    · simpa only [pow_one] using (hm J hc t).integrable (by norm_num)
    · exact (hm J hc t).integrable_sq
  · intro J hc
    exact (hm J hc true).integrable_mul (hm J hc false)


abbrev TailB_LevelL2 := Lp ℝ 2 unifOI

/-- The level reflection is measure preserving, including its endpoints. -/
theorem TailB_level_reflection_preserving :
    MeasurePreserving (fun u : ℝ => 1-u) unifOI unifOI :=
  ⟨measurable_const.sub measurable_id, map_one_sub_unifOI⟩

/-- Reflection on the fixed quantile Hilbert space. -/
def TailB_l2Reflect (f : TailB_LevelL2) : TailB_LevelL2 :=
  Lp.compMeasurePreserving (fun u : ℝ => 1-u) TailB_level_reflection_preserving f

@[fun_prop]
theorem TailB_l2Reflect_continuous : Continuous TailB_l2Reflect :=
  (Lp.isometry_compMeasurePreserving TailB_level_reflection_preserving).continuous

/-- Mean, variance and both endpoint covariances as continuous L2 functionals. -/
def TailB_l2Mean (f : TailB_LevelL2) : ℝ :=
  inner ℝ f ((memLp_const (1 : ℝ)).toLp (fun _ : ℝ => (1 : ℝ)))

def TailB_l2Variance (f : TailB_LevelL2) : ℝ :=
  inner ℝ f f - TailB_l2Mean f ^ 2

def TailB_l2Covariance (B : BoundSide) (p : TailB_LevelL2 × TailB_LevelL2) : ℝ :=
  inner ℝ p.1 (if B = .H then p.2 else TailB_l2Reflect p.2) -
    TailB_l2Mean p.1 * TailB_l2Mean p.2

@[fun_prop]
theorem TailB_l2Mean_continuous : Continuous TailB_l2Mean :=
  continuous_id.inner continuous_const

@[fun_prop]
theorem TailB_l2Variance_continuous : Continuous TailB_l2Variance :=
  (continuous_id.inner continuous_id).sub (TailB_l2Mean_continuous.pow 2)

@[fun_prop]
theorem TailB_l2Covariance_continuous (B : BoundSide) : Continuous (TailB_l2Covariance B) := by
  cases B <;> unfold TailB_l2Covariance <;> simp only [ite_true, reduceCtorEq, ite_false]
  · exact (continuous_fst.inner continuous_snd).sub
      ((TailB_l2Mean_continuous.comp continuous_fst).mul
        (TailB_l2Mean_continuous.comp continuous_snd))
  · exact (continuous_fst.inner (TailB_l2Reflect_continuous.comp continuous_snd)).sub
      ((TailB_l2Mean_continuous.comp continuous_fst).mul
        (TailB_l2Mean_continuous.comp continuous_snd))

/-- Reflection on representatives agrees with the L2 reflection. -/
theorem TailB_l2Reflect_toLp (f : ℝ → ℝ) (hf : MemLp f 2 unifOI) :
    TailB_l2Reflect (hf.toLp f) =
      (TailB_reflected_memLp hf).toLp (fun u => f (1-u)) := rfl

/-- The first-moment functional is the literal integral. -/
theorem TailB_l2Mean_toLp (f : ℝ → ℝ) (hf : MemLp f 2 unifOI) :
    TailB_l2Mean (hf.toLp f) = ∫ u, f u ∂unifOI := by
  simp only [TailB_l2Mean, TailB_toLp_inner, mul_one]

/-- Finite quantile mean and variance functionals equal `finiteMean` and `finiteVariance`. -/
theorem TailB_l2_empirical_moments {N : ℕ} [NeZero N] (y : Fin N → ℝ) :
    TailB_l2Mean ((TailB_empirical_quantile_memLp y).toLp
      (quantile (TailB_empiricalLaw y : Measure ℝ))) = finiteMean y ∧
    TailB_l2Variance ((TailB_empirical_quantile_memLp y).toLp
      (quantile (TailB_empiricalLaw y : Measure ℝ))) = finiteVariance y := by
  have hm : TailB_l2Mean ((TailB_empirical_quantile_memLp y).toLp
      (quantile (TailB_empiricalLaw y : Measure ℝ))) = finiteMean y := by
    rw [TailB_l2Mean_toLp]
    exact TailB_integral_empirical_quantile y (fun x => x) measurable_id
  refine ⟨hm, ?_⟩
  rw [TailB_l2Variance, TailB_toLp_inner, hm, finite_variance_second_moment (NeZero.pos N)]
  congr 1
  convert TailB_integral_empirical_quantile y (fun x => x*x)
    (measurable_id.mul measurable_id) using 1 <;> simp [pow_two]

/-- Both finite sharp covariances are the continuous L2 covariance functionals. -/
theorem TailB_l2_empirical_covariance {m k : ℕ} [NeZero m] [NeZero k]
    (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide) :
    TailB_l2Covariance B
      (((TailB_empirical_quantile_memLp a).toLp (quantile (TailB_empiricalLaw a : Measure ℝ))),
       ((TailB_empirical_quantile_memLp b).toLp (quantile (TailB_empiricalLaw b : Measure ℝ)))) =
      sharpCovariance a b B := by
  rw [TailB_l2Covariance, (TailB_l2_empirical_moments a).1,
    (TailB_l2_empirical_moments b).1, TailB_sharpCovariance_eq_quantile]
  cases B
  · simp only [if_true, TailB_toLp_inner]
    rfl
  · simp only [reduceCtorEq, if_false, TailB_l2Reflect_toLp, TailB_toLp_inner]
    rfl

/-- Limit variance in a product-minus-square representation. -/
theorem TailB_lawVariance_eq_second (H : JointLaw) (t : Bool)
    (hm : MemLp (fun p : ℝ × ℝ => if t then p.1 else p.2) 2 (H : Measure (ℝ × ℝ))) :
    lawVariance H t = (∫ p, (if t then p.1 else p.2) ^ 2 ∂(H : Measure (ℝ × ℝ))) -
      lawMean H t ^ 2 := by
  simpa only [covariance, lawVariance, lawMean, pow_two, Pi.mul_apply] using covariance_eq_sub hm hm

/-- The limiting quantile functionals give exactly the law's coordinate moments. -/
theorem TailB_l2_limit_moments (H : JointLaw) (t : Bool)
    (hq : MemLp (quantile (TailB_marginalLaw H t : Measure ℝ)) 2 unifOI)
    (hm : MemLp (fun p : ℝ × ℝ => if t then p.1 else p.2) 2 (H : Measure (ℝ × ℝ))) :
    TailB_l2Mean (hq.toLp (quantile (TailB_marginalLaw H t : Measure ℝ))) = lawMean H t ∧
    TailB_l2Variance (hq.toLp (quantile (TailB_marginalLaw H t : Measure ℝ))) = lawVariance H t := by
  have hmeas : Measurable (fun p : ℝ × ℝ => if t then p.1 else p.2) := by
    cases t <;> simp <;> fun_prop
  have hi : ∀ f : ℝ → ℝ, Measurable f →
      (∫ u, f (quantile (TailB_marginalLaw H t : Measure ℝ) u) ∂unifOI) =
        ∫ p, f (if t then p.1 else p.2) ∂(H : Measure (ℝ × ℝ)) := by
    intro f hf
    rw [TailB_integral_quantile _ f hf]
    exact integral_map hmeas.aemeasurable hf.aestronglyMeasurable
  have hmean : TailB_l2Mean (hq.toLp (quantile (TailB_marginalLaw H t : Measure ℝ))) =
      lawMean H t := by
    rw [TailB_l2Mean_toLp]
    exact hi (fun x => x) measurable_id
  refine ⟨hmean, ?_⟩
  rw [TailB_l2Variance, TailB_toLp_inner, hmean, TailB_lawVariance_eq_second H t hm]
  congr 1
  convert hi (fun x => x*x) (measurable_id.mul measurable_id) using 1
  congr 1
  funext p
  ring


/-- The two limiting L2 covariances are the exact compatible-law extrema. -/
theorem TailB_l2_limit_covariance (H : JointLaw)
    (h1 : MemLp (fun p : ℝ × ℝ => p.1) 2 (H : Measure (ℝ × ℝ)))
    (h0 : MemLp (fun p : ℝ × ℝ => p.2) 2 (H : Measure (ℝ × ℝ)))
    (hq1 : MemLp (quantile (TailB_marginalLaw H true : Measure ℝ)) 2 unifOI)
    (hq0 : MemLp (quantile (TailB_marginalLaw H false : Measure ℝ)) 2 unifOI)
    (B : BoundSide) :
    TailB_l2Covariance B
      (hq1.toLp (quantile (TailB_marginalLaw H true : Measure ℝ)),
       hq0.toLp (quantile (TailB_marginalLaw H false : Measure ℝ))) =
      if B = .H then sSup (lawCovariance '' compatibleLaws H)
      else sInf (lawCovariance '' compatibleLaws H) := by
  have he := TailB_frechet_covariance_L2 H h1 h0
  rw [TailB_l2Covariance, (TailB_l2_limit_moments H true hq1 h1).1,
    (TailB_l2_limit_moments H false hq0 h0).1]
  cases B
  · simp only [if_true, TailB_toLp_inner]
    exact he.1.symm
  · simp only [reduceCtorEq, if_false, TailB_l2Reflect_toLp, TailB_toLp_inner]
    exact he.2.1.symm

/-- Allocation ratios and the finite-population correction have their literal limits. -/
theorem TailB_allocation_limits (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) :
    Tendsto (fun q => ((S.design q).N : ℝ) / ((S.design q).N - 1)) atTop (𝓝 1) ∧
    Tendsto (fun q => (((S.design q).N : ℝ) - (S.design q).m) / (S.design q).m)
      atTop (𝓝 ((1 - θ * ρ) / (θ * ρ))) ∧
    Tendsto (fun q => (((S.design q).N : ℝ) - (S.design q).k) / (S.design q).k)
      atTop (𝓝 ((1 - θ * (1-ρ)) / (θ * (1-ρ)))) := by
  have hθ : 0 < θ := h.1
  have hρ : 0 < ρ := h.2.2.1
  have hρ1 : ρ < 1 := h.2.2.2.1
  have hm := h.2.2.2.2.1
  have hk := GP022B1b_control_ratio S θ ρ hm h.2.2.2.2.2.1
  have hN (q) : ((S.design q).N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne (S.design q).N)
  have hinv : Tendsto (fun q => 1 / ((S.design q).N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (GP022B1b_size_atTop S)
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  refine ⟨?_, ?_, ?_⟩
  · have hh := hOne.div (hOne.sub hinv)
      (by norm_num : (1 : ℝ) - 0 ≠ 0)
    convert hh using 1
    · funext q
      dsimp only [Pi.div_apply]
      field_simp [hN q]
    · norm_num
  · have hh := (hOne.sub hm).div hm (mul_pos hθ hρ).ne'
    convert hh using 1
    funext q
    dsimp only [Pi.div_apply]
    field_simp [hN q]
  · have hh := (hOne.sub hk).div hk
      (mul_pos hθ (sub_pos.mpr hρ1)).ne'
    convert hh using 1
    funext q
    dsimp only [Pi.div_apply]
    field_simp [hN q]

/-- Both population bounds have exactly the limits printed in Proposition 1. -/
theorem TailB_population_bound_limits (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hUI : UniformSquareIntegrability S) (B : BoundSide) :
    Tendsto (fun q => ((S.design q).N : ℝ) * populationBound (S.design q)
      (rowOutcomes S true q) (rowOutcomes S false q) B) atTop (𝓝 (limitingBound H θ ρ B)) := by
  have hq1 := TailB_population_quantile_L2 S H θ ρ h hUI true
  have hq0 := TailB_population_quantile_L2 S H θ ρ h hUI false
  have h1 := TailB_population_coordinate_memLp S H θ ρ h hUI true
  have h0 := TailB_population_coordinate_memLp S H θ ρ h hUI false
  have ht1 := TailB_toLp_tendsto _ _ (fun q => TailB_empirical_quantile_memLp
    (rowOutcomes S true q)) hq1.1 hq1.2
  have ht0 := TailB_toLp_tendsto _ _ (fun q => TailB_empirical_quantile_memLp
    (rowOutcomes S false q)) hq0.1 hq0.2
  have hv1 := (TailB_l2Variance_continuous.tendsto _).comp ht1
  have hv0 := (TailB_l2Variance_continuous.tendsto _).comp ht0
  have hcov := ((TailB_l2Covariance_continuous B).tendsto _).comp
    (ht1.prodMk_nhds ht0)
  simp only [Function.comp_def, (TailB_l2_empirical_moments _).2,
    (TailB_l2_limit_moments H true hq1.1 h1).2] at hv1
  simp only [Function.comp_def, (TailB_l2_empirical_moments _).2,
    (TailB_l2_limit_moments H false hq0.1 h0).2] at hv0
  simp only [Function.comp_def, TailB_l2_empirical_covariance,
    TailB_l2_limit_covariance H h1 h0 hq1.1 hq0.1 B] at hcov
  obtain ⟨hc, ha, hb⟩ := TailB_allocation_limits S H θ ρ h
  have hh := hc.mul (((ha.mul hv1).add (hb.mul hv0)).add (hcov.const_mul 2))
  convert hh using 1
  · funext q
    dsimp [populationBound, varianceExpression]
    ring
  · simp only [one_mul]
    rfl


instance TailB_instNeZero_treatment (S : ExperimentSequence) (q : ℕ) :
    NeZero (S.design q).m := ⟨by have := (S.design q).treatment_min; omega⟩

instance TailB_instNeZero_control (S : ExperimentSequence) (q : ℕ) :
    NeZero (S.design q).k := ⟨by have := (S.design q).control_min; omega⟩

/-- Both observed arms grow, even when the unsampled fraction vanishes. -/
theorem TailB_arm_sizes_atTop (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) :
    Tendsto (fun q => ((S.design q).m : ℝ)) atTop atTop ∧
    Tendsto (fun q => ((S.design q).k : ℝ)) atTop atTop := by
  let c := min (θ * ρ) (θ * (1-ρ)) / 2
  have hp : 0 < min (θ * ρ) (θ * (1-ρ)) := lt_min
    (mul_pos h.1 h.2.2.1) (mul_pos h.1 (sub_pos.mpr h.2.2.2.1))
  have hc : 0 < c := half_pos hp
  have he := GP022B1b_eventual_sizes S θ ρ c h.2.2.2.2.1 h.2.2.2.2.2.1
    (by dsimp [c]; linarith)
  have hct : Tendsto (fun q => c * ((S.design q).N : ℝ)) atTop atTop :=
    (GP022B1b_size_atTop S).const_mul_atTop hc
  exact ⟨tendsto_atTop_mono' _ (he.mono fun _ hx => hx.1) hct,
    tendsto_atTop_mono' _ (he.mono fun _ hx => hx.2) hct⟩

/-- Treatment and control sample quantiles converge in the same L2 space. -/
theorem TailB_sampled_quantiles (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hUI : UniformSquareIntegrability S) :
    let hq1 := (TailB_population_quantile_L2 S H θ ρ h hUI true).1
    let hq0 := (TailB_population_quantile_L2 S H θ ρ h hUI false).1
    TailB_DesignTendsto S.design (fun q π =>
      (TailB_empirical_quantile_memLp (observedTreatment (S.design q)
        (rowOutcomes S true q) π)).toLp
          (quantile (TailB_empiricalLaw (observedTreatment (S.design q)
            (rowOutcomes S true q) π) : Measure ℝ)))
        (hq1.toLp (quantile (TailB_marginalLaw H true : Measure ℝ))) ∧
    TailB_DesignTendsto S.design (fun q π =>
      (TailB_empirical_quantile_memLp (observedControl (S.design q)
        (rowOutcomes S false q) π)).toLp
          (quantile (TailB_empiricalLaw (observedControl (S.design q)
            (rowOutcomes S false q) π) : Measure ℝ)))
        (hq0.toLp (quantile (TailB_marginalLaw H false : Measure ℝ))) := by
  have hq1 := TailB_population_quantile_L2 S H θ ρ h hUI true
  have hq0 := TailB_population_quantile_L2 S H θ ρ h hUI false
  have hs := TailB_arm_sizes_atTop S H θ ρ h
  constructor
  · apply TailB_sample_quantile_toLp S.design (fun q => (S.design q).m)
      (fun q i => ⟨i.val, by have := (S.design q).sample_le; omega⟩)
      (fun q i j hij => Fin.ext (by simpa using congrArg Fin.val hij))
      (rowOutcomes S true) hs.1 (TailB_square_tails S hUI true) _ hq1.1 hq1.2
  · apply TailB_sample_quantile_toLp S.design (fun q => (S.design q).k)
      (fun q i => ⟨(S.design q).m + i.val, by have := (S.design q).sample_le; omega⟩)
      (fun q i j hij => Fin.ext (by have hh := congrArg Fin.val hij; dsimp at hh; omega))
      (rowOutcomes S false) hs.2 (TailB_square_tails S hUI false) _ hq0.1 hq0.2

/-- The exact finite-sample variance correction as a scalar multiplier. -/
theorem TailB_marginalVariance_factor {s : ℕ} (N : ℕ) (a : Fin s → ℝ) :
    marginalVarianceEstimate N a =
      (((N : ℝ) - 1) / N * ((s : ℝ) / ((s : ℝ) - 1))) * finiteVariance a := by
  have hsum : (∑ i, (a i - finiteMean a) ^ 2) = (s : ℝ) * finiteVariance a := by
    simpa only [Fintype.card_fin, finiteVariance, finiteMean] using
      (Fintype.card_mul_expect (fun i => (a i - finiteMean a) ^ 2)).symm
  unfold marginalVarianceEstimate sampleVariance
  rw [hsum]
  ring

/-- The treatment and control finite-sample correction factors both tend to one. -/
theorem TailB_marginal_factor_limits (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) :
    Tendsto (fun q => (((S.design q).N : ℝ) - 1) / (S.design q).N *
      (((S.design q).m : ℝ) / ((S.design q).m - 1))) atTop (𝓝 1) ∧
    Tendsto (fun q => (((S.design q).N : ℝ) - 1) / (S.design q).N *
      (((S.design q).k : ℝ) / ((S.design q).k - 1))) atTop (𝓝 1) := by
  have hinv : Tendsto (fun q => 1 / ((S.design q).N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (GP022B1b_size_atTop S)
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hN : Tendsto (fun q => (((S.design q).N : ℝ)-1) / (S.design q).N)
      atTop (𝓝 1) := by
    convert hOne.sub hinv using 1
    · funext q
      have hn : ((S.design q).N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (S.design q).N
      field_simp [hn]
    · norm_num
  have hs := TailB_arm_sizes_atTop S H θ ρ h
  have hr (s : ℕ → ℝ) (ht : Tendsto s atTop atTop) (hn : ∀ q, s q ≠ 0) :
      Tendsto (fun q => s q / (s q-1)) atTop (𝓝 1) := by
    have hi : Tendsto (fun q => 1 / s q) atTop (𝓝 0) := tendsto_const_nhds.div_atTop ht
    convert hOne.div (hOne.sub hi)
      (by norm_num : (1 : ℝ)-0 ≠ 0) using 1
    · funext q
      dsimp only [Pi.div_apply]
      field_simp [hn q]
    · norm_num
  constructor
  · simpa only [mul_one] using hN.mul (hr _ hs.1
      (fun q => by exact_mod_cast NeZero.ne (S.design q).m))
  · simpa only [mul_one] using hN.mul (hr _ hs.2
      (fun q => by exact_mod_cast NeZero.ne (S.design q).k))


/-- Both scaled random bound estimates converge under the original assignment laws. -/
theorem TailB_estimated_bound_limit (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hUI : UniformSquareIntegrability S) (B : BoundSide) :
    TailB_DesignTendsto S.design (fun q π => ((S.design q).N : ℝ) *
      estimatedVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) B π)
      (limitingBound H θ ρ B) := by
  have hq1 := TailB_population_quantile_L2 S H θ ρ h hUI true
  have hq0 := TailB_population_quantile_L2 S H θ ρ h hUI false
  have h1 := TailB_population_coordinate_memLp S H θ ρ h hUI true
  have h0 := TailB_population_coordinate_memLp S H θ ρ h hUI false
  obtain ⟨hs1, hs0⟩ := TailB_sampled_quantiles S H θ ρ h hUI
  have hv1 := hs1.comp TailB_l2Variance TailB_l2Variance_continuous.continuousAt
  have hv0 := hs0.comp TailB_l2Variance TailB_l2Variance_continuous.continuousAt
  have hcov := (hs1.prod hs0).comp (TailB_l2Covariance B)
    (TailB_l2Covariance_continuous B).continuousAt
  simp only [TailB_l2_empirical_moments, (TailB_l2_limit_moments H true hq1.1 h1).2] at hv1
  simp only [TailB_l2_empirical_moments, (TailB_l2_limit_moments H false hq0.1 h0).2] at hv0
  simp only [TailB_l2_empirical_covariance,
    TailB_l2_limit_covariance H h1 h0 hq1.1 hq0.1 B] at hcov
  obtain ⟨hc, ha, hb⟩ := TailB_allocation_limits S H θ ρ h
  obtain ⟨hfa, hfb⟩ := TailB_marginal_factor_limits S H θ ρ h
  have hp := (TailB_DesignTendsto.deterministic S.design hc).mul
    ((((TailB_DesignTendsto.deterministic S.design ha).mul
        ((TailB_DesignTendsto.deterministic S.design hfa).mul hv1)).add
      ((TailB_DesignTendsto.deterministic S.design hb).mul
        ((TailB_DesignTendsto.deterministic S.design hfb).mul hv0))).add
      ((TailB_DesignTendsto.deterministic S.design
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2))).mul hcov))
  convert hp using 1
  · funext q π
    dsimp [estimatedVariance, estimateBound, varianceExpression]
    rw [TailB_marginalVariance_factor, TailB_marginalVariance_factor]
    ring
  · simp only [one_mul]
    rfl

/-- The maximum of both endpoint estimation errors is o_P(1/N). -/
theorem TailB_bound_consistency (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hUI : UniformSquareIntegrability S) : boundConsistency S := by
  have he (B : BoundSide) : TailB_DesignTendsto S.design (fun q π =>
      ((S.design q).N : ℝ) * estimatedVariance (S.design q)
        (rowOutcomes S true q) (rowOutcomes S false q) B π -
      ((S.design q).N : ℝ) * populationBound (S.design q)
        (rowOutcomes S true q) (rowOutcomes S false q) B) 0 := by
    simpa only [sub_self] using (TailB_estimated_bound_limit S H θ ρ h hUI B).sub
      (TailB_DesignTendsto.deterministic S.design (TailB_population_bound_limits S H θ ρ h hUI B))
  intro ε hε
  have hp := (he .H |>.prod (he .L)) ε hε
  convert hp using 1
  funext q
  congr 1
  funext π
  apply propext
  simp only [Prod.dist_eq, Real.dist_eq, sub_zero, ← mul_sub, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ (S.design q).N from Nat.cast_nonneg _)]

/-- P022-T15: Proposition 1 under its stated hypotheses. -/
theorem TailB_proposition1 : (∀ (S : ExperimentSequence)
      (H : JointLaw)
      (θ ρ : ℝ)
      (h : Conditions123 S H θ ρ)
      (hUI : UniformSquareIntegrability S),
      (∀ h ∈ compatibleLaws H, ∀ t : Bool, ∀ j : ℕ, j ≤ 2 →
      Integrable (fun p : ℝ × ℝ => (if t then p.1 else p.2) ^ j)
        (h : Measure (ℝ × ℝ))) ∧
    (∀ h ∈ compatibleLaws H, Integrable (fun p : ℝ × ℝ => p.1 * p.2)
      (h : Measure (ℝ × ℝ))) ∧
    (∀ B, Tendsto (fun q => ((S.design q).N : ℝ) * populationBound (S.design q)
      (rowOutcomes S true q) (rowOutcomes S false q) B) atTop (𝓝 (limitingBound H θ ρ B))) ∧
    boundConsistency S) := by
  intro S H θ ρ h hUI
  obtain ⟨hm, hcross⟩ := TailB_proposition1_moments S H θ ρ h hUI
  exact ⟨hm, hcross, TailB_population_bound_limits S H θ ρ h hUI,
    TailB_bound_consistency S H θ ρ h hUI⟩

end

end AronowAudit.P022.Wave1
