import AronowAudit.P018.P018_Audit
import AronowAudit.P061.P061_Foundations
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Varying-row weak convergence, perturbation, and continuity-set adapters. -/

set_option linter.style.haveILetI false

noncomputable section
namespace AronowAudit.Shared.MapTailB
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

theorem TailB_weakLimit_perturbation
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : (n : ℕ) → Ω n → E) (G : Measure E)
    (hX : AronowAudit.P018.weakLimit P X G)
    (hY : ∀ n, AEMeasurable (Y n) (P n))
    (hclose : AronowAudit.P018.inProbability P (fun n w => X n w - Y n w)) :
    AronowAudit.P018.weakLimit P Y G := by
  letI tb05_limit_probability : IsProbabilityMeasure G := hX.2.1
  have hmap : AronowAudit.P061.Analytic.WeakConvergesLaw
      (fun n => (P n).map (X n)) G := by
    intro g
    simpa only [integral_map (hX.1 _) g.continuous.aestronglyMeasurable] using hX.2.2 g
  have hdist : ∀ ε > 0,
      Tendsto (fun n => (P n).real {w | ε ≤ dist (X n w) (Y n w)}) atTop (𝓝 0) := by
    simpa only [dist_eq_norm, Measure.real, AronowAudit.P018.inProbability] using hclose
  have h := AronowAudit.P061.Analytic.weakConvergesLaw_slutsky_dist
    hX.1 hY hmap hdist
  refine ⟨hY, hX.2.1, fun g => ?_⟩
  simpa only [integral_map (hY _) g.continuous.aestronglyMeasurable] using h g

theorem TailB_weakLimit_continuity_set
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : (n : ℕ) → Ω n → E) (G : Measure E)
    (hX : AronowAudit.P018.weakLimit P X G)
    (s : Set E) (hs : MeasurableSet s) (hboundary : G (frontier s) = 0) :
    Tendsto (fun n => (P n (X n ⁻¹' s)).toReal) atTop (𝓝 ((G s).toReal)) := by
  letI tb05_limit_probability : IsProbabilityMeasure G := hX.2.1
  let M : ℕ → ProbabilityMeasure E := fun n =>
    ⟨(P n).map (X n), inferInstance⟩
  let L : ProbabilityMeasure E := ⟨G, hX.2.1⟩
  have ht : Tendsto M atTop (𝓝 L) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro g
    simpa only [M, L, ProbabilityMeasure.coe_mk,
      integral_map (hX.1 _) g.continuous.aestronglyMeasurable] using hX.2.2 g
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    ht hboundary
  have hr := (ENNReal.continuousAt_toReal (measure_ne_top G s)).tendsto.comp hm
  simpa only [M, L, ProbabilityMeasure.coe_mk,
    Measure.map_apply_of_aemeasurable (hX.1 _) hs, Function.comp_def] using hr

theorem TailB_weakLimit_Iio
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : (n : ℕ) → Ω n → ℝ) (G : Measure ℝ)
    (hX : AronowAudit.P018.weakLimit P X G) (x : ℝ) (hx : G {x} = 0) :
    Tendsto (fun n => (P n {w | X n w < x}).toReal) atTop
      (𝓝 ((G (Set.Iio x)).toReal)) := by
  exact TailB_weakLimit_continuity_set P X G hX (Set.Iio x) measurableSet_Iio
    (by simpa only [frontier_Iio] using hx)

theorem TailB_weakLimit_continuous_map
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E F : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : (n : ℕ) → Ω n → E) (G : Measure E)
    (hX : AronowAudit.P018.weakLimit P X G) (f : E → F) (hf : Continuous f) :
    AronowAudit.P018.weakLimit P (fun n w => f (X n w)) (G.map f) := by
  letI tb05_limit_probability : IsProbabilityMeasure G := hX.2.1
  refine ⟨fun n => hf.measurable.comp_aemeasurable (hX.1 n),
    inferInstance, fun g => ?_⟩
  simpa only [integral_map hf.measurable.aemeasurable g.continuous.aestronglyMeasurable,
    BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
    using hX.2.2 (g.compContinuous ⟨f, hf⟩)


/-- A positive limiting probability of a negative variance creates an atom at zero
for the totalized square-root pivot, ruling out a standard Gaussian limit. -/
theorem TailB_no_gaussian_limit_negative_variance
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X V : (n : ℕ) → Ω n → ℝ) (c : ℝ) (hc : 0 < c)
    (hnegative : Tendsto (fun n => (P n {w | V n w < 0}).toReal) atTop (𝓝 c)) :
    ¬ AronowAudit.P018.weakLimit P (fun n w => X n w / Real.sqrt (V n w))
      (ProbabilityTheory.gaussianReal 0 1) := by
  intro hweak
  letI tb05_gaussian_null : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num)
  have hz : ProbabilityTheory.gaussianReal 0 1 ({0} : Set ℝ) = 0 := by
    exact measure_singleton _
  have hf : ProbabilityTheory.gaussianReal 0 1 (frontier ({0} : Set ℝ)) = 0 := by
    exact measure_mono_null frontier_subset_closure (by simpa using hz)
  have hzero := TailB_weakLimit_continuity_set P _ _ hweak ({0} : Set ℝ)
    (measurableSet_singleton 0) hf
  simp only [hz, ENNReal.toReal_zero] at hzero
  have hbound (n : ℕ) : (P n {w | V n w < 0}).toReal ≤
      (P n ((fun w => X n w / Real.sqrt (V n w)) ⁻¹' {0})).toReal := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro w hw
    simp only [Set.mem_setOf_eq] at hw
    simp [Real.sqrt_eq_zero_of_nonpos hw.le]
  have : c ≤ 0 := le_of_tendsto_of_tendsto' hnegative hzero hbound
  exact (not_le_of_gt hc) this

end AronowAudit.Shared.MapTailB
