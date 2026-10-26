import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellMarks

/-! Varying bounded tests of the actual discrete rare-count laws. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA

local instance instDecidableMarkedCellDiscreteLimits (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000

/-- Discrete convergence in total variation permits the test to change with
the row, as long as the tests are uniformly bounded and converge pointwise. -/
theorem marked_countable_varying_test_limit {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [Countable E]
    (μ : ℕ → Measure E) (ν : Measure E)
    (hμ : ∀ n, IsProbabilityMeasure (μ n)) [IsProbabilityMeasure ν]
    (hsingle : ∀ e, Tendsto (fun n => ((μ n) {e}).toReal)
      atTop (𝓝 ((ν {e}).toReal)))
    (F : ℕ → E → ℝ) (f : E → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n e, |F n e| ≤ C)
    (hlim : ∀ e, Tendsto (fun n => F n e) atTop (𝓝 (f e))) :
    Tendsto (fun n => ∫ e, F n e ∂μ n) atTop (𝓝 (∫ e, f e ∂ν)) := by
  haveI instProbabilityMarkedVaryingRows (n : ℕ) : IsProbabilityMeasure (μ n) := hμ n
  have htv := rare_counts_scheffe (fun n e => ((μ n) {e}).toReal)
    (fun e => (ν {e}).toReal) (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ => ENNReal.toReal_nonneg) (fun n => rare_counts_hasSum_singletons (μ n))
    (rare_counts_hasSum_singletons ν) hsingle
  have hdiff : Tendsto (fun n => (∫ e, F n e ∂μ n) - ∫ e, F n e ∂ν)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => marked_countable_test_difference
      (μ n) ν (F n) hC (hbound n))
    simpa only [mul_zero] using htv.const_mul C
  have hfixed := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => C)
    (fun n => (measurable_of_countable (F n)).aestronglyMeasurable)
    (integrable_const C) (fun n => ae_of_all _ (hbound n)) (ae_of_all _ hlim)
  convert hdiff.add hfixed using 1
  · funext n
    ring
  · simp only [zero_add]

/-- The changing-space form, using a proved discrete `RowWeak` endpoint. -/
theorem marked_discrete_varying_test_limit
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [Countable E] [TopologicalSpace E] [DiscreteTopology E]
    (P : (n : ℕ) → Measure (Ω n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (X : (n : ℕ) → Ω n → E) (hX : ∀ n, Measurable (X n))
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hweak : AronowAudit.Literature.RowWeak P X ν)
    (F : ℕ → E → ℝ) (f : E → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n e, |F n e| ≤ C)
    (hlim : ∀ e, Tendsto (fun n => F n e) atTop (𝓝 (f e))) :
    Tendsto (fun n => ∫ x, F n (X n x) ∂P n) atTop (𝓝 (∫ e, f e ∂ν)) := by
  haveI instProbabilityMarkedDiscreteRows (n : ℕ) : IsProbabilityMeasure (P n) := hP n
  have hsingle (e : E) : Tendsto (fun n => (((P n).map (X n)) {e}).toReal)
      atTop (𝓝 ((ν {e}).toReal)) := by
    let g : E → ℝ := ({e} : Set E).indicator (fun _ => 1)
    have hgb (y : E) : |g y| ≤ 1 := by
      dsimp [g]
      by_cases hy : y = e <;> simp [hy]
    have ht := hweak g continuous_of_discreteTopology ⟨1, hgb⟩
    have hrow (n : ℕ) : (∫ x, g (X n x) ∂P n) = (((P n).map (X n)) {e}).toReal := by
      rw [← integral_map (hX n).aemeasurable (measurable_of_countable g).aestronglyMeasurable]
      simp only [g, integral_indicator_const _ (measurableSet_singleton e),
        smul_eq_mul, mul_one, measureReal_def]
    have hlast : (∫ y, g y ∂ν) = (ν {e}).toReal := by
      simp only [g, integral_indicator_const _ (measurableSet_singleton e),
        smul_eq_mul, mul_one, measureReal_def]
    simpa only [hrow, hlast] using ht
  have ht := marked_countable_varying_test_limit (fun n => (P n).map (X n)) ν
    (fun _ => inferInstance) hsingle F f hC hbound hlim
  convert ht using 1
  funext n
  exact (integral_map (hX n).aemeasurable
    (measurable_of_countable (F n)).aestronglyMeasurable).symm

/-- The Poisson probability-generating integral, derived from its actual masses. -/
theorem marked_poisson_power_integral (rate : ℝ≥0) (z : ℝ) :
    (∫ n : ℕ, z^n ∂poissonMeasure rate) = Real.exp ((rate : ℝ)*(z-1)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  have hs : HasSum (fun n : ℕ =>
      Real.exp (-(rate : ℝ))*((rate : ℝ)*z)^n/(n.factorial : ℝ))
      (Real.exp (-(rate : ℝ))*Real.exp ((rate : ℝ)*z)) := by
    simpa only [mul_div_assoc, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ((rate : ℝ)*z)).mul_left
        (Real.exp (-(rate : ℝ)))
  have heq (n : ℕ) : (Real.exp (-(rate : ℝ))*(rate : ℝ)^n/(n.factorial : ℝ))*z^n =
      Real.exp (-(rate : ℝ))*((rate : ℝ)*z)^n/(n.factorial : ℝ) := by
    rw [mul_pow]
    ring
  simp only [heq]
  rw [hs.tsum_eq, ← Real.exp_add]
  congr 1
  ring

theorem marked_poisson_product_power_integral (q : ℕ) (rates : Fin q → ℝ≥0)
    (z : Fin q → ℝ) :
    (∫ v : Fin q → ℕ, ∏ i, (z i)^(v i) ∂Measure.pi
      (fun i => poissonMeasure (rates i))) =
      Real.exp (∑ i, (rates i : ℝ)*(z i-1)) := by
  rw [integral_fintype_prod_eq_prod]
  simp_rw [marked_poisson_power_integral]
  exact (Real.exp_sum _ _).symm

end AronowAudit.P001.TailA
