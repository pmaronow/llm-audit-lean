/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.ComputationalStatistics.Core.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Empirical, weighted and categorical measures: basic identities

The finite-sum/measure conversions every later module reduces to:

* `isProbabilityMeasure_empiricalMeasure` — `(1/n)·Σᵢ δ_{xᵢ}` is a probability
  measure for `n ≥ 1`;
* `isProbabilityMeasure_weightedMeasure` — the weighted analogue under simplex weights;
* `weightedMeasure_eq_map_categorical`,
  `empiricalMeasure_eq_map_categorical` — a weighted sample is the pushforward
  of a categorical index draw through the data; the empirical measure is the
  uniform-weights case.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §2.5 (random sampling from data: "the discrete uniform
population defined by the data"), ch. 4 p. 83–84 (the ECDF as a population).

**Proof formalization notes.**

* `empiricalMeasure_apply` is stated for measurable sets in `ℝ≥0∞` count form
  `(1/n)·#{i | xᵢ ∈ s}`.
* The pushforward lemmas need no measurability hypothesis on `x` because
  `Fin m` is discrete (`Measurable.of_discrete`).

**Bibliographic comments.** Viewing the sample as a surrogate population is
Efron (1979); the identities here are folklore.
-/

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {n : ℕ} {x : Fin n → 𝓧} {w : Fin n → ℝ}
  {f : 𝓧 → ℝ}

/-- **The empirical measure is a probability measure** (ECS §2.5) for a sample
of positive size. -/
instance isProbabilityMeasure_empiricalMeasure [NeZero n] :
    IsProbabilityMeasure (empiricalMeasure x) := by
  constructor
  rw [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (NeZero.ne n))
    (ENNReal.natCast_ne_top n)

/-- **Counting form of the empirical measure**: on a measurable set,
`𝔽ₙ(s) = #{i | xᵢ ∈ s}/n`, the count written as an indicator sum (avoiding a
decidability instance on membership). -/
theorem empiricalMeasure_apply
    -- LEAN-ONLY: measurability of the event (regularity)
    (s : Set 𝓧) (hs : MeasurableSet s) :
    empiricalMeasure x s
      = (n : ℝ≥0∞)⁻¹ * ∑ i, s.indicator (fun _ => (1 : ℝ≥0∞)) (x i) := by
  rw [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [Measure.dirac_apply' _ hs]
  rfl


/-- **A weighted sample carries a probability measure** (ECS §2.6): under
simplex weights, `Σᵢ wᵢ·δ_{xᵢ}` is a probability measure. -/
theorem isProbabilityMeasure_weightedMeasure
    -- USER-INPUT: nonnegative weights; ECS §2.6
    (hw0 : ∀ i, 0 ≤ w i)
    -- USER-INPUT: weights sum to one; ECS §2.6
    (hw1 : ∑ i, w i = 1) :
    IsProbabilityMeasure (weightedMeasure w x) := by
  constructor
  rw [weightedMeasure, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i), hw1, ENNReal.ofReal_one]


/-- The empirical measure is the weighted empirical measure with uniform
weights `1/n`. -/
theorem empiricalMeasure_eq_weightedMeasure [NeZero n] :
    empiricalMeasure x = weightedMeasure (fun _ => (n : ℝ)⁻¹) x := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  rw [empiricalMeasure, weightedMeasure, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_inv_of_pos hn, ENNReal.ofReal_natCast]


/-- The categorical distribution is a probability measure under simplex
weights. -/
theorem isProbabilityMeasure_categorical {m : ℕ} {q : Fin m → ℝ}
    -- USER-INPUT: nonnegative probability vector; ECS §2.5
    (hq0 : ∀ i, 0 ≤ q i)
    -- USER-INPUT: probabilities sum to one; ECS §2.5
    (hq1 : ∑ i, q i = 1) :
    IsProbabilityMeasure (categorical q) := by
  rw [categorical_eq_weightedMeasure]
  exact isProbabilityMeasure_weightedMeasure hq0 hq1

/-- **A weighted sample is a pushforward index draw**: drawing an index from
`categorical w` and reading off the data realizes `weightedMeasure w x`.  No
measurability hypothesis on `x`: the index space is discrete. -/
theorem weightedMeasure_eq_map_categorical :
    weightedMeasure w x = (categorical w).map x := by
  have hx : Measurable x := Measurable.of_discrete
  ext s hs
  rw [Measure.map_apply hx hs, weightedMeasure, categorical,
    Measure.finsetSum_apply, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ hs,
    Measure.dirac_apply' _ (hx hs)]
  by_cases h : x i ∈ s <;> simp [h]

/-- **Bootstrap draws have the empirical distribution** (ECS ch. 4, p. 84):
resampling a uniform index and reading off the data realizes the empirical
measure. -/
theorem empiricalMeasure_eq_map_categorical [NeZero n] :
    empiricalMeasure x = (categorical fun _ : Fin n => (n : ℝ)⁻¹).map x := by
  rw [empiricalMeasure_eq_weightedMeasure, weightedMeasure_eq_map_categorical]

end StatLean.ComputationalStatistics
