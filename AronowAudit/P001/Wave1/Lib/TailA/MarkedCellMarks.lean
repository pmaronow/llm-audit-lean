import AronowAudit.P001.Wave1.Lib.TailA.RareCounts
import Mathlib.MeasureTheory.Integral.Prod

/-! Uniform replacement of multinomial marks on sample-selected original labels.

The same selected original label is used in every replica.  The replacement
error is uniform over both the embedding of the labels and the bounded test.
Consequently the labels and the test may depend on the original positions.
The harmless maximum in the reference law only supplies probability measures
for the finitely many rows too small to contain the selected labels.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA

local instance instDecidableMarkedCellMarks (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

abbrev MarkedLabelMarks (r k : ℕ) := Fin r → Fin k → ℕ

def markedSelectedMarks {r k N : ℕ} (labels : Fin k ↪ Fin N)
    (a : Fin r → Fin N → Fin N) : MarkedLabelMarks r k :=
  fun t i => (Finset.univ.filter (fun j => a t j = labels i)).card

def markedPoissonMarkLaw (r k : ℕ) : Measure (MarkedLabelMarks r k) :=
  Measure.pi (fun _ : Fin r => Measure.pi (fun _ : Fin k => poissonMeasure 1))

instance instProbabilityMarkedPoissonMarks (r k : ℕ) :
    IsProbabilityMeasure (markedPoissonMarkLaw r k) := by
  unfold markedPoissonMarkLaw
  infer_instance

def markedBootstrapMarkLaw (r k N : ℕ) : Measure (MarkedLabelMarks r k) :=
  Measure.pi (fun _ : Fin r =>
    (Measure.pi (fun _ : Fin (max (k+1) N) =>
      StatLean.ComputationalStatistics.categorical
        (rareLabelProbabilities k (max (k+1) N)))).map rareCounts)

instance instProbabilityMarkedBootstrapMarks (r k N : ℕ) :
    IsProbabilityMeasure (markedBootstrapMarkLaw r k N) := by
  haveI instProbabilityMarkedMergedCategory : IsProbabilityMeasure
      (StatLean.ComputationalStatistics.categorical
        (rareLabelProbabilities k (max (k+1) N))) :=
    StatLean.ComputationalStatistics.isProbabilityMeasure_categorical
      (rare_label_probabilities_nonneg (by omega))
      (rare_label_probabilities_sum _ _)
  unfold markedBootstrapMarkLaw
  infer_instance

/-- Conditional on any set of distinct original labels, its complete replica
mark law depends only on the number of labels and the resample size. -/
theorem marked_selected_mark_law {r k N : ℕ} (hN : k+1 ≤ N)
    (labels : Fin k ↪ Fin N) :
    (Measure.pi (fun _ : Fin r => UniformResampling N)).map
      (markedSelectedMarks labels) = markedBootstrapMarkLaw r k N := by
  unfold markedBootstrapMarkLaw
  rw [max_eq_right hN]
  have hm := Measure.pi_map_pi
    (μ := fun _ : Fin r => UniformResampling N)
    (f := fun _ a i => (Finset.univ.filter (fun j => a j = labels i)).card)
    (fun _ => Measurable.of_discrete.aemeasurable)
  change (Measure.pi (fun _ : Fin r => UniformResampling N)).map
    (fun a t i => (Finset.univ.filter (fun j => a t j = labels i)).card) = _
  rw [hm]
  simp only [fixed_original_label_count_law (by omega : 0 < N) labels]

/-- Reference singleton masses converge, including all replica coordinates. -/
theorem marked_mark_singleton_limit (r k : ℕ) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (v : MarkedLabelMarks r k) :
    Tendsto (fun n => markedBootstrapMarkLaw r k (m n) {v}) atTop
      (𝓝 (markedPoissonMarkLaw r k {v})) := by
  let M : ℕ → ℕ := fun n => max (k+1) (m n)
  have hM : Tendsto M atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_right _ _) hm
  have hRate (i : Fin k) : Tendsto (fun n =>
      (M n : ℝ)*rareLabelProbabilities k (M n) i.castSucc) atTop (𝓝 (1 : ℝ)) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))) using 1
    funext n
    simp only [rareLabelProbabilities, Fin.snoc_castSucc]
    have hMn : 0 < M n := by dsimp [M]; omega
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hMn))
  have hs (u : Fin k → ℕ) := rare_counts_singleton_limit k M hM
    (fun n => rareLabelProbabilities k (M n))
    (fun n => rare_label_probabilities_nonneg (by dsimp [M]; omega))
    (fun n => rare_label_probabilities_sum _ _) (fun _ => 1) hRate u
  have ht := ENNReal.tendsto_finsetProd_of_ne_top Finset.univ
    (fun t _ => hs (v t))
    (fun t _ => measure_ne_top (Measure.pi fun _ : Fin k => poissonMeasure 1) {v t})
  simpa only [markedBootstrapMarkLaw, markedPoissonMarkLaw, Measure.pi_singleton, M]
    using ht

/-- The sum of absolute singleton-mass errors; no factor of one half is used. -/
def markedMarkError (r k N : ℕ) : ℝ :=
  ∑' v : MarkedLabelMarks r k,
    |(markedBootstrapMarkLaw r k N {v}).toReal -
      (markedPoissonMarkLaw r k {v}).toReal|

theorem marked_mark_error_nonneg (r k N : ℕ) : 0 ≤ markedMarkError r k N :=
  tsum_nonneg (fun _ => abs_nonneg _)

theorem marked_mark_error_tendsto (r k : ℕ) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => markedMarkError r k (m n)) atTop (𝓝 0) := by
  apply rare_counts_scheffe
    (fun n v => (markedBootstrapMarkLaw r k (m n) {v}).toReal)
    (fun v => (markedPoissonMarkLaw r k {v}).toReal)
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (fun n => rare_counts_hasSum_singletons (markedBootstrapMarkLaw r k (m n)))
    (rare_counts_hasSum_singletons (markedPoissonMarkLaw r k))
  intro v
  exact (ENNReal.tendsto_toReal (measure_ne_top (markedPoissonMarkLaw r k) {v})).comp
    (marked_mark_singleton_limit r k m hm v)

/-- A bounded test is controlled by the sum of absolute point-mass errors. -/
theorem marked_countable_test_difference {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [Countable E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : E → ℝ) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤
      C * ∑' x : E, |(μ {x}).toReal - (ν {x}).toReal| := by
  have hfi (ρ : Measure E) [IsProbabilityMeasure ρ] : Integrable f ρ :=
    Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable C
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hf x))
  have hsum (ρ : Measure E) [IsProbabilityMeasure ρ] :
      Summable (fun x => (ρ {x}).toReal * f x) := by
    apply ((rare_counts_hasSum_singletons ρ).summable.mul_right C).of_norm_bounded
    intro x
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf x) ENNReal.toReal_nonneg
  have he : Summable (fun x => |(μ {x}).toReal - (ν {x}).toReal|) :=
    ((rare_counts_hasSum_singletons μ).summable.sub
      (rare_counts_hasSum_singletons ν).summable).abs
  rw [integral_countable (hfi μ), integral_countable (hfi ν)]
  simp only [measureReal_def, smul_eq_mul]
  rw [← (hsum μ).tsum_sub (hsum ν)]
  change ‖tsum (fun x : E => (μ {x}).toReal * f x - (ν {x}).toReal * f x)‖ ≤ _
  apply (norm_tsum_le_tsum_norm (((hsum μ).sub (hsum ν)).norm)).trans
  rw [← he.tsum_mul_left]
  apply Summable.tsum_le_tsum _ ((hsum μ).sub (hsum ν)).norm (he.mul_left C)
  intro x
  rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)).trans_eq (mul_comm _ _)

/-- Uniformity over every choice of distinct labels and every bounded test. -/
theorem marked_selected_test_difference {r k N : ℕ} (hN : k+1 ≤ N)
    (labels : Fin k ↪ Fin N) (f : MarkedLabelMarks r k → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ v, |f v| ≤ C) :
    |(∫ a, f (markedSelectedMarks labels a)
        ∂Measure.pi (fun _ : Fin r => UniformResampling N)) -
      ∫ v, f v ∂markedPoissonMarkLaw r k| ≤ C*markedMarkError r k N := by
  rw [← integral_map Measurable.of_discrete.aemeasurable
    (measurable_of_countable f).aestronglyMeasurable,
    marked_selected_mark_law hN labels]
  exact marked_countable_test_difference _ _ f hC hf

end AronowAudit.P001.TailA
