import AronowAudit.P001.Wave1.Lib.TailA.RareCounts
import Mathlib.MeasureTheory.Integral.Prod

/-! Multinomial and independent Poisson mark laws, with a bounded-test comparison.

The maximum in the multinomial law supplies probability measures for the
finitely many rows too small to contain the specified labels.
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


end AronowAudit.P001.TailA
