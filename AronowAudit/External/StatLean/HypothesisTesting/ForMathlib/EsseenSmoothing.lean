/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.MeasureTheory.Order.Group.Lattice
import AronowAudit.External.StatLean.HypothesisTesting.ForMathlib.BerryEsseen
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Continuous ramps for distribution-function bounds

The ramp `ramp u δ` is a continuous smoothed half-line indicator. For `δ > 0`,
it is `1` on `(-∞, u]`, decreases linearly to `0` on `[u, u + δ]`, and is `0`
on `[u + δ, ∞)`. Its integral against a finite measure lies between the masses
of the half-lines ending at `u` and `u + δ`.
-/

open MeasureTheory intervalIntegral
open scoped FourierTransform Real Topology

namespace StatLean.HypothesisTesting

























/-! ## Ramps and half-line indicators -/

/-- The **ramp** (continuous smoothed indicator) `R_{u,δ}`: it equals `1` on `(-∞, u]`, falls
linearly to `0` across `[u, u + δ]`, and vanishes on `[u + δ, ∞)`. -/
noncomputable def ramp (u δ y : ℝ) : ℝ := min 1 (max 0 ((u + δ - y) / δ))

lemma ramp_nonneg (u δ y : ℝ) : 0 ≤ ramp u δ y :=
  le_min zero_le_one (le_max_left _ _)

lemma ramp_le_one (u δ y : ℝ) : ramp u δ y ≤ 1 := min_le_left _ _

lemma continuous_ramp (u δ : ℝ) : Continuous (ramp u δ) := by
  unfold ramp; fun_prop

/-- The ramp is `1` to the left of its shoulder. -/
lemma ramp_eq_one_of_le {u δ y : ℝ} (hδ : 0 < δ) (hy : y ≤ u) : ramp u δ y = 1 := by
  have h : (1 : ℝ) ≤ (u + δ - y) / δ := (one_le_div hδ).2 (by linarith)
  exact min_eq_left (le_max_of_le_right h)

/-- The ramp vanishes to the right of its foot. -/
lemma ramp_eq_zero_of_le {u δ y : ℝ} (hδ : 0 < δ) (hy : u + δ ≤ y) : ramp u δ y = 0 := by
  have h : (u + δ - y) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  simp [ramp, max_eq_left h]


lemma integrable_ramp (P : Measure ℝ) [IsFiniteMeasure P] (u δ : ℝ) :
    Integrable (ramp u δ) P :=
  (integrable_const (1 : ℝ)).mono' (continuous_ramp u δ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ramp_nonneg u δ y)]; exact ramp_le_one u δ y)

/-- The half-line indicator is dominated by the ramp sitting on it. -/
lemma measure_Iic_le_integral_ramp (P : Measure ℝ) [IsFiniteMeasure P] {δ : ℝ} (hδ : 0 < δ)
    (u : ℝ) : (P (Set.Iic u)).toReal ≤ ∫ y, ramp u δ y ∂P := by
  have hbase : (∫ y, (Set.Iic u).indicator (fun _ => (1 : ℝ)) y ∂P) = (P (Set.Iic u)).toReal := by
    rw [MeasureTheory.integral_indicator_const _ measurableSet_Iic]
    simp [measureReal_def]
  rw [← hbase]
  refine integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)
    (integrable_ramp P u δ) fun y => ?_
  · by_cases hy : y ∈ Set.Iic u
    · rw [Set.indicator_of_mem hy, ramp_eq_one_of_le hδ hy]
    · rw [Set.indicator_of_notMem hy]; exact ramp_nonneg u δ y

/-- The ramp is dominated by the indicator of the half-line ending at its foot. -/
lemma integral_ramp_le_measure_Iic (P : Measure ℝ) [IsFiniteMeasure P] {δ : ℝ} (hδ : 0 < δ)
    (u : ℝ) : (∫ y, ramp u δ y ∂P) ≤ (P (Set.Iic (u + δ))).toReal := by
  have hbase : (∫ y, (Set.Iic (u + δ)).indicator (fun _ => (1 : ℝ)) y ∂P)
      = (P (Set.Iic (u + δ))).toReal := by
    rw [MeasureTheory.integral_indicator_const _ measurableSet_Iic]
    simp [measureReal_def]
  rw [← hbase]
  refine integral_mono (integrable_ramp P u δ)
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iic) fun y => ?_
  · by_cases hy : y ∈ Set.Iic (u + δ)
    · rw [Set.indicator_of_mem hy]; exact ramp_le_one u δ y
    · rw [Set.indicator_of_notMem hy,
        ramp_eq_zero_of_le hδ (le_of_not_ge (by simpa using hy))]














variable {q : ℝ → ℝ}





end StatLean.HypothesisTesting
