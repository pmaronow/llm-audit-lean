import AronowAudit.P002.Wave1.E61EigenvalueBlueprint
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace AronowAudit.P002.Wave1.E61Eigenvalue
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

universe u

/-- First Borel--Cantelli at reciprocal integer thresholds. No measurability of D is needed. -/
theorem n9_proof : N9.{u} := by
  intro Ω _ μ D bound hsum hbound
  have hthreshold (q : ℕ) :
      ∀ᵐ ω ∂μ, ∀ᶠ j in atTop, ¬ (1 / ((q : ℝ) + 1) ≤ |D j ω|) := by
    have hqpos : 0 < (1 : ℝ) / ((q : ℝ) + 1) := by positivity
    have hfinite :
        (∑' j, μ {ω | 1 / ((q : ℝ) + 1) ≤ |D j ω|}) ≠ ∞ := by
      have hcomparison :
          (∑' j, μ {ω | 1 / ((q : ℝ) + 1) ≤ |D j ω|}) ≤
            ∑' j, ENNReal.ofReal (bound (1 / ((q : ℝ) + 1)) j) :=
        ENNReal.tsum_le_tsum (fun j => hbound _ hqpos j)
      -- This lemma handles signed bounds by summability of their positive parts.
      exact (lt_of_le_of_lt hcomparison (hsum _ hqpos).tsum_ofReal_lt_top).ne
    simpa only [Set.mem_setOf_eq] using
      (MeasureTheory.ae_eventually_notMem (μ := μ)
        (s := fun j => {ω | 1 / ((q : ℝ) + 1) ≤ |D j ω|}) hfinite)
  have hωall :
      ∀ᵐ ω ∂μ, ∀ q : ℕ, ∀ᶠ j in atTop, ¬ (1 / ((q : ℝ) + 1) ≤ |D j ω|) :=
    MeasureTheory.ae_all_iff.mpr hthreshold
  filter_upwards [hωall] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨q, hq⟩ := exists_nat_one_div_lt hε
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp (hω q)
  refine ⟨J, fun j hj => ?_⟩
  have hDj : |D j ω| < 1 / ((q : ℝ) + 1) := lt_of_not_ge (hJ j hj)
  simpa only [Real.dist_eq, sub_zero] using hDj.trans hq

end
end AronowAudit.P002.Wave1.E61Eigenvalue
