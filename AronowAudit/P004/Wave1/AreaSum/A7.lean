import AronowAudit.P004.Wave1.AreaSumBlueprint
import AronowAudit.P004.Wave1.AreaSum.A2
import AronowAudit.P004.Wave1.AreaSum.A5
import AronowAudit.P004.Wave1.AreaSum.A6
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Positive finite masses and integrability for the seven bands used in case B. -/

namespace AronowAudit.P004.Wave1.AreaSum

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- A globally measurable binary field is integrable on every set of finite volume. -/
theorem areaBinary_integrableOn {s : Set (EuclideanSpace ℝ (Fin 2))}
    (hs : volume s ≠ ⊤) (z : Assignment 2) :
    IntegrableOn (fun x => areaBinaryPopulation.outcome x z) s volume := by
  apply Measure.integrableOn_of_bounded hs
    ((a6_proof.2.1 z).aestronglyMeasurable) (M := 1)
  exact Eventually.of_forall fun x => by
    rcases a6_proof.1 x z with hx | hx <;> rw [hx] <;> norm_num

theorem a7_proof : A7 := by
  constructor
  · intro j i
    change MeasurableSet (region areaBinaryPopulation i (j : ℝ)) ∧
      0 < volume (region areaBinaryPopulation i (j : ℝ)) ∧
      volume (region areaBinaryPopulation i (j : ℝ)) < ⊤ ∧
      ∀ z, IntegrableOn (fun x => areaBinaryPopulation.outcome x z)
        (region areaBinaryPopulation i (j : ℝ)) volume
    rw [a2_proof.1 i j]
    have hvol := a5_proof.1 (areaBinaryCenter i) (j : ℕ)
    have hpos : 0 < Real.pi * (2 * (j : ℝ) + 1) := by positivity
    have hfin : volume (bin (areaBinaryCenter i) (j : ℕ)) ≠ ⊤ := by
      rw [hvol]
      exact ENNReal.ofReal_ne_top
    refine ⟨measurableSet_bin _ _, ?_, lt_top_iff_ne_top.mpr hfin,
      fun z => areaBinary_integrableOn hfin z⟩
    rw [hvol]
    exact ENNReal.ofReal_pos.mpr hpos
  · intro i
    change MeasurableSet (region areaBinaryPopulation i 6) ∧
      0 < volume (region areaBinaryPopulation i 6) ∧
      volume (region areaBinaryPopulation i 6) < ⊤ ∧
      ∀ z, IntegrableOn (fun x => areaBinaryPopulation.outcome x z)
        (region areaBinaryPopulation i 6) volume
    rw [a2_proof.2 i]
    have hvol : volume (Metric.closedBall (areaBinaryCenter i) 6) =
        ENNReal.ofReal (36 * Real.pi) := by
      rw [EuclideanSpace.volume_closedBall_fin_two,
        ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 6) 2,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6 ^ 2)]
      norm_num
    have hfin : volume (Metric.closedBall (areaBinaryCenter i) 6) ≠ ⊤ := by
      rw [hvol]
      exact ENNReal.ofReal_ne_top
    refine ⟨measurableSet_closedBall, ?_, lt_top_iff_ne_top.mpr hfin,
      fun z => areaBinary_integrableOn hfin z⟩
    rw [hvol]
    exact ENNReal.ofReal_pos.mpr (by positivity)

end
end AronowAudit.P004.Wave1.AreaSum
