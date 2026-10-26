import AronowAudit.P004.Wave1.AreaSum.A4
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace AronowAudit.P004.Wave1.AreaSum

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

theorem a5_proof : A5 := by
  classical
  constructor
  · intro c j
    have hdisk (r : ℝ) (hr : 0 ≤ r) :
        volume (Metric.closedBall c r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
      rw [EuclideanSpace.volume_closedBall_fin_two,
        ENNReal.ofReal_mul Real.pi_nonneg, ENNReal.ofReal_pow hr]
      exact mul_comm _ _
    by_cases hj : j = 0
    · subst j
      simpa [bin] using hdisk 1 zero_le_one
    · have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
      have hj1 : 0 ≤ (j : ℝ) + 1 := by positivity
      have hset : bin c j =
          Metric.closedBall c ((j : ℝ) + 1) \ Metric.closedBall c (j : ℝ) := by
        ext x
        simp only [bin, if_neg hj, Set.mem_setOf_eq, Set.mem_sdiff,
          Metric.mem_closedBall, not_le]
        exact and_comm
      have hsub : Metric.closedBall c (j : ℝ) ⊆
          Metric.closedBall c ((j : ℝ) + 1) :=
        Metric.closedBall_subset_closedBall (by linarith)
      have hfinite : volume (Metric.closedBall c (j : ℝ)) ≠ ⊤ := by
        rw [hdisk (j : ℝ) hj0]
        exact ENNReal.ofReal_ne_top
      rw [hset, measure_sdiff hsub Metric.isClosed_closedBall.measurableSet.nullMeasurableSet hfinite,
        hdisk ((j : ℝ) + 1) hj1, hdisk (j : ℝ) hj0,
        ← ENNReal.ofReal_sub _ (mul_nonneg Real.pi_nonneg (sq_nonneg (j : ℝ)))]
      congr 1
      ring
  · intro c q hq0 hq
    have hset :
        (Metric.closedBall c 1 ∩ {x | angularFraction c x < q}) \ {c} =
          {x | (0 : ℝ) < dist x c ∧ dist x c ≤ 1} ∩
            {x | angularFraction c x < q} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Metric.mem_closedBall,
        Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨hx, hangle⟩, hxc⟩
        exact ⟨⟨dist_pos.mpr hxc, hx⟩, hangle⟩
      · rintro ⟨⟨hpos, hx⟩, hangle⟩
        exact ⟨⟨hx, hangle⟩, dist_pos.mp hpos⟩
    calc
      volume (Metric.closedBall c 1 ∩ {x | angularFraction c x < q}) =
          volume ((Metric.closedBall c 1 ∩ {x | angularFraction c x < q}) \ {c}) :=
        (measure_sdiff_null (measure_singleton c)).symm
      _ = ENNReal.ofReal (q * Real.pi) := by
        rw [hset]
        simpa only [one_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, mul_one]
          using a4_proof c 0 1 q (by norm_num) (by norm_num) hq0 hq

end
end AronowAudit.P004.Wave1.AreaSum
