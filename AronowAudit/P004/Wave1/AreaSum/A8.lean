import AronowAudit.P004.Wave1.AreaSumBlueprint
import AronowAudit.P004.Wave1.AreaSum.A2
import AronowAudit.P004.Wave1.AreaSum.A4
import AronowAudit.P004.Wave1.AreaSum.A5
import AronowAudit.P004.Wave1.AreaSum.A6
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Evaluation of each actual bin integral, for every node and complete assignment. -/

namespace AronowAudit.P004.Wave1.AreaSum

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Every one of the six bins lies in the radius-six disk about its center. -/
theorem bin_dist_le_six (c x : EuclideanSpace ℝ (Fin 2)) (j : Fin 6)
    (hx : x ∈ bin c (j : ℕ)) : dist x c ≤ 6 := by
  have hj : (j : ℝ) ≤ 5 := by
    exact_mod_cast (Nat.le_of_lt_succ j.isLt)
  unfold bin at hx
  split_ifs at hx with hj0
  · have hx1 : dist x c ≤ 1 := Metric.mem_closedBall.mp hx
    linarith
  · have hxupper : dist x c ≤ (j : ℝ) + 1 := hx.2
    linarith

/-- The share's radial branch is constant on a bin, including the radius-one boundary. -/
theorem areaBinaryShare_on_bin (c x : EuclideanSpace ℝ (Fin 2)) (j : Fin 6)
    (hx : x ∈ bin c (j : ℕ)) (a : Bool) :
    areaBinaryShare c x a = binShare j a := by
  classical
  by_cases hj : j = 0
  · subst j
    have hx1 : dist x c ≤ 1 := by
      simpa only [bin, Fin.val_zero, ↓reduceIte, Metric.mem_closedBall] using hx
    cases a <;> simp [areaBinaryShare, binShare, hx1]
  · have hjNat : (j : ℕ) ≠ 0 := by
      intro h
      apply hj
      exact Fin.ext h
    have hxouter : (j : ℝ) < dist x c ∧ dist x c ≤ (j : ℝ) + 1 := by
      simpa only [bin, if_neg hjNat, Set.mem_setOf_eq] using hx
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hjNat)
    have hxnot : ¬ dist x c ≤ 1 := by linarith [hxouter.1]
    cases a <;> simp [areaBinaryShare, binShare, hj, hxnot]

/-- The two disk centers are far enough apart that node 1's bins cannot select
node 0's branch of the globally defined outcome. -/
theorem areaBinaryCenter_distance :
    dist (areaBinaryCenter 0) (areaBinaryCenter 1) = 100 := by
  norm_num [areaBinaryCenter, planePoint, EuclideanSpace.dist_eq, Fin.sum_univ_succ]

/-- The actual outcome, restricted to a node's bin, is precisely its sector indicator. -/
theorem areaBinary_outcome_on_bin (j : Fin 6) (i : Fin 2) (z : Assignment 2)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ bin (areaBinaryCenter i) (j : ℕ)) :
    areaBinaryPopulation.outcome x z =
      ({y | angularFraction (areaBinaryCenter i) y < binShare j (z i)}).indicator
        (fun _ => (1 : ℝ)) x := by
  classical
  have hnear : dist x (areaBinaryCenter i) ≤ 6 := bin_dist_le_six _ _ j hx
  have hshare : areaBinaryShare (areaBinaryCenter i) x (z i) = binShare j (z i) :=
    areaBinaryShare_on_bin _ _ j hx (z i)
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · simp only [areaBinaryPopulation, if_pos hnear, hshare]
    by_cases h : angularFraction (areaBinaryCenter 0) x < binShare j (z 0)
    · rw [if_pos h, Set.indicator_of_mem
        (by exact h : x ∈ {y | angularFraction (areaBinaryCenter 0) y < binShare j (z 0)})]
    · rw [if_neg h, Set.indicator_of_notMem
        (by exact h : x ∉ {y | angularFraction (areaBinaryCenter 0) y < binShare j (z 0)})]
  · have htriangle := dist_triangle (areaBinaryCenter 0) x (areaBinaryCenter 1)
    rw [areaBinaryCenter_distance, dist_comm (areaBinaryCenter 0) x] at htriangle
    have hfar : ¬ dist x (areaBinaryCenter 0) ≤ 6 := by linarith
    simp only [areaBinaryPopulation, if_neg hfar, if_pos hnear, hshare]
    by_cases h : angularFraction (areaBinaryCenter 1) x < binShare j (z 1)
    · rw [if_pos h, Set.indicator_of_mem
        (by exact h : x ∈ {y | angularFraction (areaBinaryCenter 1) y < binShare j (z 1)})]
    · rw [if_neg h, Set.indicator_of_notMem
        (by exact h : x ∉ {y | angularFraction (areaBinaryCenter 1) y < binShare j (z 1)})]

/-- The shares fall in the range of the sector-measure node. -/
theorem binShare_bounds (j : Fin 6) (a : Bool) :
    0 ≤ binShare j a ∧ binShare j a ≤ 1 / 2 := by
  classical
  cases a <;> by_cases hj : j = 0 <;> norm_num [binShare, hj]

/-- The central disk uses A5's disk sector; outer bins use A4's annular sector. -/
theorem bin_sector_volume (c : EuclideanSpace ℝ (Fin 2)) (j : Fin 6) (a : Bool) :
    volume (bin c (j : ℕ) ∩ {x | angularFraction c x < binShare j a}) =
      ENNReal.ofReal (binShare j a * Real.pi * (2 * (j : ℝ) + 1)) := by
  classical
  obtain ⟨hq0, hqhalf⟩ := binShare_bounds j a
  by_cases hj : j = 0
  · subst j
    simpa only [bin, Fin.val_zero, ↓reduceIte, Nat.cast_zero,
      mul_zero, zero_add, mul_one] using
      a5_proof.2 c (binShare 0 a) hq0 hqhalf
  · have hjNat : (j : ℕ) ≠ 0 := by
      intro h
      apply hj
      exact Fin.ext h
    rw [bin, if_neg hjNat]
    have hsector := a4_proof c (j : ℝ) ((j : ℝ) + 1) (binShare j a)
      (by positivity) (by linarith) hq0 hqhalf
    have hsquare : ((j : ℝ) + 1) ^ 2 - (j : ℝ) ^ 2 = 2 * (j : ℝ) + 1 := by ring
    simpa only [hsquare] using hsector

theorem a8_proof : A8 := by
  classical
  intro j i z
  have hq0 : 0 ≤ binShare j (z i) := (binShare_bounds j (z i)).1
  have harea : 0 < Real.pi * (2 * (j : ℝ) + 1) := by positivity
  have hsectorMeas : MeasurableSet
      {x | angularFraction (areaBinaryCenter i) x < binShare j (z i)} :=
    measurableSet_lt (a6_proof.2.2 (areaBinaryCenter i)) measurable_const
  have hnum :
      (∫ x in bin (areaBinaryCenter i) (j : ℕ), areaBinaryPopulation.outcome x z) =
        binShare j (z i) * Real.pi * (2 * (j : ℝ) + 1) := by
    calc
      _ = ∫ x in bin (areaBinaryCenter i) (j : ℕ),
          ({y | angularFraction (areaBinaryCenter i) y < binShare j (z i)}).indicator
            (fun _ => (1 : ℝ)) x :=
        setIntegral_congr_fun (measurableSet_bin _ _) fun x hx =>
          areaBinary_outcome_on_bin j i z x hx
      _ = (volume (bin (areaBinaryCenter i) (j : ℕ) ∩
          {x | angularFraction (areaBinaryCenter i) x < binShare j (z i)})).toReal := by
        rw [setIntegral_indicator hsectorMeas, setIntegral_const]
        simp only [Measure.real, smul_eq_mul, mul_one]
      _ = binShare j (z i) * Real.pi * (2 * (j : ℝ) + 1) := by
        rw [bin_sector_volume, ENNReal.toReal_ofReal (by positivity)]
  change (∫ x in region areaBinaryPopulation i (j : ℝ),
      areaBinaryPopulation.outcome x z ∂volume) /
    (volume (region areaBinaryPopulation i (j : ℝ))).toReal = binShare j (z i)
  rw [a2_proof.1 i j, hnum, a5_proof.1,
    ENNReal.toReal_ofReal (le_of_lt harea)]
  apply (div_eq_iff harea.ne').2
  ring

end
end AronowAudit.P004.Wave1.AreaSum
