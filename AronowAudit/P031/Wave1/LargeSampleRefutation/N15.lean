import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint
import Mathlib.Data.Nat.Choose.Central

/-! Central-binomial decay, with the square-root comparison separated from the recurrence. -/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem n15_proof : N15 := by
  intro k
  change (Nat.centralBinom k : ℝ) / 4 ^ k ≤ 1 / Real.sqrt ((k : ℝ) + 1)
  induction k with
  | zero => norm_num [Nat.centralBinom]
  | succ k ih =>
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk1 : 0 < (k : ℝ) + 1 := by positivity
    have hk2 : 0 < (k : ℝ) + 2 := by positivity
    have hs1 : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr hk1
    have hs2 : 0 < Real.sqrt ((k : ℝ) + 2) := Real.sqrt_pos.mpr hk2
    have hrec : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
        2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    have hnext : (Nat.centralBinom (k + 1) : ℝ) =
        (2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ)) / ((k : ℝ) + 1) := by
      apply (eq_div_iff hk1.ne').mpr
      nlinarith [hrec]
    have hratio : (Nat.centralBinom (k + 1) : ℝ) / 4 ^ (k + 1) =
        ((Nat.centralBinom k : ℝ) / 4 ^ k) *
          ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) := by
      rw [hnext, pow_succ]
      field_simp [hk1.ne', (pow_pos (by norm_num : (0 : ℝ) < 4) k).ne'] <;> ring
    have hsquare :
        ((2 * (k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 2)) ^ 2 ≤
          (2 * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)) ^ 2 := by
      calc
        _ = (2 * (k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) := by
          rw [mul_pow, Real.sq_sqrt hk2.le]
        _ ≤ 4 * ((k : ℝ) + 1) ^ 3 := by nlinarith
        _ = _ := by
          rw [mul_pow, Real.sq_sqrt hk1.le]
          ring
    have hroot : (2 * (k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 2) ≤
        2 * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1) :=
      (sq_le_sq₀ (by positivity) (by positivity)).mp hsquare
    have hfactor : (1 / Real.sqrt ((k : ℝ) + 1)) *
        ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) ≤
          1 / Real.sqrt ((k : ℝ) + 2) := by
      calc
        _ = (2 * (k : ℝ) + 1) /
            (2 * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)) := by
          field_simp [hs1.ne', hk1.ne'] <;> ring
        _ ≤ _ := (div_le_div_iff₀ (by positivity) hs2).mpr (by
          simpa only [one_mul] using hroot)
    simp only [Nat.cast_succ]
    rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring, hratio]
    exact (mul_le_mul_of_nonneg_right ih (by positivity)).trans hfactor

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
