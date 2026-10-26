import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint
import Mathlib.Analysis.Real.Sqrt

/-! Expand the difference in means using zero controls, then use
the supplied true-variance formula. Positivity and the square-root identity
for the power-of-two population size are isolated before clearing divisors. -/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem n10_proof : N10 := by
  intro hvariance n s hs
  obtain ⟨hVar, hEffect⟩ := hvariance n
  let A : ℝ := (2 : ℝ) ^ (2 * (n + 1) ^ 2)
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hN16 : (16 : ℝ) ≤ (hcN n : ℝ) := by
    exact_mod_cast hcN_ge n
  have hN : 0 < (hcN n : ℝ) := by linarith
  have hN1 : 0 < (hcN n : ℝ) - 1 := by linarith
  have hN2 : 0 < (hcN n : ℝ) - 2 := by linarith
  have hNpow : (hcN n : ℝ) = A ^ 2 := by
    dsimp only [A, hcN, hcK]
    rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
    congr 1
    ring
  have hsqrtN : Real.sqrt (hcN n : ℝ) = A := by
    rw [hNpow, Real.sqrt_sq hA.le]
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtN1 : 0 < Real.sqrt ((hcN n : ℝ) - 1) := Real.sqrt_pos.2 hN1
  have hsqrtN2 : 0 < Real.sqrt ((hcN n : ℝ) - 2) := Real.sqrt_pos.2 hN2
  have hsqrtVar :
      Real.sqrt (((hcN n : ℝ) - 2) /
          (2 * (hcN n : ℝ) * ((hcN n : ℝ) - 1))) =
        Real.sqrt ((hcN n : ℝ) - 2) /
          (Real.sqrt 2 * A * Real.sqrt ((hcN n : ℝ) - 1)) := by
    rw [Real.sqrt_div hN2.le,
      Real.sqrt_mul (show 0 ≤ 2 * (hcN n : ℝ) by positivity),
      Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num), hsqrtN]
  have hsqrtRatio :
      Real.sqrt (((hcN n : ℝ) - 1) / ((hcN n : ℝ) - 2)) =
        Real.sqrt ((hcN n : ℝ) - 1) / Real.sqrt ((hcN n : ℝ) - 2) :=
    Real.sqrt_div hN1.le _

  have hcard : s.card = 2 := by
    simpa only [hypercubePopulation] using (Finset.mem_powersetCard.mp hs).2
  have htreated :
      (∑ i ∈ s, observed s (hypercubePopulation n).y1 (hypercubePopulation n).y0 i) =
        (∑ i ∈ s, hcQ n i) / A := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    exact observed_treatment s (hypercubePopulation n).y1
      (hypercubePopulation n).y0 hi
  have hcontrol :
      (∑ i ∈ sᶜ, observed s (hypercubePopulation n).y1 (hypercubePopulation n).y0 i) =
        0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact observed_control s (hypercubePopulation n).y1
      (hypercubePopulation n).y0 hi
  have hpoint : pointEstimate (hypercubePopulation n) s =
      (∑ i ∈ s, hcQ n i) / (2 * A) := by
    unfold pointEstimate estimate groupMean
    rw [htreated, hcontrol, hcard]
    simp only [Nat.cast_ofNat, zero_div, sub_zero]
    rw [div_div, mul_comm A 2]

  rw [hpoint, hEffect, sub_zero, hVar, hsqrtVar, hsqrtRatio]
  field_simp [hA.ne', hsqrt2.ne', hsqrtN1.ne', hsqrtN2.ne'] <;>
    ring_nf <;> norm_num [Real.sq_sqrt]

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
