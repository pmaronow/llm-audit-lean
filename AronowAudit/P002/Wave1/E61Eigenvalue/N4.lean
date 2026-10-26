import AronowAudit.P002.Wave1.E61EigenvalueBlueprint
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Exp

namespace AronowAudit.P002.Wave1.E61Eigenvalue
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

universe u

/-- Finite Chernoff bounds for `a` and `-a`, followed by the two-event union bound. -/
theorem n4_proof : N4 := by
  intro hTwo hMGF N p a s hp hp1 hs hV
  let w : Finset (Fin N) → ℝ := fun T => p ^ T.card * (1 - p) ^ (N - T.card)
  have hw (T : Finset (Fin N)) : 0 ≤ w T := by
    dsimp [w]
    exact mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp1) _)
  have hmgf (v : Fin N → ℝ) (θ : ℝ) :
      (∑ T : Finset (Fin N), w T *
        Real.exp (θ * ((∑ i ∈ T, v i) - p * ∑ i, v i))) ≤
        Real.exp (θ ^ 2 * (∑ i, v i ^ 2) / 8) := by
    change (∑ T : Finset (Fin N), p ^ T.card * (1 - p) ^ (N - T.card) *
        Real.exp (θ * ((∑ i ∈ T, v i) - p * ∑ i, v i))) ≤ _
    rw [hMGF N p θ v]
    calc
      _ ≤ ∏ i, Real.exp ((θ * v i) ^ 2 / 8) := by
        apply Finset.prod_le_prod₀
        · intro i _
          exact add_nonneg (mul_nonneg hp (Real.exp_pos _).le)
            (mul_nonneg (sub_nonneg.mpr hp1) (Real.exp_pos _).le)
        · intro i _
          simpa only [mul_assoc] using hTwo p (θ * v i) hp hp1
      _ = Real.exp (∑ i, (θ * v i) ^ 2 / 8) := (Real.exp_sum _ _).symm
      _ = Real.exp (θ ^ 2 * (∑ i, v i ^ 2) / 8) := by
        congr 1
        simp only [mul_pow, Finset.mul_sum, Finset.sum_div]
  have htail (v : Fin N → ℝ) (hv : 0 < ∑ i, v i ^ 2) :
      (∑ T : Finset (Fin N),
        if s ≤ (∑ i ∈ T, v i) - p * ∑ i, v i then w T else 0) ≤
        Real.exp (-2 * s ^ 2 / ∑ i, v i ^ 2) := by
    let V : ℝ := ∑ i, v i ^ 2
    let θ : ℝ := 4 * s / V
    let d : Finset (Fin N) → ℝ := fun T => (∑ i ∈ T, v i) - p * ∑ i, v i
    have hVpos : 0 < V := hv
    have hθ : 0 ≤ θ := by dsimp [θ]; positivity
    have hpoint (T : Finset (Fin N)) :
        (if s ≤ d T then w T else 0) ≤ w T * Real.exp (θ * (d T - s)) := by
      by_cases hT : s ≤ d T
      · rw [if_pos hT]
        have he : 1 ≤ Real.exp (θ * (d T - s)) := by
          simpa only [Real.exp_zero] using
            (Real.exp_le_exp.mpr (mul_nonneg hθ (sub_nonneg.mpr hT)))
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he (hw T)
      · rw [if_neg hT]
        exact mul_nonneg (hw T) (Real.exp_pos _).le
    change (∑ T : Finset (Fin N), if s ≤ d T then w T else 0) ≤
      Real.exp (-2 * s ^ 2 / V)
    calc
      _ ≤ ∑ T : Finset (Fin N), w T * Real.exp (θ * (d T - s)) :=
        Finset.sum_le_sum (fun T _ => hpoint T)
      _ = Real.exp (-θ * s) *
          (∑ T : Finset (Fin N), w T * Real.exp (θ * d T)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T _
        calc
          w T * Real.exp (θ * (d T - s)) =
              w T * Real.exp ((-θ * s) + θ * d T) := by congr 2; ring
          _ = _ := by rw [Real.exp_add]; ring
      _ ≤ Real.exp (-θ * s) * Real.exp (θ ^ 2 * V / 8) :=
        mul_le_mul_of_nonneg_left (hmgf v θ) (Real.exp_pos _).le
      _ = Real.exp (-2 * s ^ 2 / V) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [θ]
        field_simp [hVpos.ne'] <;> ring
  have hplus := htail a hV
  have hminus := htail (fun i => -a i) (by simpa only [neg_sq] using hV)
  have hneg (T : Finset (Fin N)) :
      (∑ i ∈ T, -a i) - p * (∑ i, -a i) =
        -((∑ i ∈ T, a i) - p * ∑ i, a i) := by
    simp only [Finset.sum_neg_distrib]
    ring
  have hnonneg (Q : Prop) (T : Finset (Fin N)) : 0 ≤ (if Q then w T else 0) := by
    split_ifs
    · exact hw T
    · exact le_rfl
  change (∑ T : Finset (Fin N),
      if s ≤ |(∑ i ∈ T, a i) - p * ∑ i, a i| then w T else 0) ≤ _
  calc
    _ ≤ (∑ T : Finset (Fin N),
          if s ≤ (∑ i ∈ T, a i) - p * ∑ i, a i then w T else 0) +
        (∑ T : Finset (Fin N),
          if s ≤ (∑ i ∈ T, -a i) - p * ∑ i, -a i then w T else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro T _
      rw [hneg]
      let d : ℝ := (∑ i ∈ T, a i) - p * ∑ i, a i
      change (if s ≤ |d| then w T else 0) ≤
        (if s ≤ d then w T else 0) + (if s ≤ -d then w T else 0)
      by_cases hT : s ≤ |d|
      · rw [if_pos hT]
        by_cases hd : 0 ≤ d
        · have hsd : s ≤ d := by simpa only [abs_of_nonneg hd] using hT
          rw [if_pos hsd]
          exact le_add_of_nonneg_right (hnonneg _ T)
        · have hsd : s ≤ -d := by
            simpa only [abs_of_neg (lt_of_not_ge hd)] using hT
          rw [if_pos hsd]
          exact le_add_of_nonneg_left (hnonneg _ T)
      · rw [if_neg hT]
        exact add_nonneg (hnonneg _ T) (hnonneg _ T)
    _ ≤ Real.exp (-2 * s ^ 2 / ∑ i, a i ^ 2) +
        Real.exp (-2 * s ^ 2 / ∑ i, a i ^ 2) := by
      exact add_le_add hplus (by simpa only [neg_sq] using hminus)
    _ = 2 * Real.exp (-2 * s ^ 2 / ∑ i, a i ^ 2) := by ring

end
end AronowAudit.P002.Wave1.E61Eigenvalue
