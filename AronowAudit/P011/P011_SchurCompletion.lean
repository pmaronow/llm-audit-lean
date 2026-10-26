import AronowAudit.P011.P011_DenseInfrastructure

namespace AronowAudit.P011.SchurSupport
open scoped BigOperators Matrix
open DenseCompletion
noncomputable section

/-- The absolute row-sum Schur estimate for a symmetric real matrix, in the
Euclidean operator norm. -/
theorem operatorNorm_le_abs_row_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, M i j = M j i) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ i, (∑ j, |M i j|) ≤ C) : operatorNorm M ≤ C := by
  have hcol (j : Fin n) : (∑ i, |M i j|) ≤ C := by
    calc
      _ = ∑ i, |M j i| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hM i j]
      _ ≤ C := hrow j
  have hx (x : Fin n → ℝ) : l2 (M *ᵥ x) ≤ C * l2 x := by
    have hi (i : Fin n) : (M *ᵥ x) i ^ 2 ≤ C * ∑ j, |M i j| * x j ^ 2 := by
      have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
        (r := fun j => M i j * x j) (f := fun j => |M i j|)
        (g := fun j => |M i j| * x j ^ 2)
        (fun j _ => abs_nonneg (M i j))
        (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
        (fun j _ => by rw [mul_pow, ←mul_assoc, ←pow_two, sq_abs])
      exact hh.trans (mul_le_mul_of_nonneg_right (hrow i)
        (Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))))
    have hs : (∑ i, (M *ᵥ x) i ^ 2) ≤ C ^ 2 * ∑ j, x j ^ 2 := by
      calc
        _ ≤ ∑ i, C * ∑ j, |M i j| * x j ^ 2 := Finset.sum_le_sum (fun i _ => hi i)
        _ = C * ∑ j, (∑ i, |M i j|) * x j ^ 2 := by
          rw [←Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_mul]
        _ ≤ C * ∑ j, C * x j ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
        _ = _ := by rw [←Finset.mul_sum]; ring
    apply (sq_le_sq₀ (l2_nonneg _) (mul_nonneg hC (l2_nonneg _))).mp
    simpa only [l2_sq, mul_pow] using hs
  change ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖ ≤ C
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have hxnorm : l2 (WithLp.ofLp x) = ‖x‖ := by
    rw [←l2_norm]
  have he : (Matrix.toEuclideanLin M).toContinuousLinearMap x =
      WithLp.toLp 2 (M *ᵥ WithLp.ofLp x) := by
    have hxx : x = WithLp.toLp 2 (WithLp.ofLp x) := by simp
    rw [hxx]
    simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin,
      Matrix.toLpLin_toLp, Matrix.toLin'_apply]
  rw [he, l2_norm]
  simpa only [hxnorm] using hx (WithLp.ofLp x)

end
end AronowAudit.P011.SchurSupport
