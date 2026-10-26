import AronowAudit.P001.Wave1.SieveRateBlueprint
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Support

/-!
# SieveRate N6: every full-rank least-squares polynomial is OLS

The normal-equation/Pythagoras argument is given by
`AronowAudit.P001.ols_correct_rows_solution_residuals`. Its coefficient criterion is
identified with the exact range-indexed polynomial criterion.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n6_proof : N6 := by
  classical
  intro hN5 n d x y p hdn hinj hpdeg hmin
  let xf : Fin n → ℝ := fun i => x i
  let yf : Fin n → ℝ := fun i => y i
  let P : Matrix (Fin n) (Fin (d + 1)) ℝ := vand d xf
  let b : Fin (d + 1) → ℝ := fun k => p.coeff (k : ℕ)

  have hunit : IsUnit (P.transpose * P).det := hN5 n d xf hdn hinj
  have hinter : ∀ i : Fin n, P i 0 = 1 := by
    intro i
    simp only [P, vand, Fin.val_zero, pow_zero]
  have hOLS : ∀ a : Fin (d + 1) → ℝ,
      olsRSS P yf (olsCoef P yf) ≤ olsRSS P yf a ∧
        (olsRSS P yf a = olsRSS P yf (olsCoef P yf) ↔ a = olsCoef P yf) :=
    (ols_correct_rows_solution_residuals P yf hunit hinter).1

  -- Coefficient vectors give feasible competitors, including the OLS vector.
  have hdegree (a : Fin (d + 1) → ℝ) : (coeffPoly a).natDegree ≤ d := by
    unfold coeffPoly
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro k _
    exact (Polynomial.natDegree_C_mul_X_pow_le (a k) (k : ℕ)).trans
      (Nat.le_of_lt_succ k.isLt)

  -- A degree-bounded polynomial is exactly its first d+1 coefficients.
  have hp : p = coeffPoly b := by
    change p = ∑ k : Fin (d + 1), C (p.coeff (k : ℕ)) * X ^ (k : ℕ)
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ => C (p.coeff k) * X ^ k) (d + 1)]
    exact p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hpdeg)

  have heval (a : Fin (d + 1) → ℝ) (i : Fin n) :
      P.mulVec a i = (coeffPoly a).eval (x i) := by
    simp only [P, xf, vand, Matrix.mulVec, dotProduct, coeffPoly,
      Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _

  have hcriterion (a : Fin (d + 1) → ℝ) :
      olsRSS P yf a =
        ∑ i ∈ Finset.range n, (y i - (coeffPoly a).eval (x i)) ^ 2 := by
    unfold olsRSS
    simp_rw [heval]
    change (∑ i : Fin n, (y i - (coeffPoly a).eval (x i)) ^ 2) = _
    exact Fin.sum_univ_eq_sum_range
      (fun i : ℕ => (y i - (coeffPoly a).eval (x i)) ^ 2) n

  have hreverse : olsRSS P yf b ≤ olsRSS P yf (olsCoef P yf) := by
    rw [hcriterion b, hcriterion (olsCoef P yf), ← hp]
    exact hmin (coeffPoly (olsCoef P yf)) (hdegree (olsCoef P yf))
  have hb : b = olsCoef P yf :=
    (hOLS b).2.mp (le_antisymm hreverse (hOLS b).1)
  calc
    p = coeffPoly b := hp
    _ = coeffPoly (olsCoef P yf) := congrArg (fun a : Fin (d + 1) → ℝ => coeffPoly a) hb
    _ = olsPoly d (fun i : Fin n => x i) (fun i : Fin n => y i) := rfl

end

end AronowAudit.P001.Wave1.SieveRate
