import AronowAudit.P001.Wave1.SieveRateBlueprint
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # SieveRate N9: Cauchy–Schwarz for an invertible Gram matrix -/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n9_proof : N9 := by
  classical
  intro n K P hP c w
  let A : Matrix (Fin K) (Fin K) ℝ := P.transpose * P
  let u : Fin K → ℝ := A⁻¹.mulVec w
  have hAu : A.mulVec u = w := by
    dsimp only [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hP, Matrix.one_mulVec]
  have hnormal : P.transpose.mulVec (P.mulVec u) = w := by
    rw [Matrix.mulVec_mulVec]
    exact hAu
  have hcross : c ⬝ᵥ w = (P.mulVec c) ⬝ᵥ (P.mulVec u) := by
    calc
      c ⬝ᵥ w = c ⬝ᵥ (P.transpose.mulVec (P.mulVec u)) :=
        congrArg (fun v : Fin K → ℝ => c ⬝ᵥ v) hnormal.symm
      _ = (P.mulVec c) ⬝ᵥ (P.mulVec u) := by
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hquad : w ⬝ᵥ A⁻¹.mulVec w = ∑ i, (P.mulVec u i) ^ 2 := by
    calc
      w ⬝ᵥ A⁻¹.mulVec w = u ⬝ᵥ w := by
        change w ⬝ᵥ u = u ⬝ᵥ w
        exact dotProduct_comm _ _
      _ = u ⬝ᵥ A.mulVec u := by rw [hAu]
      _ = ∑ i, (P.mulVec u i) ^ 2 := gram_quadratic_form P u
  have hCS :
      ((P.mulVec c) ⬝ᵥ (P.mulVec u)) ^ 2 ≤
        (∑ i, (P.mulVec c i) ^ 2) * ∑ i, (P.mulVec u i) ^ 2 := by
    simpa only [dotProduct] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (P.mulVec c) (P.mulVec u))
  change (c ⬝ᵥ w) ^ 2 ≤ (∑ i, (P.mulVec c i) ^ 2) * (w ⬝ᵥ A⁻¹.mulVec w)
  rw [hcross, hquad]
  exact hCS

end

end AronowAudit.P001.Wave1.SieveRate
