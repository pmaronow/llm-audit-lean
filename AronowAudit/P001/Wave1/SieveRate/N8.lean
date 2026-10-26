import AronowAudit.P001.Wave1.SieveRateBlueprint
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Polynomial

/-! # SieveRate N8: coefficient moments and Vandermonde evaluation -/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n8_proof : N8 := by
  classical
  constructor
  · intro d b r
    have hint (k : Fin (d + 1)) :
        IntegrableOn (fun z : ℝ => b k * (z ^ (k : ℕ) * r.eval z))
          (Set.Icc (0 : ℝ) (1 / 2)) :=
      (continuous_const.mul ((continuous_id.pow (k : ℕ)).mul r.continuous)).integrableOn_Icc
    have hexpand (z : ℝ) :
        (coeffPoly b).eval z * r.eval z =
          ∑ k : Fin (d + 1), b k * (z ^ (k : ℕ) * r.eval z) := by
      simp only [coeffPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_assoc _ _ _
    calc
      regionInt (coeffPoly b) r =
          ∫ z in Set.Icc (0 : ℝ) (1 / 2),
            ∑ k : Fin (d + 1), b k * (z ^ (k : ℕ) * r.eval z) := by
        unfold regionInt
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hexpand
      _ = ∑ k : Fin (d + 1),
          ∫ z in Set.Icc (0 : ℝ) (1 / 2), b k * (z ^ (k : ℕ) * r.eval z) :=
        integral_finsetSum Finset.univ (fun k _ => hint k)
      _ = ∑ k : Fin (d + 1),
          b k * ∫ z in Set.Icc (0 : ℝ) (1 / 2), z ^ (k : ℕ) * r.eval z := by
        apply Finset.sum_congr rfl
        intro k _
        exact integral_const_mul (b k) _
      _ = b ⬝ᵥ regionMoments d r := by
        simp only [dotProduct, regionMoments, regionInt, Polynomial.eval_pow,
          Polynomial.eval_X]
  · intro d n x c i
    simp only [vand, Matrix.mulVec, dotProduct, coeffPoly,
      Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _

end

end AronowAudit.P001.Wave1.SieveRate
