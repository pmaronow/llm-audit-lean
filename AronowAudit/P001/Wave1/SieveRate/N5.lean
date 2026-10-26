import AronowAudit.P001.Wave1.SieveRateBlueprint
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Distinct designs give an injective polynomial evaluation map and a positive definite Gram matrix.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n5_proof : N5 := by
  classical
  intro n d x hdn hx
  have hdegree (c : Fin (d + 1) → ℝ) : (coeffPoly c).natDegree ≤ d := by
    unfold coeffPoly
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    exact (Polynomial.natDegree_C_mul_X_pow_le (c k) (k : ℕ)).trans
      (Nat.le_of_lt_succ k.isLt)
  have hcoeff (c : Fin (d + 1) → ℝ) (k : Fin (d + 1)) :
      (coeffPoly c).coeff (k : ℕ) = c k := by
    unfold coeffPoly
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single k]
    · simp [Polynomial.coeff_C_mul_X_pow]
    · intro j _ hjk
      have hkj : (k : ℕ) ≠ (j : ℕ) := by
        intro h
        exact hjk (Fin.ext h.symm)
      simp only [Polynomial.coeff_C_mul_X_pow, if_neg hkj]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim
  have heval (c : Fin (d + 1) → ℝ) (i : Fin n) :
      (coeffPoly c).eval (x i) = (vand d x).mulVec c i := by
    simp only [coeffPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Matrix.mulVec, dotProduct, vand, Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hkernel (c : Fin (d + 1) → ℝ) (hc : (vand d x).mulVec c = 0) : c = 0 := by
    have hz : ∀ i : Fin n, (coeffPoly c).eval (x i) = 0 := by
      intro i
      rw [heval]
      exact congrFun hc i
    have hcard : (coeffPoly c).natDegree < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      exact lt_of_le_of_lt (hdegree c) (by omega)
    have hp : coeffPoly c = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (coeffPoly c) hx hz hcard
    funext k
    have hk := congrArg (fun p : Polynomial ℝ => p.coeff (k : ℕ)) hp
    simpa only [hcoeff, Polynomial.coeff_zero, Pi.zero_apply] using hk
  have hpos : ((vand d x).transpose * vand d x).PosDef := by
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    refine ⟨?_, ?_⟩
    · have he : (vand d x).conjTranspose = (vand d x).transpose := by
        ext i j
        simp
      simpa only [he] using (Matrix.posSemidef_conjTranspose_mul_self (vand d x)).isHermitian
    · intro c hc
      have hPc : (vand d x).mulVec c ≠ 0 := by
        intro h
        exact hc (hkernel c h)
      have hex : ∃ i : Fin n, (vand d x).mulVec c i ≠ 0 := by
        by_contra h
        push_neg at h
        exact hPc (funext h)
      obtain ⟨i, hi⟩ := hex
      have hsum : 0 < ∑ j : Fin n, ((vand d x).mulVec c j) ^ 2 :=
        lt_of_lt_of_le (sq_pos_of_ne_zero hi)
          (Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i))
      simpa only [star_trivial, gram_quadratic_form] using hsum
  exact (Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit

end

end AronowAudit.P001.Wave1.SieveRate
