import SAP.P005a.WH.W2.Leaves
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W2.P.T9_L2

noncomputable section

open Finset
open scoped BigOperators Matrix

private lemma quadratic_diagonal_conjugate (k : ℕ)
    (U : Matrix (Fin k) (Fin k) ℝ) (d : Fin k → ℝ) (v : Fin k → ℝ) :
    SAP.P005a.WH.W2.quadratic (U * Matrix.diagonal d * Uᵀ) v =
      ∑ i, ((Uᵀ *ᵥ v) i)^2 * d i := by
  let x : Fin k → ℝ := Uᵀ *ᵥ v
  change SAP.P005a.dot v ((U * Matrix.diagonal d * Uᵀ) *ᵥ v) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change SAP.P005a.dot v (U *ᵥ (Matrix.diagonal d *ᵥ x)) = _
  calc
    SAP.P005a.dot v (U *ᵥ (Matrix.diagonal d *ᵥ x)) =
        SAP.P005a.dot (Matrix.diagonal d *ᵥ x) (Uᵀ *ᵥ v) := by
          change dotProduct v (U *ᵥ (Matrix.diagonal d *ᵥ x)) = _
          exact Matrix.dotProduct_transpose_mulVec Uᵀ v (Matrix.diagonal d *ᵥ x)
    _ = SAP.P005a.dot x (Matrix.diagonal d *ᵥ x) := by
          unfold SAP.P005a.dot
          change dotProduct (Matrix.diagonal d *ᵥ x) x = _
          exact dotProduct_comm _ _
    _ = ∑ i, x i ^ 2 * d i := by
          unfold SAP.P005a.dot
          apply Finset.sum_congr rfl
          intro i hi
          rw [Matrix.mulVec_diagonal]
          ring

private lemma unitary_coordinates_unit (k : ℕ)
    (U : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ)
    (hU : U * Uᵀ = 1) (hv : SAP.P005a.WH.W2.unitVector v) :
    ∑ i, ((Uᵀ *ᵥ v) i)^2 = 1 := by
  have hmul : U *ᵥ (Uᵀ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  have hdot : SAP.P005a.dot (Uᵀ *ᵥ v) (Uᵀ *ᵥ v) =
      SAP.P005a.dot v v := by
    calc
      SAP.P005a.dot (Uᵀ *ᵥ v) (Uᵀ *ᵥ v) =
          SAP.P005a.dot v (U *ᵥ (Uᵀ *ᵥ v)) := by
            change dotProduct (Uᵀ *ᵥ v) (Uᵀ *ᵥ v) = _
            exact Matrix.dotProduct_transpose_mulVec U (Uᵀ *ᵥ v) v
      _ = SAP.P005a.dot v v := by rw [hmul]

  simpa [SAP.P005a.dot, sq] using hdot.trans hv

end

end SAP.P005a.WH.W2.P.T9_L2

open SAP.P005a.WH.W2.P.T9_L2

noncomputable section

open Finset
open scoped BigOperators Matrix

theorem SAP.P005a.WH.W2.T9_L2_proof : SAP.P005a.WH.W2.T9_L2 := by
  intro k A hA v hv
  let U : Matrix (Fin k) (Fin k) ℝ := hA.eigenvectorUnitary
  let eig : Fin k → ℝ := hA.eigenvalues
  have hspec : A = U * Matrix.diagonal eig * Uᵀ := by
    simpa [U, eig, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using
        hA.spectral_theorem
  have hUtU : Uᵀ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
        Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUUt : U * Uᵀ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
        Unitary.coe_mul_star_self hA.eigenvectorUnitary
  let x : Fin k → ℝ := Uᵀ *ᵥ v
  have hx : ∑ i, x i ^ 2 = 1 := by
    simpa [x, sq] using unitary_coordinates_unit k U v hUUt hv
  have hunit : IsUnit U := by
    apply (isUnit_iff_exists).2
    exact ⟨Uᵀ, hUUt, hUtU⟩
  have hexp : NormedSpace.exp A = U * Matrix.diagonal (fun i => Real.exp (eig i)) * Uᵀ := by
    rw [hspec]
    have hc := Matrix.exp_conj U (Matrix.diagonal eig) hunit
    have hinv : U⁻¹ = Uᵀ := by
      calc
        U⁻¹ = U⁻¹ * (U * Uᵀ) := by rw [hUUt, mul_one]
        _ = (U⁻¹ * U) * Uᵀ := by rw [mul_assoc]
        _ = Uᵀ := by
          have hdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
          have hinv_mul : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U hdet
          rw [hinv_mul, one_mul]
    rw [hinv] at hc
    rw [hc, Matrix.exp_diagonal]
    rw [Pi.exp_def]
    apply congrArg (fun f : Fin k → ℝ => U * Matrix.diagonal f * Uᵀ)
    funext i
    exact congrFun Real.exp_eq_exp_ℝ.symm (eig i)
  have hquadA : SAP.P005a.WH.W2.quadratic A v = ∑ i, x i ^ 2 * eig i := by
    rw [hspec]
    simpa [x, sq] using quadratic_diagonal_conjugate k U eig v
  have hquadExp : SAP.P005a.WH.W2.quadratic (NormedSpace.exp A) v =
      ∑ i, x i ^ 2 * Real.exp (eig i) := by
    rw [hexp]
    simpa [x, sq] using quadratic_diagonal_conjugate k U (fun i => Real.exp (eig i)) v
  have hw : ∀ i, 0 ≤ x i ^ 2 := fun i => sq_nonneg (x i)
  have hj := convexOn_exp.map_sum_le (t := Finset.univ) (fun i _ => hw i) hx (fun i _ => Set.mem_univ (eig i))
  have hj' : Real.exp (∑ i, x i ^ 2 * eig i) ≤
      ∑ i, x i ^ 2 * Real.exp (eig i) := by
    simpa [smul_eq_mul] using hj
  rw [hquadA, hquadExp]
  exact hj'
