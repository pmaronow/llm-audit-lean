import SAP.P037a.WH.W1.Leaves
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W1.P.T4_L6

open SAP.P037a
open scoped BigOperators Classical

lemma gram_eq_transpose_diagonal_mul {I K : Type*} [Fintype I]
    (w : I → ℝ) (X : Matrix I K ℝ) :
    gramWeighted w X = Matrix.transpose X * Matrix.diagonal w * X := by
  classical
  ext k l
  simp [gramWeighted, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma wls_iff_normal {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq K] (w : I → ℝ) (X : Matrix I K ℝ) (y : I → ℝ) (b : K → ℝ) :
    WLS w X y b ↔ (gramWeighted w X).mulVec b = rhsWeighted w X y := by
  classical
  have hcoord (k : K) :
      (∑ i, w i * X i k * (y i - ∑ l, X i l * b l)) =
        rhsWeighted w X y k - (gramWeighted w X).mulVec b k := by
    simp [rhsWeighted, gramWeighted, Matrix.mulVec, dotProduct,
      Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib, mul_sub,
      mul_assoc, mul_left_comm, mul_comm]
    conv_rhs => rw [Finset.sum_comm]
  constructor
  · intro h
    ext k
    have hk := hcoord k
    rw [h k] at hk
    linarith
  · intro h k
    have hk := hcoord k
    have heq := congrFun h k
    rw [heq] at hk
    simp at hk
    exact hk

end SAP.P037a.WH.W1.P.T4_L6

open SAP.P037a.WH.W1.P.T4_L6

theorem SAP.P037a.WH.W1.T4_L6_proof : SAP.P037a.WH.W1.T4_L6 := by
  classical
  change SAP.P037a.wlsRegularity
  intro I K instI instK instDec w X y hw hX
  let G := gramWeighted w X
  have hdiag : (Matrix.diagonal w : Matrix I I ℝ).PosDef := by
    exact Matrix.PosDef.diagonal hw
  have hposFactor : (Matrix.transpose X * Matrix.diagonal w * X).PosDef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hdiag.conjTranspose_mul_mul_same hX)
  have hpos : G.PosDef := by
    change (gramWeighted w X).PosDef
    rw [gram_eq_transpose_diagonal_mul]
    exact hposFactor
  have hunit : IsUnit G.det := by
    exact (Matrix.isUnit_iff_isUnit_det G).mp hpos.isUnit
  have hdet : G.det ≠ 0 := hunit.ne_zero
  have hGunit : IsUnit G := hpos.isUnit
  have hinj : Function.Injective G.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hGunit
  have hnormal : G.mulVec (wlsCoefficient w X y) = rhsWeighted w X y := by
    change G.mulVec (G⁻¹.mulVec (rhsWeighted w X y)) = rhsWeighted w X y
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
  refine ⟨hdet, (wls_iff_normal w X y (wlsCoefficient w X y)).mpr ?_, ?_⟩
  · simpa [G] using hnormal
  · intro b hb
    have hbnormal : G.mulVec b = rhsWeighted w X y :=
      (wls_iff_normal w X y b).mp hb
    apply hinj
    rw [hbnormal, hnormal]
