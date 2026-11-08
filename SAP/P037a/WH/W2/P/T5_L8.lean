import SAP.P037a.WH.W2.Leaves
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W2.P.T5_L8

open SAP.P037a
open scoped BigOperators

theorem gram_mulVec_eq {I K : Type} [Fintype I] [Fintype K]
    (w : I → ℝ) (X : Matrix I K ℝ) (b : K → ℝ) (k : K) :
    (gramWeighted w X).mulVec b k =
      ∑ i, w i * X i k * ∑ l, X i l * b l := by
  classical
  simp only [Matrix.mulVec_apply_eq_sum, gramWeighted]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    ∑ l, (w i * X i k * X i l) * b l =
        ∑ l, (w i * X i k) * (X i l * b l) := by
          apply Finset.sum_congr rfl
          intro l hl
          ring
    _ = (w i * X i k) * ∑ l, X i l * b l := by rw [Finset.mul_sum]

theorem gram_eq_congruence {I K : Type} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K]
    (w : I → ℝ) (X : Matrix I K ℝ) :
    gramWeighted w X = Matrix.conjTranspose X * Matrix.diagonal w * X := by
  classical
  ext k l
  simp [gramWeighted, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm, mul_left_comm]

theorem wls_iff_normal {I K : Type} [Fintype I] [Fintype K]
    (w : I → ℝ) (X : Matrix I K ℝ) (y : I → ℝ) (b : K → ℝ) :
    WLS w X y b ↔ (gramWeighted w X).mulVec b = rhsWeighted w X y := by
  constructor
  · intro h
    ext k
    have hk := h k
    have hcoord : rhsWeighted w X y k - (gramWeighted w X).mulVec b k =
        ∑ i, w i * X i k * (y i - ∑ l, X i l * b l) := by
      rw [gram_mulVec_eq, rhsWeighted]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    linarith
  · intro h k
    have hk := congrFun h k
    have hcoord : rhsWeighted w X y k - (gramWeighted w X).mulVec b k =
        ∑ i, w i * X i k * (y i - ∑ l, X i l * b l) := by
      rw [gram_mulVec_eq, rhsWeighted]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hk] at hcoord
    simpa using hcoord.symm

end SAP.P037a.WH.W2.P.T5_L8

theorem SAP.P037a.WH.W2.T5_L8_proof : SAP.P037a.WH.W2.T5_L8 := by
  classical
  intro I K _ _ _ w X y hw hX
  let G : Matrix K K ℝ := gramWeighted w X
  have hD : (Matrix.diagonal w : Matrix I I ℝ).PosDef :=
    Matrix.posDef_diagonal_iff.mpr hw
  have hGpos : G.PosDef := by
    rw [show G = Matrix.conjTranspose X * Matrix.diagonal w * X by
      dsimp [G]; exact SAP.P037a.WH.W2.P.T5_L8.gram_eq_congruence w X]
    exact hD.conjTranspose_mul_mul_same hX
  have hdet : IsUnit G.det := by
    exact (Matrix.isUnit_iff_isUnit_det G).mp hGpos.isUnit
  have hdet' : IsUnit (gramWeighted w X).det := by
    simpa [G] using hdet
  have hinjG : Function.Injective G.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hGpos.isUnit
  have hcoeff : G.mulVec (wlsCoefficient w X y) = rhsWeighted w X y := by
    change G.mulVec (G⁻¹.mulVec (rhsWeighted w X y)) = rhsWeighted w X y
    calc
      G.mulVec (G⁻¹.mulVec (rhsWeighted w X y)) =
          (G * G⁻¹).mulVec (rhsWeighted w X y) := by rw [Matrix.mulVec_mulVec]
      _ = (1 : Matrix K K ℝ).mulVec (rhsWeighted w X y) := by
        rw [Matrix.mul_nonsing_inv G hdet]
      _ = rhsWeighted w X y := Matrix.one_mulVec _
  refine ⟨hdet', ?_, ?_⟩
  · apply (SAP.P037a.WH.W2.P.T5_L8.wls_iff_normal w X y
      (wlsCoefficient w X y)).2
    simpa [G] using hcoeff
  · intro b hb
    have hb' := (SAP.P037a.WH.W2.P.T5_L8.wls_iff_normal w X y b).1 hb
    apply hinjG
    calc
      G.mulVec b = rhsWeighted w X y := by simpa [G] using hb'
      _ = G.mulVec (wlsCoefficient w X y) := hcoeff.symm
