import SAP.P015a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015a.WH.W1.P.T8_L1

open Matrix
open scoped BigOperators

noncomputable section

theorem proofCore : SAP.P015a.WH.W1.T8_L1 := by
  intro n q W f d θ hder
  let row : Fin n → (Fin q → ℝ) →L[ℝ] ℝ := fun i =>
    ∑ j, W i j • ContinuousLinearMap.proj j
  have hrow : ∀ i, HasFDerivAt (fun t : Fin q → ℝ => W.mulVec t i) (row i) θ := by
    intro i
    have hlin : HasFDerivAt (row i) (row i) θ := (row i).hasFDerivAt
    have hfun : (fun t : Fin q → ℝ => W.mulVec t i) = row i := by
      funext t
      simp [row, Matrix.mulVec, dotProduct]
    simpa only [hfun] using hlin
  have hterms : ∀ i, HasFDerivAt (fun t : Fin q → ℝ => f i (W.mulVec t i))
      (d i • row i) θ := by
    intro i
    exact (hder i).comp_hasFDerivAt θ (hrow i)
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (A := fun i t => f i (W.mulVec t i))
    (A' := fun i => d i • row i) (x := θ) (fun i _ => hterms i)
  have hlin : (∑ i, d i • row i) =
      (SAP.P015a.scoreDifferential (W.transpose.mulVec d)) := by
    ext t
    simp only [SAP.P015a.scoreDifferential, row, _root_.sum_apply,
      _root_.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    calc
      (∑ i, d i * ∑ j, W i j * t j) =
          ∑ i, ∑ j, d i * (W i j * t j) := by
        simp only [Finset.mul_sum]
      _ = ∑ j, ∑ i, d i * (W i j * t j) := Finset.sum_comm
      _ = ∑ j, (∑ i, W i j * d i) * t j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  change HasFDerivAt (fun t : Fin q → ℝ => ∑ i, f i (W.mulVec t i))
    (SAP.P015a.scoreDifferential (W.transpose.mulVec d)) θ
  rw [← hlin]
  simpa using hsum

end
end SAP.P015a.WH.W1.P.T8_L1

theorem SAP.P015a.WH.W1.T8_L1_proof : SAP.P015a.WH.W1.T8_L1 :=
  SAP.P015a.WH.W1.P.T8_L1.proofCore
