import SAP.P018b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b.WH.W1.P.T17_L2
open Finset Matrix
open scoped BigOperators Matrix.Norms.Elementwise

private theorem intercept_gram :
    sampleGram (wholeInterceptX (Fin 6)) = !![(6 : ℝ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sampleGram, outer, wholeInterceptX, Fin.sum_univ_succ]

private theorem intercept_inverse :
    (sampleGram (wholeInterceptX (Fin 6)))⁻¹ = !![(1/6 : ℝ)] := by
  rw [intercept_gram]
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j
  norm_num [Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply,
    Fin.sum_univ_succ]

private theorem cycle_sum : (∑ d : Fin 6, wholeCycle d) = 0 := by
  norm_num [wholeCycle, Fin.sum_univ_succ]

private theorem intercept_ols :
    sampleOLS (wholeInterceptX (Fin 6)) wholeCycle = 0 := by
  rw [sampleOLS, intercept_inverse]
  ext i
  fin_cases i
  norm_num [Matrix.mulVec, dotProduct, wholeInterceptX, score, wholeCycle,
    Fin.sum_univ_succ]

private theorem intercept_residual (d : Fin 6) :
    fittedResidual (wholeInterceptX (Fin 6)) wholeCycle d = wholeCycle d := by
  rw [fittedResidual, intercept_ols]
  simp [dot, wholeInterceptX]

private theorem cycle_meat :
    meat sixMembers (fun d => score (wholeInterceptX (Fin 6) d)
      (fittedResidual (wholeInterceptX (Fin 6)) wholeCycle d)) = !![(-4 : ℝ)] := by
  have hr : (fun d => score (wholeInterceptX (Fin 6) d)
      (fittedResidual (wholeInterceptX (Fin 6)) wholeCycle d)) =
      (fun d => score (wholeInterceptX (Fin 6) d) (wholeCycle d)) := by
    funext d
    rw [intercept_residual]
  rw [hr]
  ext i j
  fin_cases i <;> fin_cases j
  norm_num [meat, score, outer, wholeInterceptX, wholeCycle, sixMembers,
    Fin.sum_univ_succ]

end SAP.P018b.WH.W1.P.T17_L2

theorem SAP.P018b.WH.W1.T17_L2_proof : SAP.P018b.WH.W1.T17_L2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [SAP.P018b.WH.W1.P.T17_L2.intercept_gram]
    norm_num [Matrix.det_fin_one]
  · exact SAP.P018b.WH.W1.P.T17_L2.intercept_ols
  · intro d
    exact SAP.P018b.WH.W1.P.T17_L2.intercept_residual d
  · rw [sampleVariance, SAP.P018b.WH.W1.P.T17_L2.intercept_inverse,
      SAP.P018b.WH.W1.P.T17_L2.cycle_meat]
    norm_num [sandwich, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
      Fin.sum_univ_succ]
