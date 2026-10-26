import AronowAudit.P002.Wave1.PrintedTheorem2Blueprint
import Mathlib.Logic.Equiv.Fin.Basic

namespace AronowAudit.P002.Wave1.PrintedTheorem2
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Reindex the intercept and sole covariate by `Fin 2` and expand the determinant. -/
theorem n5_proof : N5 := by
  intro n x S hS
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hS)
  have hconst : groupMean S (fun _ => (1 : ℝ)) = 1 := by
    simp [groupMean, hcard]
  have he0 : finSuccEquiv 1 (0 : Fin 2) = none := finSuccEquiv_zero
  have he1 : finSuccEquiv 1 (1 : Fin 2) = some (0 : Fin 1) :=
    finSuccEquiv_succ (0 : Fin 1)
  let G : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.reindex (finSuccEquiv 1).symm (finSuccEquiv 1).symm (gram x S)
  have hdet : G.det = (gram x S).det :=
    Matrix.det_reindex_self (finSuccEquiv 1).symm (gram x S)
  have h00 : G 0 0 = 1 := by
    simpa only [G, Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply,
      he0, gram, augmented, one_mul] using hconst
  have h01 : G 0 1 = groupMean S (fun i => x i 0) := by
    simp only [G, Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply,
      he0, he1, gram, augmented, one_mul]
  have h10 : G 1 0 = groupMean S (fun i => x i 0) := by
    simp only [G, Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply,
      he0, he1, gram, augmented, mul_one]
  have h11 : G 1 1 = groupMean S (fun i => x i 0 ^ 2) := by
    simp only [G, Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply,
      he1, gram, augmented, pow_two]
  rw [← hdet, Matrix.det_fin_two, h00, h01, h10, h11, one_mul, pow_two]

end
end AronowAudit.P002.Wave1.PrintedTheorem2
