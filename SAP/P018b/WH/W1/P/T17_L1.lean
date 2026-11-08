import SAP.P018b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable section

namespace SAP.P018b.WH.W1.P.T17_L1

open SAP.P018b
open Matrix
open scoped BigOperators

def overlapExplicit : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1,1,1,1,1,0;
    1,1,1,1,0,1;
    1,1,1,0,1,1;
    1,1,0,1,1,1;
    1,0,1,1,1,1;
    0,1,1,1,1,1]

def eigenbasis : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1,1,0,0,1,1;
    1,0,1,0,-1,0;
    1,0,0,1,0,-1;
    1,0,0,-1,0,-1;
    1,0,-1,0,-1,0;
    1,-1,0,0,1,1]

def eigenbasisInv : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1/6,1/6,1/6,1/6,1/6,1/6;
    1/2,0,0,0,0,-1/2;
    0,1/2,0,0,-1/2,0;
    0,0,1/2,-1/2,0,0;
    1/6,-1/3,1/6,1/6,-1/3,1/6;
    1/6,1/6,-1/3,-1/3,1/6,1/6]

def eigenvalues : Fin 6 → ℝ := ![5,1,1,1,-1,-1]

def eigenbasisUnit : (Matrix (Fin 6) (Fin 6) ℝ)ˣ :=
  ⟨eigenbasis, eigenbasisInv,
    by ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [eigenbasis, eigenbasisInv, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_succ],
    by ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [eigenbasis, eigenbasisInv, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_succ]⟩

theorem overlap_eq_explicit : wholeOverlap4 = overlapExplicit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [wholeOverlap4, overlapExplicit, sixMembers]

theorem eigenbasis_diagonalizes :
    wholeOverlap4 * eigenbasis = eigenbasis * diagonal eigenvalues := by
  rw [overlap_eq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [overlapExplicit, eigenbasis, eigenvalues, Matrix.mul_apply,
      Matrix.diagonal_apply, Fin.sum_univ_succ]

theorem overlap_conjugate :
    wholeOverlap4 = eigenbasisUnit.val * diagonal eigenvalues * eigenbasisUnit.val⁻¹ := by
  have hPQ : eigenbasis * eigenbasisInv = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [eigenbasis, eigenbasisInv, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_succ]
  have hQP : eigenbasisInv * eigenbasis = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [eigenbasis, eigenbasisInv, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_succ]
  have hInv : eigenbasis⁻¹ = eigenbasisInv := Matrix.inv_eq_left_inv hQP
  have hfactor : wholeOverlap4 = eigenbasis * diagonal eigenvalues * eigenbasisInv := by
    calc
      wholeOverlap4 = wholeOverlap4 * (eigenbasis * eigenbasisInv) := by rw [hPQ]; simp
      _ = (wholeOverlap4 * eigenbasis) * eigenbasisInv := by rw [Matrix.mul_assoc]
      _ = (eigenbasis * diagonal eigenvalues) * eigenbasisInv := by rw [eigenbasis_diagonalizes]
      _ = eigenbasis * diagonal eigenvalues * eigenbasisInv := rfl
  rw [show (eigenbasisUnit.val : Matrix (Fin 6) (Fin 6) ℝ) = eigenbasis from rfl,
    hInv]
  exact hfactor

end SAP.P018b.WH.W1.P.T17_L1

open SAP.P018b
open SAP.P018b.WH.W1.P.T17_L1
open Matrix

theorem SAP.P018b.WH.W1.T17_L1_proof : SAP.P018b.WH.W1.T17_L1 := by
  change wholeOverlap4.charpoly = _
  rw [show wholeOverlap4 =
      eigenbasisUnit.val * Matrix.diagonal eigenvalues * eigenbasisUnit.val⁻¹ from overlap_conjugate]
  rw [Matrix.charpoly_units_conj]
  rw [Matrix.charpoly_diagonal]
  norm_num [eigenvalues, Fin.prod_univ_succ]
  ring
