import SAP.P026a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P026a.WH.W2.P.T7_L2

open SAP.P026a
open SAP.P026a.WH.W2
open Finset
open scoped BigOperators

def rawGram (t u v : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  fun i j => match i.val, j.val with
    | 0, 0 => 16 | 0, 1 => t | 0, 2 => 10 | 0, 3 => 43
    | 1, 0 => t | 1, 1 => t | 1, 2 => u | 1, 3 => v
    | 2, 0 => 10 | 2, 1 => u | 2, 2 => 10 | 2, 3 => 28
    | 3, 0 => 43 | 3, 1 => v | 3, 2 => 28 | 3, 3 => 149
    | _, _ => 0

theorem rawGram_det (t u v : ℚ) :
    (rawGram t u v).det =
      60 * ((t - (t-u)^2/6 - u^2/10) * (331/10) -
        (v - (15/6)*(t-u) - (28/10)*u)^2) := by
  norm_num [rawGram, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.det_fin_two, Matrix.submatrix, Fin.sum_univ_succ, Fin.succAbove]
  ring

def totalT (w : W2Allocation) : ℚ := ∑ i, w2Treatment w i

def block2T (w : W2Allocation) : ℚ :=
  ∑ i, w2Treatment w i * (if 6 ≤ i.val then 1 else 0)

def tx (w : W2Allocation) : ℚ := ∑ i, w2Treatment w i * paperTableX i

theorem treatment_sq (w : W2Allocation) (i : Fin 16) :
    w2Treatment w i * w2Treatment w i = w2Treatment w i := by
  simp [w2Treatment, armIndicator]

theorem block2T_symm (w : W2Allocation) :
    (∑ i, (if 6 ≤ i.val then 1 else 0) * w2Treatment w i) = block2T w := by
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem tx_symm (w : W2Allocation) :
    (∑ i, paperTableX i * w2Treatment w i) = tx w := by
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem tx_direct (w : W2Allocation) :
    (∑ i, w2Treatment w i * paperTableX i) = tx w := rfl

theorem gram_eq (w : W2Allocation) :
    w2Gram (w2FeCovDesign w) (fun _ => 1) =
      rawGram (totalT w) (block2T w) (tx w) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp only [w2Gram, w2FeCovDesign, rawGram]
  all_goals
    norm_num [totalT, block2T, tx, paperTableX, Fin.sum_univ_succ,
      treatment_sq, block2T_symm] <;> first | decide +kernel | ring

theorem det_formula (w : W2Allocation) :
    (w2Gram (w2FeCovDesign w) (fun _ => 1)).det =
      60 * ((totalT w - (totalT w - block2T w)^2/6 - (block2T w)^2/10) *
        (331/10) -
        (tx w - (15/6)*(totalT w - block2T w) - (28/10)*block2T w)^2) := by
  rw [gram_eq, rawGram_det]

end SAP.P026a.WH.W2.P.T7_L2

theorem SAP.P026a.WH.W2.T7_L2_proof : SAP.P026a.WH.W2.T7_L2 := by
  classical
  intro w
  rw [SAP.P026a.WH.W2.P.T7_L2.det_formula]
  rcases w with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> decide +kernel
