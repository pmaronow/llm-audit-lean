import SAP.P041.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators

namespace SAP.P041.WH.W1.P.T9_L3

lemma arm_sum_split {n : ℕ} (treated : Fin n → Bool) (Y : Fin n → ℝ) :
    ArmTotalW1 treated true Y + ArmTotalW1 treated false Y = ∑ i, Y i := by
  classical
  unfold ArmTotalW1
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
    (fun i => treated i = true) Y]
  simp

lemma treated_indicator_sum {n : ℕ} (treated : Fin n → Bool)
    (hT : (Finset.univ.filter (fun i => treated i = true)).card = 75) :
    (∑ i : Fin n, if treated i then (1 : ℝ) else 0) = 75 := by
  classical
  rw [Finset.sum_boole]
  exact_mod_cast hT

lemma treated_indicator_nested_sum {n : ℕ} (treated : Fin n → Bool)
    (hT : (Finset.univ.filter (fun i => treated i = true)).card = 75) :
    (∑ i : Fin n, if treated i = true then
      (if treated i = true then (1 : ℝ) else 0) else 0) = 75 := by
  calc
    _ = ∑ i : Fin n, if treated i = true then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : treated i = true <;> simp [h]
    _ = 75 := by simpa using treated_indicator_sum treated hT

lemma treated_conditional_sum {n : ℕ} (treated : Fin n → Bool) (Y : Fin n → ℝ) :
    (∑ i : Fin n, if treated i = true then Y i else 0) =
      ArmTotalW1 treated true Y := by
  classical
  unfold ArmTotalW1
  rw [Finset.sum_filter]

end SAP.P041.WH.W1.P.T9_L3

theorem SAP.P041.WH.W1.T9_L3_proof : SAP.P041.WH.W1.T9_L3 := by
  classical
  intro n treated Y hT hF
  have hn : n = 151 := by
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => treated i = true)
    have hnot : (Finset.univ.filter (fun i : Fin n => ¬ treated i = true)).card = 76 := by
      simpa using hF
    have hsum : 75 + 76 = n := by
      rw [hT, hnot] at hc
      simpa [Finset.card_univ, Fintype.card_fin] using hc
    omega
  have hTsum := SAP.P041.WH.W1.P.T9_L3.treated_indicator_sum treated hT
  have hTnested := SAP.P041.WH.W1.P.T9_L3.treated_indicator_nested_sum treated hT
  have hXgram : (FormerRowsW1 treated).transpose * FormerRowsW1 treated =
      (!![151,75;75,75] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext j l
    fin_cases j <;> fin_cases l <;>
      simp [Matrix.mul_apply, Matrix.transpose_apply, FormerRowsW1,
        hn, hTsum, hTnested]
  have hfit : (FormerRowsW1 treated).transpose *ᵥ Y =
      ![ArmTotalW1 treated true Y + ArmTotalW1 treated false Y,
        ArmTotalW1 treated true Y] := by
    ext j
    fin_cases j
    · simp [Matrix.mulVec, Matrix.transpose_apply, dotProduct, FormerRowsW1,
        SAP.P041.WH.W1.P.T9_L3.arm_sum_split]
    · simpa [Matrix.mulVec, Matrix.transpose_apply, dotProduct, FormerRowsW1] using
        SAP.P041.WH.W1.P.T9_L3.treated_conditional_sum treated Y
  let inv : Matrix (Fin 2) (Fin 2) ℝ := !![1/76,-1/76;-1/76,151/5700]
  have hinv : (!![151,75;75,75] : Matrix (Fin 2) (Fin 2) ℝ) * inv = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [inv, Matrix.mul_apply, Fin.sum_univ_succ]
  have hunit : IsUnit ((FormerRowsW1 treated).transpose * FormerRowsW1 treated).det := by
    rw [hXgram]
    exact Matrix.isUnit_det_of_right_inverse hinv
  let X := FormerRowsW1 treated
  have hNE := AronowAudit.P041.ols_normal_equations X Y hunit
  rw [hXgram, hfit] at hNE
  have hslope := AronowAudit.P041.former_two_group_slope
    (olsCoefficients X Y) (ArmTotalW1 treated true Y) (ArmTotalW1 treated false Y) hNE
  exact ⟨hn, hXgram, hunit, hfit, hslope⟩
