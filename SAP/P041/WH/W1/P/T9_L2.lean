import SAP.P041.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SAP.P041.WH.W1.P.T9_L2

open Matrix
open scoped BigOperators

def citedCellRow (w : Fin 2) (b : Bool) : Fin 3 → ℝ :=
  ![1, if b then 1 else 0, if w = 1 then 1 else 0]

lemma sum_by_cited_cells {n : ℕ} (study : Fin n → Fin 2)
    (treated : Fin n → Bool) (hbal : BalancedCellsW1 study treated)
    (f : Fin 2 → Bool → ℝ) :
    (∑ i : Fin n, f (study i) (treated i)) =
      ∑ w : Fin 2, ∑ b : Bool, (50 : ℝ) * f w b := by
  classical
  have hgroup :
      (∑ p : Fin 2 × Bool,
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => (study i, treated i) = p),
          f p.1 p.2) =
        ∑ i : Fin n, f (study i) (treated i) := by
    exact Finset.sum_fiberwise_of_maps_to'
      (s := Finset.univ) (t := Finset.univ)
      (g := fun i : Fin n => (study i, treated i))
      (by intro i hi; simp) (fun p : Fin 2 × Bool => f p.1 p.2)
  rw [← hgroup, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro b hb
  have hcard :
      (Finset.univ.filter (fun i : Fin n => (study i, treated i) = (w, b))).card = 50 := by
    simpa using hbal w b
  have hfilter :
      Finset.univ.filter (fun i : Fin n => (study i, treated i) = (w, b)) =
        Finset.univ.filter (fun i => study i = w ∧ treated i = b) := by
    ext i
    simp
  rw [hfilter, Finset.sum_const, nsmul_eq_mul]
  rw [hbal w b]
  norm_num

lemma card_eq_two_hundred {n : ℕ} (study : Fin n → Fin 2)
    (treated : Fin n → Bool) (hbal : BalancedCellsW1 study treated) : n = 200 := by
  have h := sum_by_cited_cells study treated hbal (fun _ _ => (1 : ℝ))
  norm_num [Finset.sum_const, nsmul_eq_mul] at h
  exact_mod_cast h

end SAP.P041.WH.W1.P.T9_L2

open Matrix
open scoped BigOperators

theorem SAP.P041.WH.W1.T9_L2_proof : SAP.P041.WH.W1.T9_L2 := by
  classical
  intro n study treated Y hbal
  let X := SAP.P041.CitedRowsW1 study treated
  have hn : n = 200 := SAP.P041.WH.W1.P.T9_L2.card_eq_two_hundred study treated hbal
  have hGram : X.transpose * X = SAP.P041.citationGram := by
    ext j l
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    change (∑ i : Fin n,
      SAP.P041.WH.W1.P.T9_L2.citedCellRow (study i) (treated i) j *
        SAP.P041.WH.W1.P.T9_L2.citedCellRow (study i) (treated i) l) =
        SAP.P041.citationGram j l
    rw [SAP.P041.WH.W1.P.T9_L2.sum_by_cited_cells study treated hbal
      (fun w b => SAP.P041.WH.W1.P.T9_L2.citedCellRow w b j *
        SAP.P041.WH.W1.P.T9_L2.citedCellRow w b l)]
    fin_cases j <;> fin_cases l <;>
      norm_num [SAP.P041.WH.W1.P.T9_L2.citedCellRow, SAP.P041.citationGram,
        Fintype.sum_prod_type, Fin.sum_univ_succ]
  have hInv : SAP.P041.citationGram * SAP.P041.citationGramInverse = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [SAP.P041.citationGram, SAP.P041.citationGramInverse,
        Matrix.mul_apply, Fin.sum_univ_succ]
  have hUnit : IsUnit (X.transpose * X).det := by
    rw [hGram]
    exact Matrix.isUnit_det_of_right_inverse hInv
  have hCross : X.transpose *ᵥ Y =
      ![SAP.P041.ArmTotalW1 treated true Y + SAP.P041.ArmTotalW1 treated false Y,
        SAP.P041.ArmTotalW1 treated true Y,
        SAP.P041.StudyTotalW1 study 1 Y] := by
    ext j
    fin_cases j
    · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      change (∑ i : Fin n, (1 : ℝ) * Y i) = _
      simp only [one_mul]
      calc
        (∑ i : Fin n, Y i) =
            (∑ i : Fin n, ((if treated i then Y i else 0) +
              (if treated i = false then Y i else 0))) := by
                apply Finset.sum_congr rfl
                intro i hi
                cases treated i <;> simp
        _ = SAP.P041.ArmTotalW1 treated true Y + SAP.P041.ArmTotalW1 treated false Y := by
          rw [Finset.sum_add_distrib]
          simp [SAP.P041.ArmTotalW1, Finset.sum_filter]
    · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      change (∑ i : Fin n, (if treated i then (1 : ℝ) else 0) * Y i) = _
      simp [SAP.P041.ArmTotalW1, Finset.sum_filter]
    · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      change (∑ i : Fin n, (if study i = 1 then (1 : ℝ) else 0) * Y i) = _
      simp [SAP.P041.StudyTotalW1, Finset.sum_filter]
  have hnormal := AronowAudit.P041.ols_normal_equations X Y hUnit
  rw [hGram, hCross] at hnormal
  have hβ : SAP.P041.citationGram *ᵥ olsCoefficients X Y =
      ![SAP.P041.ArmTotalW1 treated true Y + SAP.P041.ArmTotalW1 treated false Y,
        SAP.P041.ArmTotalW1 treated true Y,
        SAP.P041.StudyTotalW1 study 1 Y] := hnormal
  have hslope := SAP.P041.Bridge.cited_balanced_slope (olsCoefficients X Y)
    (SAP.P041.ArmTotalW1 treated true Y) (SAP.P041.ArmTotalW1 treated false Y)
    (SAP.P041.StudyTotalW1 study 1 Y) hβ
  exact ⟨hn, hGram, hUnit, hCross, hslope⟩
