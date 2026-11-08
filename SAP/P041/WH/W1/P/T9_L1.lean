import SAP.P041.WH.W1.Leaves
import AronowAudit.P041.P041_OLS

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SAP.P041.WH.W1.P.T9_L1

open Matrix
open scoped BigOperators

private def positiveStudyGramInverse : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1/75,-1/150,-1/100,-1/100;
    -1/150,1/75,0,0;
    -1/100,0,1/50,1/100;
    -1/100,0,1/100,1/50]

theorem positiveStudyGram_right_inverse :
    positiveStudyGram * positiveStudyGramInverse = 1 := by
  ext j l
  fin_cases j <;> fin_cases l <;>
    norm_num [positiveStudyGram, positiveStudyGramInverse, Matrix.mul_apply,
      Fin.sum_univ_succ]

private theorem sum_partition_cells {n : ℕ}
    (study : Fin n → Fin 3) (treated : Fin n → Bool) (f : Fin n → ℝ) :
    (∑ i : Fin n, f i) =
      ∑ c : Fin 3 × Bool,
        ∑ i ∈ Finset.univ.filter (fun i => (study i, treated i) = c), f i := by
  classical
  have hmap : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (study i, treated i) ∈ (Finset.univ : Finset (Fin 3 × Bool)) :=
    fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.univ) (g := fun i => (study i, treated i)) hmap f]

private theorem sum_cell_constant {n : ℕ} (study : Fin n → Fin 3)
    (treated : Fin n → Bool) (hb : BalancedCellsW1 study treated)
    (w : Fin 3) (b : Bool) (f : Fin n → ℝ) (v : ℝ)
    (hf : ∀ i ∈ Finset.univ.filter (fun i => study i = w ∧ treated i = b), f i = v) :
    (∑ i ∈ Finset.univ.filter (fun i => study i = w ∧ treated i = b), f i) = 50 * v := by
  calc
    _ = ∑ _i ∈ Finset.univ.filter (fun i => study i = w ∧ treated i = b), v := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hf i hi
    _ = 50 * v := by simp [hb w b]

private theorem positive_rows_constant {n : ℕ}
    (study : Fin n → Fin 3) (treated : Fin n → Bool)
    (w : Fin 3) (b : Bool) (i : Fin n)
    (hi : i ∈ Finset.univ.filter (fun i => study i = w ∧ treated i = b)) :
    PositiveRowsW1 study treated i =
      ![(1 : ℝ), (if b then 1 else 0), (if w = 1 then 1 else 0),
        (if w = 2 then 1 else 0)] := by
  have hs := (Finset.mem_filter.mp hi).2.1
  have ht := (Finset.mem_filter.mp hi).2.2
  simp [PositiveRowsW1, hs, ht]

private def positiveCellRow (w : Fin 3) (b : Bool) : Fin 4 → ℝ :=
  ![(1 : ℝ), (if b then 1 else 0), (if w = 1 then 1 else 0),
    (if w = 2 then 1 else 0)]

theorem positive_gram_from_cells {n : ℕ}
    (study : Fin n → Fin 3) (treated : Fin n → Bool)
    (hb : BalancedCellsW1 study treated) :
    (PositiveRowsW1 study treated).transpose * PositiveRowsW1 study treated =
      positiveStudyGram := by
  let X := PositiveRowsW1 study treated
  ext j l
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [sum_partition_cells study treated (fun i => X i j * X i l)]
  rw [Fintype.sum_prod_type]
  calc
    (∑ w : Fin 3, ∑ b : Bool,
        ∑ i ∈ Finset.univ.filter (fun i => (study i, treated i) = (w, b)),
          X i j * X i l) =
      ∑ w : Fin 3, ∑ b : Bool, 50 * (positiveCellRow w b j * positiveCellRow w b l) := by
        apply Finset.sum_congr rfl
        intro w hw
        apply Finset.sum_congr rfl
        intro b hb'
        have hcell := sum_cell_constant study treated hb w b
          (fun i => X i j * X i l) (positiveCellRow w b j * positiveCellRow w b l)
          (by
            intro i hi
            have hr := positive_rows_constant study treated w b i hi
            have hrow : X i = positiveCellRow w b := by
              simpa [X, positiveCellRow] using hr
            rw [hrow])
        simpa only [Prod.mk.injEq] using hcell
    _ = positiveStudyGram j l := by
      fin_cases j <;> fin_cases l <;>
        norm_num [positiveStudyGram, positiveCellRow, Fin.sum_univ_succ]

private theorem sum_if_eq_filter {n : ℕ} (p : Fin n → Prop)
    [DecidablePred p] (f : Fin n → ℝ) :
    (∑ i : Fin n, if p i then f i else 0) =
      ∑ i ∈ Finset.univ.filter p, f i := by
  classical
  simp only [← Finset.sum_filter]

private theorem sum_if_bool_true {n : ℕ} (treated : Fin n → Bool)
    (Y : Fin n → ℝ) :
    (∑ i : Fin n, (if treated i then 1 else 0) * Y i) =
      ArmTotalW1 treated true Y := by
  classical
  rw [show (∑ i : Fin n, (if treated i then 1 else 0) * Y i) =
      ∑ i : Fin n, (if treated i = true then Y i else 0) by
        apply Finset.sum_congr rfl
        intro i _
        cases treated i <;> simp]
  simp [ArmTotalW1, Finset.sum_filter]

private theorem sum_if_study {n : ℕ} (study : Fin n → Fin 3)
    (w : Fin 3) (Y : Fin n → ℝ) :
    (∑ i : Fin n, (if study i = w then 1 else 0) * Y i) =
      StudyTotalW1 study w Y := by
  classical
  rw [show (∑ i : Fin n, (if study i = w then 1 else 0) * Y i) =
      ∑ i : Fin n, (if study i = w then Y i else 0) by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring]
  simp [StudyTotalW1, Finset.sum_filter]

private theorem sum_eq_arm_totals {n : ℕ} (treated : Fin n → Bool)
    (Y : Fin n → ℝ) :
    (∑ i : Fin n, Y i) = ArmTotalW1 treated true Y + ArmTotalW1 treated false Y := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin n)))
    (p := fun i => treated i = true) (f := Y)]
  simp [ArmTotalW1]

theorem positive_cross_products {n : ℕ}
    (study : Fin n → Fin 3) (treated : Fin n → Bool) (Y : Fin n → ℝ) :
    (PositiveRowsW1 study treated).transpose *ᵥ Y =
      ![ArmTotalW1 treated true Y + ArmTotalW1 treated false Y,
        ArmTotalW1 treated true Y, StudyTotalW1 study 1 Y,
        StudyTotalW1 study 2 Y] := by
  ext j
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Matrix.transpose_apply]
  fin_cases j
  · simpa [PositiveRowsW1] using sum_eq_arm_totals treated Y
  · simpa [PositiveRowsW1] using sum_if_bool_true treated Y
  · simpa [PositiveRowsW1] using sum_if_study study 1 Y
  · simpa [PositiveRowsW1] using sum_if_study study 2 Y

end SAP.P041.WH.W1.P.T9_L1

open SAP.P041.WH.W1.P.T9_L1
open Matrix

theorem SAP.P041.WH.W1.T9_L1_proof : SAP.P041.WH.W1.T9_L1 := by
  intro n study treated Y hb
  let X := PositiveRowsW1 study treated
  have hsize : n = 300 := by
    classical
    have hcard : Fintype.card (Fin n) =
        ∑ c : Fin 3 × Bool,
          (Finset.univ.filter (fun i => (study i, treated i) = c)).card := by
      have hh := Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset (Fin 3 × Bool)))
        (f := fun i => (study i, treated i))
        (H := fun _ _ => Finset.mem_univ _)
      simpa using hh
    have hcards : ∀ w : Fin 3, ∀ b : Bool,
        (Finset.univ.filter (fun i => study i = w ∧ treated i = b)).card = 50 := hb
    have hsimp : (∑ c : Fin 3 × Bool,
        (Finset.univ.filter (fun i => (study i, treated i) = c)).card) = 300 := by
      rw [Fintype.sum_prod_type]
      simp only [Prod.mk.injEq]
      calc
        (∑ w : Fin 3, ∑ b : Bool,
            (Finset.univ.filter (fun i => study i = w ∧ treated i = b)).card) =
          ∑ w : Fin 3, ∑ b : Bool, 50 := by
            apply Finset.sum_congr rfl
            intro w hw
            apply Finset.sum_congr rfl
            intro b hb'
            rw [hcards w b]
        _ = 300 := by norm_num [Fin.sum_univ_succ]
    simpa using hcard.trans hsimp
  have hgram : X.transpose * X = positiveStudyGram := by
    exact positive_gram_from_cells study treated hb
  have hunit : IsUnit (X.transpose * X).det := by
    rw [hgram]
    exact Matrix.isUnit_det_of_right_inverse positiveStudyGram_right_inverse
  have hcross : X.transpose *ᵥ Y =
      ![ArmTotalW1 treated true Y + ArmTotalW1 treated false Y,
        ArmTotalW1 treated true Y, StudyTotalW1 study 1 Y,
        StudyTotalW1 study 2 Y] := positive_cross_products study treated Y
  have hnormal := AronowAudit.P041.ols_normal_equations X Y hunit
  have hbeta : positiveStudyGram *ᵥ olsCoefficients X Y =
      ![ArmTotalW1 treated true Y + ArmTotalW1 treated false Y,
        ArmTotalW1 treated true Y, StudyTotalW1 study 1 Y,
        StudyTotalW1 study 2 Y] := by
    calc
      positiveStudyGram *ᵥ olsCoefficients X Y =
          (X.transpose * X) *ᵥ olsCoefficients X Y := by rw [← hgram]
      _ = X.transpose *ᵥ Y := hnormal
      _ = ![ArmTotalW1 treated true Y + ArmTotalW1 treated false Y,
          ArmTotalW1 treated true Y, StudyTotalW1 study 1 Y,
          StudyTotalW1 study 2 Y] := hcross
  have hslope := AronowAudit.P041.positive_balanced_slope
    (olsCoefficients X Y) (ArmTotalW1 treated true Y)
    (ArmTotalW1 treated false Y) (StudyTotalW1 study 1 Y)
    (StudyTotalW1 study 2 Y) hbeta
  exact ⟨hsize, hgram, hunit, hcross, hslope⟩
