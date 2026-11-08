import SAP.P041.WH.W1.Leaves
import SAP.P041.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.WH.W1.P.T7_L1

open Matrix
open scoped BigOperators

theorem sum_by_cell (cell : Fin 200 → Fin 4) (f : Fin 4 → ℝ) :
    (∑ i : Fin 200, f (cell i)) =
      ∑ c : Fin 4,
        ((Finset.univ.filter (fun i : Fin 200 => cell i = c)).card : ℝ) * f c := by
  classical
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin 200))) (t := Finset.univ) (g := cell)
    (fun _ _ => Finset.mem_univ _) (fun i => f (cell i))
  calc
    (∑ i : Fin 200, f (cell i)) =
        ∑ c ∈ (Finset.univ : Finset (Fin 4)),
          ∑ i ∈ (Finset.univ : Finset (Fin 200)) with cell i = c, f (cell i) := hfiber.symm
    _ = ∑ c : Fin 4,
          ((Finset.univ.filter (fun i : Fin 200 => cell i = c)).card : ℝ) * f c := by
      apply Finset.sum_congr rfl
      intro c hc
      have hconst : ∀ i ∈ (Finset.univ : Finset (Fin 200)).filter (fun i => cell i = c),
          f (cell i) = f c := by
        intro i hi
        exact congrArg f (Finset.mem_filter.mp hi).2
      rw [Finset.sum_congr rfl hconst]
      simp [Finset.sum_const]

theorem response_sum_cell
    (cell : Fin 200 → Fin 4) (y : Fin 200 → Bool) (c : Fin 4)
    (hsurv : ∀ c : Fin 4,
      (Finset.univ.filter (fun i : Fin 200 => cell i = c ∧ y i = true)).card =
        (![12,25,23,42] : Fin 4 → ℕ) c) :
    (∑ i ∈ (Finset.univ : Finset (Fin 200)).filter (fun i => cell i = c),
      if y i then (1 : ℝ) else 0) =
        (((![12,25,23,42] : Fin 4 → ℕ) c : ℕ) : ℝ) := by
  classical
  rw [Finset.sum_boole]
  have hfilter :
      ((Finset.univ : Finset (Fin 200)).filter (fun i => cell i = c)).filter
          (fun i => y i = true) =
        Finset.univ.filter (fun i => cell i = c ∧ y i = true) := by
    ext i
    simp [and_comm]
  rw [hfilter, hsurv c]

theorem weighted_response_sum
    (cell : Fin 200 → Fin 4) (y : Fin 200 → Bool) (f : Fin 4 → ℝ)
    (hsurv : ∀ c : Fin 4,
      (Finset.univ.filter (fun i : Fin 200 => cell i = c ∧ y i = true)).card =
        (![12,25,23,42] : Fin 4 → ℕ) c) :
    (∑ i : Fin 200, f (cell i) * (if y i then (1 : ℝ) else 0)) =
      ∑ c : Fin 4, f c *
        (((![12,25,23,42] : Fin 4 → ℕ) c : ℕ) : ℝ) := by
  classical
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin 200))) (t := Finset.univ) (g := cell)
    (fun _ _ => Finset.mem_univ _)
    (fun i => f (cell i) * (if y i then (1 : ℝ) else 0))
  calc
    (∑ i : Fin 200, f (cell i) * (if y i then (1 : ℝ) else 0)) =
        ∑ c ∈ (Finset.univ : Finset (Fin 4)),
          ∑ i ∈ (Finset.univ : Finset (Fin 200)) with cell i = c,
            f (cell i) * (if y i then (1 : ℝ) else 0) := hfiber.symm
    _ = ∑ c : Fin 4, f c *
          (((![12,25,23,42] : Fin 4 → ℕ) c : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro c hc
      have hconst : ∀ i ∈ (Finset.univ : Finset (Fin 200)).filter (fun i => cell i = c),
          f (cell i) * (if y i then (1 : ℝ) else 0) =
            f c * (if y i then (1 : ℝ) else 0) := by
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      calc
        (∑ i ∈ (Finset.univ : Finset (Fin 200)) with cell i = c,
            f (cell i) * (if y i then (1 : ℝ) else 0)) =
            f c * ∑ i ∈ (Finset.univ : Finset (Fin 200)).filter (fun i => cell i = c),
              (if y i then (1 : ℝ) else 0) := by
          rw [Finset.sum_congr rfl hconst, Finset.mul_sum]
        _ = f c * (((![12,25,23,42] : Fin 4 → ℕ) c : ℕ) : ℝ) := by
          rw [response_sum_cell cell y c hsurv]

end SAP.P041.WH.W1.P.T7_L1

open Matrix
open scoped BigOperators

theorem SAP.P041.WH.W1.T7_L1_proof : SAP.P041.WH.W1.T7_L1 := by
  classical
  intro n cell y hInput
  rcases hInput with ⟨hn, hcells, hsurvivors⟩
  subst n
  let X := SAP.P041.CitationRowsW1 cell
  let Y := SAP.P041.BinaryResponseW1 y
  have hcellReal : ∀ c : Fin 4,
      ((Finset.univ.filter (fun i : Fin 200 => cell i = c)).card : ℝ) = 50 := by
    intro c
    exact_mod_cast hcells c
  have hsurvivorReal : ∀ c : Fin 4,
      (((![12,25,23,42] : Fin 4 → ℕ) c : ℕ) : ℝ) =
        SAP.P041.citationCellSurvivors c := by
    intro c
    fin_cases c <;> norm_num [SAP.P041.citationCellSurvivors] at hsurvivors ⊢
  have hGram : X.transpose * X = SAP.P041.citationGram := by
    ext j l
    change (∑ i : Fin 200,
      SAP.P041.citationCellDesign (cell i) j * SAP.P041.citationCellDesign (cell i) l) =
        SAP.P041.citationGram j l
    rw [SAP.P041.WH.W1.P.T7_L1.sum_by_cell cell (fun c =>
      SAP.P041.citationCellDesign c j * SAP.P041.citationCellDesign c l)]
    calc
      (∑ c : Fin 4,
          ((Finset.univ.filter (fun i : Fin 200 => cell i = c)).card : ℝ) *
            (SAP.P041.citationCellDesign c j * SAP.P041.citationCellDesign c l)) =
          ∑ c : Fin 4, (50 : ℝ) *
            SAP.P041.citationCellDesign c j * SAP.P041.citationCellDesign c l := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [hcellReal c]
        ring
      _ = SAP.P041.citationGram j l := by
        exact congrFun (congrFun SAP.P041.Bridge.citation_ols_exact_fit.1 j) l
  have hCross : X.transpose *ᵥ Y = ![102,67,65] := by
    ext j
    change (∑ i : Fin 200,
      SAP.P041.citationCellDesign (cell i) j *
        (if y i then (1 : ℝ) else 0)) = (![102,67,65] : Fin 3 → ℝ) j
    rw [SAP.P041.WH.W1.P.T7_L1.weighted_response_sum cell y
      (fun c => SAP.P041.citationCellDesign c j)
      hsurvivors]
    have hcounts :
        (∑ c : Fin 4,
          SAP.P041.citationCellDesign c j *
            (((![12,25,23,42] : Fin 4 → ℕ) c : ℕ) : ℝ)) =
          (∑ c : Fin 4,
            SAP.P041.citationCellSurvivors c * SAP.P041.citationCellDesign c j) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [hsurvivorReal c]
      ring
    rw [hcounts]
    exact congrFun SAP.P041.Bridge.citation_ols_exact_fit.2.1 j
  have hCert := SAP.P041.Bridge.citation_ols_exact_fit
  have hUnit : IsUnit (X.transpose * X).det := by
    rw [hGram]
    exact Matrix.isUnit_det_of_right_inverse hCert.2.2.1
  have hInverse : (X.transpose * X)⁻¹ = SAP.P041.citationGramInverse := by
    rw [hGram, SAP.P041.Bridge.citation_gram_inverse_is_inverse]
  have hBeta : SAP.P041.olsCoefficients X Y = SAP.P041.citationBeta := by
    unfold SAP.P041.olsCoefficients
    rw [hInverse, hCross]
    exact hCert.2.2.2.2.1
  have hCellFits : ∀ c : Fin 4,
      SAP.P041.citationCellDesign c ⬝ᵥ SAP.P041.citationBeta =
        (![21/100,53/100,49/100,81/100] : Fin 4 → ℝ) c := by
    intro c
    fin_cases c <;>
      norm_num [SAP.P041.citationCellDesign, SAP.P041.citationBeta,
        dotProduct, Fin.sum_univ_succ]
  have hFits : X *ᵥ SAP.P041.olsCoefficients X Y = fun i =>
      (![21/100,53/100,49/100,81/100] : Fin 4 → ℝ) (cell i) := by
    funext i
    rw [hBeta]
    change SAP.P041.citationCellDesign (cell i) ⬝ᵥ SAP.P041.citationBeta = _
    exact hCellFits (cell i)
  change X.transpose * X = SAP.P041.citationGram ∧
    X.transpose *ᵥ Y = ![102,67,65] ∧ IsUnit (X.transpose * X).det ∧
    (X.transpose * X)⁻¹ = SAP.P041.citationGramInverse ∧
    SAP.P041.olsCoefficients X Y = SAP.P041.citationBeta ∧
    X *ᵥ SAP.P041.olsCoefficients X Y = fun i =>
      (![21/100,53/100,49/100,81/100] : Fin 4 → ℝ) (cell i)
  exact ⟨hGram, hCross, hUnit, hInverse, hBeta, hFits⟩
