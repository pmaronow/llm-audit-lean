import SAP.P041.Defs
import AronowAudit.P041.P041_Hazards
import AronowAudit.P041.P041_OLS
import AronowAudit.P041.P041_Order
import AronowAudit.P041.P041_PrintedRefutations
import AronowAudit.P041.P041_Risks
import AronowAudit.P041.P041_Tenure
import AronowAudit.P041.P041_Wald
import AronowAudit.P041.Wave1.Gap.GLP041P042P045B1
import AronowAudit.P041.Wave1.Gap.GP041P042P045B1

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.Bridge
open Matrix
open scoped BigOperators

theorem citation_gram_inverse_is_inverse :
  citationGram⁻¹ = citationGramInverse := by
  exact @AronowAudit.P041.citation_gram_inverse_is_inverse

theorem citation_hc1_exact_variance :
  (fun i => citationCellDesign i ⬝ᵥ citationBeta) = ![21/100,53/100,49/100,81/100] ∧
    binaryCellSSR 50 12 (21/100) = 1833/200 ∧
    binaryCellSSR 50 25 (53/100) = 2509/200 ∧
    binaryCellSSR 50 23 (49/100) = 2493/200 ∧
    binaryCellSSR 50 42 (81/100) = 1353/200 ∧
    ((1833/200 + 2509/200 + 2493/200 + 1353/200 : ℝ)) = 2047/50 ∧
    (∀ i : Fin 4, (citationGramInverse 1 ⬝ᵥ citationCellDesign i)^2 = 1/10000) ∧
    (200/197 : ℝ) * (∑ i : Fin 4,
      binaryCellSSR 50 (citationCellSurvivors i) (citationCellDesign i ⬝ᵥ citationBeta) *
      (citationGramInverse 1 ⬝ᵥ citationCellDesign i)^2) = 2047/492500 := by
  exact @AronowAudit.P041.citation_hc1_exact_variance

theorem citation_ols_exact_fit :
  (fun j l => ∑ i : Fin 4, (50:ℝ) * citationCellDesign i j *
      citationCellDesign i l) = citationGram ∧
    (fun j => ∑ i : Fin 4, citationCellSurvivors i * citationCellDesign i j) =
      ![102,67,65] ∧
    citationGram * citationGramInverse = 1 ∧
    citationGramInverse * citationGram = 1 ∧
    citationGramInverse *ᵥ ![102,67,65] = citationBeta ∧
    citationBeta 1 = 0.320 ∧
    citationBeta 1 = (1/2)*((25-12)/50 + (42-23)/50) := by
  exact @AronowAudit.P041.citation_ols_exact_fit

theorem corrected_citation_standard_error :
  (0.320/0.645 : ℝ) = 64/129 ∧ (64/129 : ℝ) < 1 ∧
    (0.0635 : ℝ)^2 ≤ 2047/492500 ∧ (2047/492500 : ℝ) < 0.0645^2 ∧
    0.0635 ≤ Real.sqrt (2047/492500) ∧ Real.sqrt (2047/492500) < 0.0645 ∧
    (0.645 : ℝ)^2 = 16641/40000 ∧ (16641/40000 : ℝ) ≠ 2047/492500 ∧
    ((8/25 : ℝ)^2 / (2047/492500)) = 50432/2047 ∧
    (24 : ℝ) < 50432/2047 ∧ (2.61 : ℝ)^2 < 24 ∧
    4.89 < (8/25 : ℝ) / Real.sqrt (2047/492500) ∧
    2.61 < (8/25 : ℝ) / Real.sqrt (2047/492500) := by
  exact @AronowAudit.P041.corrected_citation_standard_error

theorem cited_balanced_slope :
  ∀ (β : Fin 3 → ℝ) (sT sB w₄ : ℝ)
    (hβ : citationGram *ᵥ β = ![sT+sB,sT,w₄]),
    β 1 = sT/100 - sB/100 := by
  exact @AronowAudit.P041.cited_balanced_slope

theorem ols_complement_coefficients :
  ∀ {n k : Type*} [Fintype n] [Fintype k]
    [DecidableEq k] (X : Matrix n k ℝ) (e₁ : k → ℝ) (S : n → ℝ)
    (hX : IsUnit (X.transpose * X).det) (h₁ : X *ᵥ e₁ = 1),
    olsCoefficients X (1-S) = e₁ - olsCoefficients X S := by
  exact @AronowAudit.P041.ols_complement_coefficients

theorem ols_complement_residuals_and_covariance :
  ∀ {n k : Type*} [Fintype n]
    [Fintype k] [DecidableEq k] (X : Matrix n k ℝ) (e₁ : k → ℝ) (S : n → ℝ)
    (hX : IsUnit (X.transpose * X).det) (h₁ : X *ᵥ e₁ = 1),
    olsResidual X (1-S) = -olsResidual X S ∧
    robustMeat X (olsResidual X (1-S)) = robustMeat X (olsResidual X S) ∧
    hc1Covariance X (1-S) = hc1Covariance X S := by
  exact @AronowAudit.P041.ols_complement_residuals_and_covariance

theorem positive_balanced_slope :
  ∀ (β : Fin 4 → ℝ) (sT sB w₂ w₄ : ℝ)
    (hβ : positiveStudyGram *ᵥ β = ![sT+sB,sT,w₂,w₄]),
    β 1 = sT/150 - sB/150 := by
  exact @AronowAudit.P041.positive_balanced_slope

theorem s11_survival_slopes_and_not_removal :
  armSurvivalDifference 150 150 105 88 = 17/150 ∧
    armSurvivalDifference 150 150 98 75 = 23/150 ∧
    armSurvivalDifference 150 150 90 68 = 11/75 ∧
    armSurvivalDifference 150 150 68 49 = 19/150 ∧
    armSurvivalDifference 100 100 67 35 = 8/25 ∧
    armSurvivalDifference 100 100 63 26 = 37/100 ∧
    armSurvivalDifference 100 100 58 19 = 39/100 ∧
    armSurvivalDifference 100 100 34 11 = 23/100 ∧
    armSurvivalDifference 75 76 72 75 = -51/1900 ∧
    armSurvivalDifference 75 76 68 73 = -307/5700 ∧
    (∀ p ∈ ({(17/150,0.113),(23/150,0.153),(11/75,0.147),(19/150,0.127),
      (8/25,0.320),(37/100,0.370),(39/100,0.390),(23/100,0.230),
      (-51/1900,-0.027),(-307/5700,-0.054)} : Finset (ℝ × ℝ)),
      p.1 ≠ 0 ∧ withinPrintedPrecision p.1 p.2 ∧
        ¬ withinPrintedPrecision (-p.1) p.2) := by
  exact @AronowAudit.P041.s11_survival_slopes_and_not_removal

end SAP.P041.Bridge
