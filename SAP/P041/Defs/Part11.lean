import SAP.P041.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041
open Matrix
open scoped BigOperators

/-- Mathematical content packaged for P041-T9. -/
def T9Statement : Prop :=
  (∀ (n k : ℕ) (j₀ : Fin k) (X : Matrix (Fin n) (Fin k) ℝ) (S : Fin n → ℝ),
      k < n → IsUnit (X.transpose * X).det → (∀ i, X i j₀ = 1) →
      olsCoefficients X (1-S) = Pi.single j₀ 1 - olsCoefficients X S ∧
      olsResidual X (1-S) = -olsResidual X S ∧
      robustMeat X (olsResidual X (1-S)) = robustMeat X (olsResidual X S) ∧
      hc1Covariance X (1-S) = hc1Covariance X S ∧
      (∀ j, Real.sqrt (hc1Covariance X (1-S) j j) =
        Real.sqrt (hc1Covariance X S j j))) ∧
  (∀ (n : ℕ) (X : Matrix (Fin n) (Fin 4) ℝ) (S : Fin n → ℝ)
      (sT sB w₂ w₄ : ℝ),
      IsUnit (X.transpose * X).det → X.transpose * X = positiveStudyGram →
      X.transpose *ᵥ S = ![sT+sB,sT,w₂,w₄] →
      olsCoefficients X S 1 = sT/150 - sB/150) ∧
  (∀ (n : ℕ) (X : Matrix (Fin n) (Fin 3) ℝ) (S : Fin n → ℝ)
      (sT sB w₄ : ℝ),
      IsUnit (X.transpose * X).det → X.transpose * X = citationGram →
      X.transpose *ᵥ S = ![sT+sB,sT,w₄] →
      olsCoefficients X S 1 = sT/100 - sB/100) ∧
  (∀ (n : ℕ) (X : Matrix (Fin n) (Fin 2) ℝ) (S : Fin n → ℝ)
      (sT sB : ℝ),
      IsUnit (X.transpose * X).det →
      X.transpose * X = !![151,75;75,75] → X.transpose *ᵥ S = ![sT+sB,sT] →
      olsCoefficients X S 1 = sT/75 - sB/76) ∧
  (armSurvivalDifference 150 150 105 88 = 17/150 ∧
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
        ¬ withinPrintedPrecision (-p.1) p.2))

end SAP.P041
