import SAP.P025a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a
noncomputable section
open scoped BigOperators

def T6Statement : Prop :=
  (∀ pG pE γ : ℝ, 0 < pE → pE < pG → pG < 1 → 1 ≤ γ →
    (((binaryInterval pG γ) ∩ (binaryInterval pE γ)).Nonempty ↔
      binaryLower pG γ ≤ binaryUpper pE γ) ∧
    (binaryLower pG γ ≤ binaryUpper pE γ ↔ sampleOddsRatio pG pE ≤ γ^2) ∧
    (((binaryInterval pG γ) ∩ (binaryInterval pE γ)).Nonempty ↔
      Real.sqrt (sampleOddsRatio pG pE) ≤ γ)) ∧
  (sampleOddsRatio (917/1000) (503/1000) = 455749/41749 ∧
    (330/100 : ℝ)^2 < 455749/41749 ∧ (455749/41749 : ℝ) < (331/100)^2 ∧
    sampleOddsRatio (44/48) (291/579) = 1056/97 ∧
    (329/100 : ℝ)^2 < 1056/97 ∧ (1056/97 : ℝ) < (330/100)^2 ∧
    (9 : ℝ) < 455749/41749 ∧ (455749/41749 : ℝ) < 16 ∧
    (9 : ℝ) < 1056/97 ∧ (1056/97 : ℝ) < 16 ∧
    ((11/3 : ℝ)*(288/97) = 1056/97 ∧ (288/97 : ℝ) < 3) ∧
    ((11/4 : ℝ)*(384/97) = 1056/97 ∧ (11/4 : ℝ) < 3)) ∧
  (∀ γ : ℝ, 1 ≤ γ →
    ((((binaryInterval (917/1000) γ) ∩ (binaryInterval (503/1000) γ)).Nonempty ↔
      Real.sqrt (455749/41749) ≤ γ) ∧
     (((binaryInterval (44/48) γ) ∩ (binaryInterval (291/579) γ)).Nonempty ↔
      Real.sqrt (1056/97) ≤ γ))) ∧
  (¬ ((binaryInterval (917/1000) 3) ∩ (binaryInterval (503/1000) 3)).Nonempty ∧
    ((binaryInterval (917/1000) 4) ∩ (binaryInterval (503/1000) 4)).Nonempty ∧
    ¬ ((binaryInterval (44/48) 3) ∩ (binaryInterval (291/579) 3)).Nonempty ∧
    ((binaryInterval (44/48) 4) ∩ (binaryInterval (291/579) 4)).Nonempty) ∧
  (∀ p π₁ π₀ : ℝ, 0 < p → p < 1 → 0 < π₁ → 0 < π₀ →
    let q := reweightedPrevalence p π₁ π₀
    q = p*π₀/(p*π₀+(1-p)*π₁) ∧ q/(1-q) = (p/(1-p))*(π₀/π₁)) ∧
  (∀ (pG pE g₁ g₀ e₁ e₀ : ℝ)
    (hE : 0 < pE) (hEG : pE < pG) (hG : pG < 1)
    (hg₁ : 0 < g₁) (hg₀ : 0 < g₀) (he₁ : 0 < e₁) (he₀ : 0 < e₀),
    reweightedPrevalence pG g₁ g₀ = reweightedPrevalence pE e₁ e₀ ↔
      (g₁/g₀)*(e₀/e₁) = sampleOddsRatio pG pE) ∧
  (∀ pG pE g₁ g₀ e₁ e₀ γ : ℝ, 0 < pE → pE < pG → pG < 1 →
    0 < g₁ → 0 < g₀ → 0 < e₁ → 0 < e₀ →
    reweightedPrevalence pG g₁ g₀ = reweightedPrevalence pE e₁ e₀ →
    g₁/g₀ ≤ γ → e₀/e₁ ≤ γ → sampleOddsRatio pG pE ≤ γ^2) ∧
  (330399/100000 : ℝ) < Real.sqrt (455749/41749) ∧
  Real.sqrt (455749/41749) < (330400/100000 : ℝ) ∧
  (329948/100000 : ℝ) < Real.sqrt (1056/97) ∧
  Real.sqrt (1056/97) < (329949/100000 : ℝ)

end
end SAP.P025a
