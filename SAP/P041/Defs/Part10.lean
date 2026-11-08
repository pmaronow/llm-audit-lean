import SAP.P041.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041
open Matrix
open scoped BigOperators

/-- Mathematical content packaged for P041-T8. -/
def T8Statement : Prop :=
  ((∀ h s : ℝ, printedInterval 0.670 h → printedInterval 0.095 s →
      2.80 < |hazardWald h s|) ∧
    (∀ h s : ℝ, printedInterval 0.480 h → printedInterval 0.174 s →
      2.01 < |hazardWald h s| ∧ |hazardWald h s| < 2.04) ∧
    (∀ h s : ℝ, printedInterval 0.274 h → printedInterval 0.162 s →
      2.18 < |hazardWald h s| ∧ |hazardWald h s| < 2.20) ∧
    (∀ h s : ℝ, printedInterval 0.316 h → printedInterval 0.149 s →
      2.43 < |hazardWald h s| ∧ |hazardWald h s| < 2.46)) ∧
  ((∀ h s : ℝ, printedInterval 0.670 h → printedInterval 0.095 s →
      normalTwoSided (hazardWald h s) < 0.01 ∧ significanceTier (hazardWald h s) = 3) ∧
    (∀ h s : ℝ, printedInterval 0.480 h → printedInterval 0.174 s →
      0.01 < normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.05 ∧
      significanceTier (hazardWald h s) = 2) ∧
    (∀ h s : ℝ, printedInterval 0.274 h → printedInterval 0.162 s →
      0.01 < normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.05 ∧
      significanceTier (hazardWald h s) = 2) ∧
    (∀ h s : ℝ, printedInterval 0.316 h → printedInterval 0.149 s →
      0.01 < normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.05 ∧
      significanceTier (hazardWald h s) = 2)) ∧
  (∀ (p₁ p₂ p₃ p₄ : ℝ)
    (h₁ : p₁ < 0.01) (h₂ : 0.01 < p₂ ∧ p₂ < 0.05)
    (h₃ : 0.01 < p₃ ∧ p₃ < 0.05) (h₄ : 0.01 < p₄ ∧ p₄ < 0.05),
    p₁ < 0.05 ∧ p₂ < 0.10 ∧ p₃ < 0.10 ∧ ¬ p₄ < 0.01)

end SAP.P041
