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

theorem exponential_survival_power_laws :
  ∀ (q t : ℝ) (hq : 0 < q),
    exponentialSurvival (positiveHazard q) t = q^(t/6) ∧
    exponentialSurvival (negativeHazard q) t = q^(t/4) := by
  exact @AronowAudit.P041.exponential_survival_power_laws

theorem twelve_hour_survival :
  ∀ (q : ℝ) (hq : 0 < q),
    exponentialSurvival (positiveHazard q) 12 = q^2 ∧
    exponentialSurvival (negativeHazard q) 12 = q^3 ∧
    twelveHourContrast q = q^2 * (1-q) := by
  exact @AronowAudit.P041.twelve_hour_survival

theorem risk_measure_gaps :
  relativeIncrease 75 52 - symmetricDifference 75 52 = 13225/1651 ∧
    relativeIncrease 92 69 - symmetricDifference 92 69 = 100/21 ∧
    relativeIncrease 62 32 - symmetricDifference 62 32 = 5625/188 := by
  exact @AronowAudit.P041.risk_measure_gaps

theorem risk_percentages_counterexample :
  relativeIncrease (75/150) (52/150) = 575/13 ∧
    relativeIncrease (92/150) (69/150) = 100/3 ∧
    relativeIncrease (62/100) (32/100) = 375/4 ∧
    (575/13 : ℝ) - 36 = 107/13 ∧ (107/13 : ℝ) > 1/2 ∧
    (100/3 : ℝ) - 29 = 13/3 ∧ (13/3 : ℝ) > 1/2 ∧
    (375/4 : ℝ) - 64 = 119/4 ∧ (119/4 : ℝ) > 1/2 ∧
    ¬ roundsWhole (relativeIncrease (75/150) (52/150)) 36 ∧
    ¬ roundsWhole (relativeIncrease (92/150) (69/150)) 29 ∧
    ¬ roundsWhole (relativeIncrease (62/100) (32/100)) 64 ∧
    roundsWhole (relativeIncrease (75/150) (52/150)) 44 ∧
    roundsWhole (relativeIncrease (92/150) (69/150)) 33 ∧
    roundsWhole (relativeIncrease (62/100) (32/100)) 94 ∧
    symmetricDifference 75 52 = 4600/127 ∧
    symmetricDifference 92 69 = 200/7 ∧
    symmetricDifference 62 32 = 3000/47 ∧
    roundsWhole (symmetricDifference 75 52) 36 ∧
    roundsWhole (symmetricDifference 92 69) 29 ∧
    roundsWhole (symmetricDifference 62 32) 64 := by
  exact @AronowAudit.P041.risk_percentages_counterexample

theorem symmetric_understates_relative :
  ∀ (a b : ℝ) (hb : 0 < b) (hab : b < a),
    relativeIncrease a b - symmetricDifference a b =
      100 * (a-b)^2 / (b*(a+b)) ∧
    0 < relativeIncrease a b - symmetricDifference a b := by
  exact @AronowAudit.P041.symmetric_understates_relative

theorem corrected_risk_percentages :
  relativeIncrease (75/150) (52/150) = 575/13 ∧
    roundsWhole (relativeIncrease (75/150) (52/150)) 44 ∧
    |relativeIncrease (75/150) (52/150) - 44.23| ≤ 0.005 ∧
    relativeIncrease (92/150) (69/150) = 100/3 ∧
    roundsWhole (relativeIncrease (92/150) (69/150)) 33 ∧
    |relativeIncrease (92/150) (69/150) - 33.33| ≤ 0.005 ∧
    relativeIncrease (62/100) (32/100) = 375/4 ∧
    relativeIncrease (62/100) (32/100) = 93.75 ∧
    roundsWhole (relativeIncrease (62/100) (32/100)) 94 ∧
    relativeIncrease (76/150) (52/150) = 600/13 ∧
    roundsWhole (relativeIncrease (76/150) (52/150)) 46 ∧
    |relativeIncrease (76/150) (52/150) - 46.15| ≤ 0.005 ∧
    symmetricDifference 75 52 = 4600/127 ∧
    symmetricDifference 92 69 = 200/7 ∧
    symmetricDifference 62 32 = 3000/47 ∧
    roundsWhole (symmetricDifference 75 52) 36 ∧
    roundsWhole (symmetricDifference 92 69) 29 ∧
    roundsWhole (symmetricDifference 62 32) 64 := by
  exact @AronowAudit.P041.corrected_risk_percentages

theorem slow_schedule_zero :
  ∀ (m : ℕ) (z : Finset (Fin (2*m))),
    citationContrast m z (fun _ => 0) = 0 := by
  exact @AronowAudit.P041.slow_schedule_zero

theorem nested_significance_reading :
  ∀ (p₁ p₂ p₃ p₄ : ℝ)
    (h₁ : p₁ < 0.01) (h₂ : 0.01 < p₂ ∧ p₂ < 0.05)
    (h₃ : 0.01 < p₃ ∧ p₃ < 0.05) (h₄ : 0.01 < p₄ ∧ p₄ < 0.05),
    p₁ < 0.05 ∧ p₂ < 0.10 ∧ p₃ < 0.10 ∧ ¬ p₄ < 0.01 := by
  exact @AronowAudit.P041.nested_significance_reading

theorem printed_tenure_reciprocal_enclosures :
  (∀ r : ℝ, 0.989-0.0005 ≤ r → r ≤ 0.989+0.0005 →
      1.0106 < 1/r ∧ 1/r < 1.0117 ∧ 1 < 1/r) ∧
    (∀ r : ℝ, 0.981-0.0005 ≤ r → r ≤ 0.981+0.0005 →
      1.0188 < 1/r ∧ 1/r < 1.0199 ∧ 1 < 1/r) ∧
    (∀ r : ℝ, 1.056-0.0005 ≤ r → r ≤ 1.056+0.0005 →
      0.9465 < 1/r ∧ 1/r < 0.9475 ∧ 1/r < 1) ∧
    (∀ r : ℝ, 1.004-0.0005 ≤ r → r ≤ 1.004+0.0005 →
      0.9955 < 1/r ∧ 1/r < 0.9966 ∧ 1/r < 1) := by
  exact @AronowAudit.P041.printed_tenure_reciprocal_enclosures

theorem tenure_multiplier_is_reciprocal :
  ∀ (a g C L : ℝ),
    Real.exp (-g) = 1 / Real.exp g ∧
    Real.exp ((a+C*g)+(-g)*(L+1)) =
      Real.exp ((a+C*g)+(-g)*L) * (1/Real.exp g) ∧
    (∀ r : ℝ, 0 < r →
      ((r < 1 ↔ 1 < 1/r) ∧ (1 < r ↔ 1/r < 1))) := by
  exact @AronowAudit.P041.tenure_multiplier_is_reciprocal

theorem year_tenure_exact_instance :
  tenureFromYear 2014 2009 = 5 ∧ tenureFromYear 2014 2008 = 6 ∧
    illustrativeYearRelativeHazard 0 2009 = 1 ∧
    illustrativeYearRelativeHazard 0 2008 = 1 ∧
    illustrativeYearRelativeHazard 1 2009 = 1 ∧
    illustrativeYearRelativeHazard 1 2008 = 125/132 ∧
    (1:ℝ) < 132/125 ∧ (125/132:ℝ) < 1 ∧
    (132/125:ℝ)*(125/132) = 1 := by
  exact @AronowAudit.P041.year_tenure_exact_instance

theorem year_tenure_reparameterization :
  ∀ (h₀ a b g C L T w : ℝ),
    b*(C-L)+a*T+g*T*(C-L)+w =
      C*b+(-b)*L+(a+C*g)*T+(-g)*T*L+w ∧
    tenureHazard h₀ b a g C L T w = yearHazard h₀ b a g (C-L) T w := by
  exact @AronowAudit.P041.year_tenure_reparameterization

theorem printed_directional_percentages_refuted :
  ¬ (roundsWhole (relativeIncrease (75/150) (52/150)) 36 ∧
    roundsWhole (relativeIncrease (92/150) (69/150)) 29 ∧
    roundsWhole (relativeIncrease (62/100) (32/100)) 64) := by
  exact @AronowAudit.P041.printed_directional_percentages_refuted

theorem printed_percentages_arithmetic_and_direction :
  symmetricDifference 75 52 = 4600/127 ∧
    symmetricDifference 92 69 = 200/7 ∧
    symmetricDifference 62 32 = 3000/47 ∧
    roundsWhole (symmetricDifference 75 52) 36 ∧
    roundsWhole (symmetricDifference 92 69) 29 ∧
    roundsWhole (symmetricDifference 62 32) 64 ∧
    (52/150 : ℝ) < 75/150 ∧ (69/150 : ℝ) < 92/150 ∧
    (32/100 : ℝ) < 62/100 := by
  exact @AronowAudit.P041.printed_percentages_arithmetic_and_direction

end SAP.P041.Bridge
