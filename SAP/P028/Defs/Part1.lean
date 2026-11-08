import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

def effect (p e0 e1 : ℝ) : ℝ := (e1 - e0) / p

def lowerControl (p e0 e1 : ℝ) : ℝ :=
  max (max 0 (-effect p e0 e1)) (1 - (1 - e0) / p)

def upperControl (p e0 e1 : ℝ) : ℝ :=
  min (min 1 (1 - effect p e0 e1)) (e0 / p)

def lowerTreated (p e0 e1 : ℝ) : ℝ :=
  max (max 0 (effect p e0 e1)) (1 - (1 - e1) / p)

def upperTreated (p e0 e1 : ℝ) : ℝ :=
  min (min 1 (1 + effect p e0 e1)) (e1 / p)

def mixtureSystem (p e0 e1 x0 x1 : ℝ) : Prop :=
  ∃ n : ℝ, p*x0 + (1-p)*n = e0 ∧ p*x1 + (1-p)*n = e1 ∧
    0 ≤ x0 ∧ x0 ≤ 1 ∧ 0 ≤ x1 ∧ x1 ≤ 1 ∧ 0 ≤ n ∧ n ≤ 1

def correctedSystem (p e0 e1 x0 x1 : ℝ) : Prop :=
  p*x0 + e1 - p*x1 = e0 ∧ 0 ≤ x0 ∧ x0 ≤ 1 ∧ 0 ≤ x1 ∧ x1 ≤ 1 ∧
    0 ≤ e1-p*x1 ∧ e1-p*x1 ≤ 1-p

def printedSystem (p e0 e1 x0 x1 : ℝ) : Prop :=
  p*x0 + e1 - p*x1 = e0 ∧ 0 ≤ x0 ∧ x0 ≤ 1 ∧ 0 ≤ x1 ∧ x1 ≤ 1 ∧
    0 ≤ e1-p*x1 ∧ e1-p*x1 ≤ 1

end
end SAP.P028
