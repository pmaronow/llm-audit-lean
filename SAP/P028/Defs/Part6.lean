import SAP.P028.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

def T4Statement : Prop :=
  (∀ p e0 e1 x0 x1 : ℝ, 0 < p → p < 1 →
    (mixtureSystem p e0 e1 x0 x1 ↔ correctedSystem p e0 e1 x0 x1) ∧
    (∀ n, p*x1+(1-p)*n = e1 → n = (e1-p*x1)/(1-p)) ∧
    (p*x0+e1-p*x1 = e0 ↔ x0 = x1-effect p e0 e1) ∧
    (x0 = x1-effect p e0 e1 →
      ((0 ≤ x0 ∧ x0 ≤ 1) ↔ (effect p e0 e1 ≤ x1 ∧ x1 ≤ 1+effect p e0 e1))) ∧
    ((0 ≤ e1-p*x1 ∧ e1-p*x1 ≤ 1-p) ↔ ((e1+p-1)/p ≤ x1 ∧ x1 ≤ e1/p)) ∧
    (e1+p-1)/p = 1-(1-e1)/p ∧
    (mixtureSystem p e0 e1 x0 x1 ↔ x0 = x1-effect p e0 e1 ∧
      lowerTreated p e0 e1 ≤ x1 ∧ x1 ≤ upperTreated p e0 e1) ∧
    lowerTreated p e0 e1-effect p e0 e1 = lowerControl p e0 e1 ∧
    upperTreated p e0 e1-effect p e0 e1 = upperControl p e0 e1 ∧
    ((0 ≤ e1-p*x1 ∧ e1-p*x1 ≤ 1) ↔ ((e1-1)/p ≤ x1 ∧ x1 ≤ e1/p)) ∧
    (e1 ≤ 1 → 0 ≤ x1 → (e1-1)/p ≤ x1 ∧
      ((0 ≤ e1-p*x1 ∧ e1-p*x1 ≤ 1) ↔ x1 ≤ e1/p)) ∧
    (mixtureSystem p e0 e1 x0 x1 → printedSystem p e0 e1 x0 x1)) ∧
  (printedSystem (1/2) (3/4) (3/4) 0 0 ∧
    ¬ mixtureSystem (1/2) (3/4) (3/4) 0 0)

def misprintFacts : Prop :=
  printedSystem (1/2) (3/4) (3/4) 0 0 ∧
    ¬ mixtureSystem (1/2) (3/4) (3/4) 0 0 ∧
    ¬ correctedSystem (1/2) (3/4) (3/4) 0 0 ∧
    ((3/4-(1/2)*0)/(1-1/2) : ℝ) = 3/2 ∧
    (((3/4)-1)/(1/2) : ℝ) = -1/2 ∧
    (((3/4)+(1/2)-1)/(1/2) : ℝ) = 1/2 ∧
    lowerControl (1/2) (3/4) (3/4) = 1/2 ∧
    upperControl (1/2) (3/4) (3/4) = 1 ∧
    lowerTreated (1/2) (3/4) (3/4) = 1/2 ∧
    upperTreated (1/2) (3/4) (3/4) = 1

def T5Statement : Prop :=
  misprintFacts ∧
  ∃ M : CausalModel (Bool × Bool), boundedOutcomes M ∧
    complierProbability M = 1/2 ∧ armMean M false = 3/4 ∧ armMean M true = 3/4 ∧
    complierMean M false = 1 ∧ complierMean M true = 1

end
end SAP.P028
