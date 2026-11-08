import SAP.P025a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a
noncomputable section
open scoped BigOperators

def T1Statement : Prop :=
  ((0 : ℝ) < 1/2 ∧ (1/2 : ℝ) ≤ 1 ∧
    Monotone binaryTwo ∧
    printedLowerCut binaryTwo (fun _ => 1) 2 (0 : Fin 2) ∧
    lowerValue binaryTwo (fun _ => 1) 2 0 = 1/2 ∧
    lowerValue binaryTwo (fun _ => 1) 2 1 = 1/3 ∧
    upperCut binaryTwo (fun _ => 1) 2 (1 : Fin 2) ∧
    upperValue binaryTwo (fun _ => 1) 2 1 = 2/3 ∧
    ((1/2 : ℝ) - 1/3 = 1/6) ∧
    (∀ u v : ℝ, 1 ≤ u → u ≤ 2 → 1 ≤ v → v ≤ 2 →
      1/3 ≤ v/(u+v) ∧ v/(u+v) ≤ 2/3)) ∧
  (attainable binaryTwo (fun _ => 1) (1/2) 1 = Set.Icc (1/3) (2/3) ∧
    (1/3 : ℝ) ∉ Set.Icc (1/2) (2/3)) ∧
  ((∀ ω, 0 ≤ twoProbability ω) ∧ (∑ ω, twoProbability ω) = 1 ∧
    (∀ i, designInclusion twoSample twoProbability i = twoPi i) ∧
    (∑ ω, twoProbability ω * (if twoSample ω = {0,1} then 1 else 0)) = 1/2) ∧
  (∀ {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ), Monotone y →
    ∀ γ : ℝ, 1 ≤ γ →
    printedLowerCut y (fun _ => 1) γ ⟨0,hn⟩ ∧
    lowerValue y (fun _ => 1) γ 0 = populationMean y ∧
    (1 < γ → (∃ i, y ⟨0,hn⟩ < y i) →
      lowerValue y (fun _ => 1) γ 1 < lowerValue y (fun _ => 1) γ 0 ∧
      ¬ IsLeast (normAttainable y (fun _ => 1) γ) (lowerValue y (fun _ => 1) γ 0)))

def T2Statement : Prop :=
  (∀ i, (1/2 : ℝ) ≤ twoPi i ∧ twoPi i ≤ 1) ∧
    StrictMono binaryTwo ∧ populationMean binaryTwo = 1/2 ∧
    printedLowerCut binaryTwo twoPi 2 (0 : Fin 2) ∧
    lowerValue binaryTwo twoPi 2 0 = 2/3 ∧
    lowerValue binaryTwo twoPi 2 1 = 1/2 ∧
    upperValue binaryTwo twoPi 2 1 = 4/5 ∧
    separation binaryTwo twoPi 2 ∧
    (1/2 : ℝ) < 2/3 ∧
    (∀ u v : ℝ, 1 ≤ u → u ≤ 2 → 1 ≤ v → v ≤ 2 →
      1/2 ≤ v/(u/2+v) ∧ v/(u/2+v) ≤ 4/5)

def T10Statement : Prop :=
  (StrictMono fourOutcomes ∧
    lowerCut fourOutcomes (fun _ => 1) 2 (2 : Fin 4) ∧
    lowerValue fourOutcomes (fun _ => 1) 2 2 = 7/6 ∧
    printedLowerExpression fourOutcomes (fun _ => 1) 2 2 = some 1 ∧
    printedLowerCut fourOutcomes (fun _ => 1) 2 (0 : Fin 4) ∧
    printedLowerExpression fourOutcomes (fun _ => 1) 2 0 = none ∧
    (1 : ℝ) ≠ 7/6 ∧
    (∀ w : Fin 4 → ℝ, normBox 2 w → 7/6 ≤ ratio fourOutcomes (fun _ => 1) w)) ∧
  ((∀ ω, 0 ≤ fourClassProbability ω) ∧ (∑ ω, fourClassProbability ω) = 1 ∧
    (∀ i : Fin 6, designInclusion fourClassSample fourClassProbability i =
      (![1/2,1/2,1/2,1/2,1,1] : Fin 6 → ℝ) i) ∧
    (∀ j : Fin 4, designClassTotal fourClassSample fourClassProbability sixTailClass j = 1) ∧
    (∀ j : Fin 4, (Finset.univ.filter (fun i => sixTailClass i = j)).card =
      (![2,2,1,1] : Fin 4 → ℕ) j) ∧
    populationMean sixTailOutcomes = 7/6) ∧
  lowerValue fourOutcomes (fun _ => 1) 2 0 = 3/2 ∧
  lowerValue fourOutcomes (fun _ => 1) 2 1 = 6/5 ∧
  (∀ j : Fin 4,
    ((Finset.univ.filter (fun i => sixTailClass i = j)).card : ℝ) /
      designClassTotal fourClassSample fourClassProbability sixTailClass j =
      lowerWeights 2 2 j)

end
end SAP.P025a
