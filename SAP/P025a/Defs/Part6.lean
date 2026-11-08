import SAP.P025a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a
noncomputable section
open scoped BigOperators

def printedSampleClaim : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : Monotone y) (α β : ℝ) (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1),
    ∃ kL kH : Fin n, printedLowerCut y (fun _ => 1) (β/α) kL ∧
      upperCut y (fun _ => 1) (β/α) kH ∧
      IsLeast (attainable y (fun _ => 1) α β) (lowerValue y (fun _ => 1) (β/α) kL.val) ∧
      IsGreatest (attainable y (fun _ => 1) α β) (upperValue y (fun _ => 1) (β/α) kH.val) ∧
      attainable y (fun _ => 1) α β = Set.Icc
        (lowerValue y (fun _ => 1) (β/α) kL.val) (upperValue y (fun _ => 1) (β/α) kH.val)

def printedClassFormulaClaim : Prop :=
  ∀ {J : ℕ} (hJ : 0 < J) (y mass : Fin J → ℝ)
    (hy : StrictMono y) (hmass : ∀ j, 0 < mass j) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1),
    ∃ kL kH : Fin J, printedLowerCut y mass (β/α) kL ∧ upperCut y mass (β/α) kH ∧
      IsLeast (attainable y mass α β) (lowerValue y mass (β/α) kL.val) ∧
      IsGreatest (attainable y mass α β) (upperValue y mass (β/α) kH.val) ∧
      (∀ x, printedLowerExpression y mass (β/α) kL.val = some x →
        x = lowerEndpoint y mass α β) ∧
      upperEndpoint y mass α β = upperValue y mass (β/α) kH.val

/-- A feasible six-unit, four-outcome counterexample to the printed lower
first-cut optimizer, independent of whether its display has a value. -/
def T8RealizableCounterexample : Prop :=
  (1 : ℝ) < 2 ∧ StrictMono fourOutcomes ∧
  printedLowerCut fourOutcomes (fun _ => 1) 2 (0 : Fin 4) ∧
  lowerValue fourOutcomes (fun _ => 1) 2 0 = 3/2 ∧
  IsLeast (attainable fourOutcomes (fun _ => 1) (1/2) 1) (7/6) ∧
  ¬ IsLeast (attainable fourOutcomes (fun _ => 1) (1/2) 1)
    (lowerValue fourOutcomes (fun _ => 1) 2 0) ∧
  (∀ ω, 0 ≤ fourClassProbability ω) ∧
  (∑ ω, fourClassProbability ω) = 1 ∧
  (∀ i : Fin 6, (1/2 : ℝ) ≤ designInclusion fourClassSample fourClassProbability i ∧
    designInclusion fourClassSample fourClassProbability i ≤ 1) ∧
  (∀ i : Fin 6, sixTailOutcomes i = fourOutcomes (sixTailClass i)) ∧
  (∀ j : Fin 4, designClassTotal fourClassSample fourClassProbability sixTailClass j = 1)

def T7Statement : Prop :=
  (¬ printedSampleClaim) ∧
  (∀ {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : Monotone y) (α β : ℝ) (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1),
    ∃ kH : Fin n, upperCut y (fun _ => 1) (β/α) kH ∧
      IsGreatest (attainable y (fun _ => 1) α β) (upperValue y (fun _ => 1) (β/α) kH.val))

def T8Statement : Prop :=
  (¬ printedClassFormulaClaim) ∧
  T8RealizableCounterexample ∧
  (printedLowerExpression fourOutcomes (fun _ => 1) 2 0 = none) ∧
  (∀ {J : ℕ} (hJ : 0 < J) (y mass : Fin J → ℝ)
    (hy : StrictMono y) (hmass : ∀ j, 0 < mass j) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1),
    ∃ kH : Fin J, upperCut y mass (β/α) kH ∧
      IsGreatest (attainable y mass α β) (upperValue y mass (β/α) kH.val) ∧
      upperEndpoint y mass α β = upperValue y mass (β/α) kH.val)

def T9Statement : Prop :=
  ∀ {J : ℕ} (hJ : 0 < J) (y mass : Fin J → ℝ), StrictMono y →
  (∀ j, 0 < mass j) → ∀ α β : ℝ, 0 < α → α ≤ β → β ≤ 1 →
  (∀ k : ℕ, k ≤ J →
    ratio y mass (fun i => if i.val < k then 1/α else 1/β) =
      lowerNumerator y mass (β/α) k / lowerDenominator mass (β/α) k) ∧
  (∀ k : Fin J, lowerCut y mass (β/α) k →
    lowerEndpoint y mass α β =
      lowerNumerator y mass (β/α) k.val / lowerDenominator mass (β/α) k.val) ∧
  (∀ (k : ℕ) (hk2 : 2 ≤ k) (hkJ : k ≤ J),
    let u : Fin J := ⟨k-2, by omega⟩
    let v : Fin J := ⟨k-1, by omega⟩
    let N := lowerNumerator y mass (β/α) k
    let D := lowerDenominator mass (β/α) k
    printedLowerExpression y mass (β/α) k =
      some ((N+mass u*y u+mass v*y v)/(D+mass u+mass v)) ∧
    (N+mass u*y u+mass v*y v)/(D+mass u+mass v)-N/D =
      (mass u*(y u-N/D)+mass v*(y v-N/D))/(D+mass u+mass v)) ∧
  printedLowerExpression y mass (β/α) 0 = none ∧
  printedLowerExpression y mass (β/α) 1 = none

end
end SAP.P025a
