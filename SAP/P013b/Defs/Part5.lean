import Mathlib
import SAP.P013b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P013b
open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]


def T15Statement : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} (P : Design Ω) (F : Population P N K),
    0 < N → ∀ d e : Fin K, d ≠ e → Positivity F d → Positivity F e →
    ((∀ i j, i ≠ j → 0 < jointPi F i j d e) →
      expectation P (covarianceHT F d e) ≤ covariance P (htTotal F d) (htTotal F e)) ∧
    ((∀ i j, i ≠ j → 0 < jointPi F i j d e) →
      (∀ i, F.outcome i d = F.outcome i e) →
      expectation P (covarianceHT F d e) = covariance P (htTotal F d) (htTotal F e)) ∧
    expectation P (covarianceA F d e) ≤ covariance P (htTotal F d) (htTotal F e) ∧
    variance P (htEffect F d e) ≤ expectation P (effectVariance F d e)


def T16Statement : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} (P : Design Ω) (F : Population P N K),
    0 < N → ∀ d : Fin K, Positivity F d → ∀ g : Fin N → ℝ,
    expectation P (differenceTotal F d g) = potentialTotal F d ∧
    (∀ z, differenceTotal F d g z =
      (∑ i, indicator F.exposure i d z * ((observed F z i - g i) / pi F i d)) +
        ∑ i, g i) ∧
    expectation P (htCount F d) = (N : ℝ) ∧
    |expectation P (hajek F d) - potentialMean F d| ≤
      Real.sqrt (variance P (fun z => htCount F d z / (N : ℝ)) * variance P (hajek F d))


def T17Statement : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} (P : Design Ω) (F : Population P N K),
    0 < N → ∀ (yr : Fin N → Ω → ℝ) (d e : Fin K),
    d ≠ e → Misspecified F yr → Positivity F d → Positivity F e →
    expectation P (htRandomizationTotal F yr d) = conditionalPotentialTotal F yr d ∧
    expectation P (fun z =>
      (htRandomizationTotal F yr d z - htRandomizationTotal F yr e z) / (N : ℝ)) =
      (conditionalPotentialTotal F yr d - conditionalPotentialTotal F yr e) / (N : ℝ)


def T18Statement : Prop :=
  ¬ ∀ S : ExperimentSequence, NestedPopulationSetup S → StandingPositivity S →
    Condition3 S → Condition5Printed S → Condition6 S →
    ∀ α : ℝ, 0 < α → α < 1 → 1 - α ≤ liminf (seqCoverage S α) atTop


def T19Statement : Prop :=
  ∀ S : ExperimentSequence, NestedPopulationSetup S → StandingPositivity S →
    Condition3 S → Condition4 S →
    ConvergesInProbability (seqLaw S) (fun n z => seqEstimate S n z - seqTarget S n) 0

end
end SAP.P013b
