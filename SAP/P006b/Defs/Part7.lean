import Mathlib
import SAP.P006b.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def T26Statement : Prop :=
  ¬ ∀ {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] [Countable C]
      [MeasurableSingletonClass C] {n : ℕ} (E : Experiment Ω C n),
      Standing E → (∀ x : C, 0 < (E.PX {x}).toReal) →
      PointwiseUnbiased E {π | Admissible π} →
      IsBest {π | Admissible π} E.expectedATO (printedAverageRule E.μ1) ∧
      IsBest {π | Admissible π} E.expectedATT (printedAverageRule E.τ)

def T27Statement : Prop :=
  ¬ ∀ {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n),
      Standing E → ∀ (PiSet : Set (C → ℝ)), (∀ π ∈ PiSet, Admissible π) →
      PointwiseUnbiased E PiSet →
      (∀ π ∈ PiSet, E.expectedTT π = (n : ℝ) * E.V π) ∧
      (∀ π, IsBest PiSet E.expectedTT π ↔ IsBest PiSet E.V π) ∧
      (∀ π, IsBest PiSet E.expectedTT π → regret PiSet E.V π = 0) ∧
      (PiSet = {π | Admissible π} → IsBest PiSet E.expectedTT (positiveRule E.τ))


def T29ExistenceStatement : Prop :=
  ∀ (M : ℝ) (hM : 0 < M),
    ∃ α : ℝ, α < 0 ∧
      IsBest binaryPolicies (rewardP1 (1/2)) (0,1) ∧
      IsBest binaryPolicies
        (binaryWelfare (1/2) (fun x => if x then 1 else -α)) (1,1) ∧
      M < regret binaryPolicies
        (binaryWelfare (1/2) (fun x => if x then 1 else -α)) (0,1)

def T29FamilyStatement : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (p α : ℝ)
    (hp : 0 < p ∧ p < 1) (hα : α < 0),
    (∀ π ∈ binaryPolicies, finiteIIDAverage n p outcomeP1 π =
      emptyFactor n ((1-p)*π.1+p*π.2)*(p*π.2)) ∧
    (2 ≤ n → ∀ π, IsBest binaryPolicies (finiteIIDAverage n p outcomeP1) π ↔
      π = (0,1)) ∧
    (n = 1 → ∀ π, IsBest binaryPolicies (finiteIIDAverage n p outcomeP1) π ↔
      binaryFeasible π ∧ π.2 = 1) ∧
    IsBest binaryPolicies
      (binaryWelfare p (fun x => if x then 1 else -α)) (1,1) ∧
    bestValue binaryPolicies (binaryWelfare p (fun x => if x then 1 else -α)) =
      -α*(1-p)+p ∧
    regret binaryPolicies (binaryWelfare p (fun x => if x then 1 else -α)) (0,1) =
      -α*(1-p)


def T29Statement : Prop :=
  T29ExistenceStatement ∧ T29FamilyStatement ∧
  (∀ p : ℝ, 0 < p → p < 1 →
    Tendsto (fun α : ℝ => -α*(1-p)) atBot atTop) ∧
  (∀ (p α : ℝ), binaryWelfare p (fun x => if x then 1 else -α) (0,1) = p)
  ∧ (∀ p : ℝ, 0 < p → p < 1 →
    Tendsto (fun α : ℝ =>
      regret binaryPolicies (binaryWelfare p (fun x => if x then 1 else -α)) (0,1))
      atBot atTop)


def T30Statement : Prop :=
  IsBest binaryPolicies (oneTT (fun _ => 1) (fun _ _ => 0)) (1,1) ∧
    IsBest binaryPolicies twoTTConstant (1,1) ∧
    bestValue binaryPolicies (oneTT (fun _ => 1) (fun _ _ => 0)) = 1 ∧
    bestValue binaryPolicies twoTTConstant = 2 ∧
    bestValue binaryPolicies (oneTT (fun _ => 1) (fun _ _ => 0)) <
      bestValue binaryPolicies twoTTConstant ∧
    (∀ x : Bool, (1 : ℝ) ≤ 1) ∧ (1 : ℝ) ≤ 1

end
end SAP.P006b
