import Mathlib
import SAP.P006b.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def T23CoreStatement : Prop :=
  (∀ world y0 t r, 0 ≤ missingWorldMass world y0 t r) ∧
    (∀ world, (∑ y0 : Bool, ∑ t : Bool, ∑ r : Bool,
      missingWorldMass world y0 t r) = 1) ∧
    (∀ world y0 t, (∑ r : Bool, missingWorldMass world y0 t r) =
      coinMass (missingWorldPrevalence world) y0 * (1/2 : ℝ)) ∧
    (∀ world, (∑ y0 : Bool, ∑ r : Bool,
      missingWorldMass world y0 false r) = 1/2 ∧
      (∑ y0 : Bool, missingWorldMass world y0 false true) = 1/4) ∧
    (∀ record, missingObservedMass false record = missingObservedMass true record) ∧
    missingWorldMean false = 1/2 ∧ missingWorldMean true = 3/4 ∧
    (∀ world, missingUntreatedObservedMean world = 3/4) ∧
    missingUntreatedObservedMean false - missingWorldMean false = 1/4

def T23Statement : Prop :=
  T23CoreStatement ∧
  missingObservedMass false (false,false,none) = 1/4 ∧
  missingObservedMass false (false,true,some false) = 1/16 ∧
  missingObservedMass false (false,true,some true) = 3/16 ∧
  missingObservedMass false (true,true,some true) = 1/2 ∧
  (∀ world : Bool,
    (∑ y0 : Bool, missingWorldMass world y0 false true) /
      (∑ y0 : Bool, ∑ r : Bool, missingWorldMass world y0 false r) = 1/2)


def T24Statement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (hμ : IsProbabilityMeasure μ)
    (Y0 Y1 : Ω → ℝ) (T R : Ω → Bool)
    (hm : Measurable Y0 ∧ Measurable Y1 ∧ Measurable T ∧ Measurable R)
    (hint : Integrable Y0 μ ∧ Integrable Y1 μ)
    (hI : IndepFun (fun ω => (Y0 ω,Y1 ω)) T μ)
    (hT : 0 < (μ {ω | T ω = false}).toReal)
    (hR : 0 < (μ {ω | T ω = false ∧ R ω = true}).toReal),
    let A := {ω | T ω = false}
    let A1 := {ω | T ω = false ∧ R ω = true}
    let A0 := {ω | T ω = false ∧ R ω = false}
    let Y := fun ω => if T ω then Y1 ω else Y0 ω
    let q := (μ A1).toReal/(μ A).toReal
    (eventMean μ A1 Y0 = eventMean μ A Y0 →
      (∫ ω, Y0 ω ∂μ) = eventMean μ A1 Y) ∧
    (q < 1 →
      (∫ ω, Y0 ω ∂μ) = q*eventMean μ A1 Y0+(1-q)*eventMean μ A0 Y0 ∧
      (eventMean μ A1 Y0 = (∫ ω, Y0 ω ∂μ) ↔
        eventMean μ A1 Y0 = eventMean μ A0 Y0)) ∧
    (IndepFun Y0 R ((μ A)⁻¹ • μ.restrict A) →
      eventMean μ A1 Y0 = eventMean μ A Y0)

def T25FamilyStatement : Prop :=
  ∀ (n : ℕ) (hn : 0 < n)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hβα : β < α),
    (∀ π, (n : ℝ)*lowerBoundReward β 0 π = (n : ℝ)*β*π.1/2) ∧
    (∀ π, IsBest binaryPolicies (fun p => (n : ℝ)*lowerBoundReward β 0 p) π ↔
      binaryFeasible π ∧ π.1 = 1) ∧
    IsBest binaryPolicies (lowerBoundWelfare α β 0) (0,1) ∧
    bestValue binaryPolicies (lowerBoundWelfare α β 0) = α/2 ∧
    (∀ π, IsBest binaryPolicies (fun p => (n : ℝ)*lowerBoundReward β 0 p) π →
      regret binaryPolicies (lowerBoundWelfare α β 0) π = α-β/2-α*π.2/2) ∧
    regret binaryPolicies (lowerBoundWelfare α β 0) (1,0) = α-β/2 ∧
    lowerBoundGamma α = α

def T25ExistenceStatement : Prop :=
  ∀ (n : ℕ) (hn : 0 < n)
    (α ε : ℝ) (hα : 0 < α) (hε : 0 < ε),
    ∃ β : ℝ, 0 < β ∧ β < α ∧
      IsBest binaryPolicies (fun π => (n : ℝ)*lowerBoundReward β 0 π) (1,0) ∧
      regret binaryPolicies (lowerBoundWelfare α β 0) (1,0) ≥ lowerBoundGamma α-ε

def T25UniqueStatement : Prop :=
  ∀ (n : ℕ) (hn : 0 < n)
    (α ε : ℝ) (hα : 0 < α) (hε : 0 < ε),
    ∃ δ : ℝ, 0 < δ ∧ δ < α ∧
      IsBest binaryPolicies (fun π => (n : ℝ)*lowerBoundReward δ δ π) (1,0) ∧
      (∀ π, IsBest binaryPolicies (fun p => (n : ℝ)*lowerBoundReward δ δ p) π →
        π = (1,0) ∧
        regret binaryPolicies (lowerBoundWelfare α δ δ) π =
          α-(δ+δ)/2 ∧
        regret binaryPolicies (lowerBoundWelfare α δ δ) π ≥ lowerBoundGamma α-ε)

/-- Constant public covariate, fair private type, deterministic outcomes and baseline zero. -/
def T25Statement : Prop :=
  T25FamilyStatement ∧ T25ExistenceStatement ∧ T25UniqueStatement ∧
  (∀ (n : ℕ) (β η : ℝ) (π : BinaryPolicy),
    finiteIIDTT n (lowerBoundY1 β η) π = (n : ℝ)*lowerBoundReward β η π) ∧
  (∀ (α β η : ℝ) (π : BinaryPolicy),
    lowerBoundReward β η π = (β*π.1-η*π.2)/2 ∧
    lowerBoundWelfare α β η π = ((β-α)*π.1+(α-η)*π.2)/2 ∧
    (∑ u : Bool, (1/2 : ℝ)*lowerBoundY0 α u) = 0) ∧
  (∀ (β η : ℝ), 0 < β → 0 < η → ∀ π : BinaryPolicy,
    IsBest binaryPolicies (lowerBoundReward β η) π ↔ π = (1,0)) ∧
  (∀ (α β η : ℝ), β < α → η < α →
    IsBest binaryPolicies (lowerBoundWelfare α β η) (0,1) ∧
    bestValue binaryPolicies (lowerBoundWelfare α β η) = (α-η)/2)

end
end SAP.P006b
