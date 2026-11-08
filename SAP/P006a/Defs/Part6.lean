import Mathlib
import SAP.P006a.Defs.Part1
import SAP.P006a.Defs.Part2
import SAP.P006a.Defs.Part3
import SAP.P006a.Defs.Part4
import SAP.P006a.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

universe u v
namespace SAP.P006a
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p


/-- P006-T11: the packaged mathematical assertion. -/
def T11Statement : Prop :=
  (∀ {C : Type*} [MeasurableSpace C]
    (PiSet : Set (C → ℝ)) (hπ : ∀ π ∈ PiSet, Admissible π)
    (hz : (fun _ => 0) ∈ PiSet) (reward : OutcomeLaw C → (C → ℝ) → ℝ)
    (hN : NondegenerateReward PiSet reward) (hI : TreatedDataInvariant PiSet reward),
    (∀ M : ℝ, 0 < M →
      ∃ D π, FiniteOutcomeLaw D ∧ IsBest PiSet (reward D) π ∧
        M < regret PiSet (outcomeWelfare D) π) ∧
    (∀ D π, FiniteOutcomeLaw D → IsBest PiSet (reward D) π →
      0 < (∫ z, π z.1 ∂D) → ∀ B : ℝ, 0 < B →
      FiniteOutcomeLaw (shiftedOutcomeLaw D B) ∧
      Measure.map treatedProjection (shiftedOutcomeLaw D B) =
        Measure.map treatedProjection D ∧
      IsBest PiSet (reward (shiftedOutcomeLaw D B)) π ∧
      (∀ π' ∈ PiSet, outcomeWelfare (shiftedOutcomeLaw D B) π' =
        -B*(∫ z, π' z.1 ∂D)) ∧
      bestValue PiSet (outcomeWelfare (shiftedOutcomeLaw D B)) = 0 ∧
      regret PiSet (outcomeWelfare (shiftedOutcomeLaw D B)) π =
        B*(∫ z, π z.1 ∂D) ∧
      (∀ π' ∈ PiSet, outcomeWelfare (shiftedOutcomeLaw D B) π' ≤ 0) ∧
      IsBest PiSet (outcomeWelfare (shiftedOutcomeLaw D B)) (fun _ => 0) ∧
      (∀ M : ℝ, 0 < M →
        0 < (M+1)/(∫ z, π z.1 ∂D) ∧
        M < regret PiSet
          (outcomeWelfare (shiftedOutcomeLaw D ((M+1)/(∫ z, π z.1 ∂D)))) π))) ∧
  (∀ B : ℝ, 0 < B →
    let D : OutcomeLaw Unit := Measure.dirac ((),(1+B,1))
    let P : Set (Unit → ℝ) := {fun _ => 0, fun _ => 1}
    FiniteOutcomeLaw D ∧ NondegenerateReward P (fun _ _ => 0) ∧
    TreatedDataInvariant P (fun _ _ => 0) ∧
    (∀ π ∈ P, IsBest P (fun _ => (0 : ℝ)) π) ∧
    IsBest P (outcomeWelfare D) (fun _ => 0) ∧
    regret P (outcomeWelfare D) (fun _ => 0) = 0 ∧
    regret P (outcomeWelfare D) (fun _ => 1) = B)


/-- P006-T12: the packaged mathematical assertion. -/
def T12Statement : Prop :=
  (intervalLaw Set.univ = 1 ∧ referenceWithAtom Set.univ = 1 ∧
    intervalLaw.support = Set.Icc 0 1 ∧ referenceWithAtom.support = Set.Icc 0 1 ∧
    intervalLaw ≪ referenceWithAtom ∧
    intervalLaw ({1/2} : Set ℝ) = 0 ∧ referenceWithAtom ({1/2} : Set ℝ) = 1/2 ∧
    ¬ referenceWithAtom ≪ intervalLaw ∧
    ¬ ∃ f : ℝ → ℝ≥0∞, Measurable f ∧ referenceWithAtom = intervalLaw.withDensity f) ∧
  (∀ s : Set ℝ, (1/2 : ℝ≥0∞) * intervalLaw s ≤ referenceWithAtom s)


/-- P006-T13: the packaged mathematical assertion. -/
def T13Statement : Prop :=
  ∀ {K : ℕ} {C : Type u} [MeasurableSpace C] {Ω : Fin K → Type v}
    [∀ k, MeasurableSpace (Ω k)]
    (nk : Fin K → ℕ) (E : (k : Fin K) → Experiment (Ω k) C (nk k))
    (P0 : Measure C) (hP0 : IsProbabilityMeasure P0)
    (hD : ∀ k, OutcomeStanding (E k))
    (hmu0 : ∀ j k, (E j).μ0 = (E k).μ0)
    (hac : ∀ k, P0 ≪ (E k).PX)
    (hτ : ∀ k, Integrable (E k).τ P0)
    (hR : ∀ k π, Admissible π → ∀ i,
      Integrable (fun ω => bit ((E k).T π i ω) *
        ((E k).μhat π ω ((E k).X i ω) -
          (E k).μ0 ((E k).X i ω))) ((E k).law π))
    (hU : ∀ k, TreatedUnbiased (E k) (E k).μ0 {π | Admissible π})
    (hreward : ∀ k π, Admissible π → ∀ i,
      Integrable (fun ω => ((E k).observed π ω i -
        (E k).μhat π ω ((E k).X i ω)) * bit ((E k).T π i ω) *
        referenceWeight (nk k) P0 (E k).PX ((E k).X i ω)) ((E k).law π)),
    (∀ k π, Admissible π →
      (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX) π =
        (nk k : ℝ) * (∫ x, (E k).τ x * π x *
          referenceWeight (nk k) P0 (E k).PX x ∂(E k).PX) ∧
      (nk k : ℝ) * (∫ x, (E k).τ x * π x *
          referenceWeight (nk k) P0 (E k).PX x ∂(E k).PX) =
        (∫ x, (E k).τ x * π x ∂P0)) ∧
    (∀ k, IsBest {π | Admissible π}
      ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
      (positiveRule (E k).τ) ∧
      bestValue {π | Admissible π}
        ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX)) =
        (∫ x, positivePart ((E k).τ x) ∂P0)) ∧
    (∀ j k, (∀ x, (E k).τ x ≤ (E j).τ x) →
      (∫ x, positivePart ((E k).τ x) ∂P0) ≤
        (∫ x, positivePart ((E j).τ x) ∂P0)) ∧
    UniformRankPreservation (fun _ => {π | Admissible π})
      (fun k => (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
      (fun k => (E k).τ) ∧
    ((∀ k x, 0 ≤ (E k).τ x) →
      (∀ k, bestValue {π | Admissible π}
        ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX)) =
        (∫ x, (E k).τ x ∂P0)) ∧
      RelativeRankPreservation P0 (fun _ => {π | Admissible π})
        (fun k => (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
        (fun k => (E k).τ))


/-- P006-T14: the packaged mathematical assertion. -/
def T14Statement : Prop :=
  ∀ {C : Type*} [MeasurableSpace C] (P0 : Measure C) (τj τk : C → ℝ),
    (∀ x, τk x ≤ τj x) →
    Integrable (fun x => max (τj x) 0) P0 →
    Integrable (fun x => max (τk x) 0) P0 →
    (∫ x, max (τk x) 0 ∂P0) ≤ (∫ x, max (τj x) 0 ∂P0)


/-- P006-T15: the packaged mathematical assertion. -/
def T15Statement : Prop :=
  ((∀ record, singletonObservedMass 0 1 record = singletonObservedMass 2 1 record) ∧
    (1 : ℝ) > 0 ∧ coinMass 1 false = 0 ∧ (0 : ℝ) ≠ 2 ∧
    (∀ record, binaryObservedMass (fun _ => 0) (fun _ => 1) (1,1/2) record =
      binaryObservedMass (fun x => if x then 0 else 2) (fun _ => 1) (1,1/2) record) ∧
    (∀ x, 0 < binaryRule (1,1/2) x) ∧
    coinMass (binaryRule (1,1/2) false) false = 0 ∧
    (∑ x : Bool, (1/2 : ℝ)*coinMass (binaryRule (1,1/2) x) false) = 1/4 ∧
    binaryObservedMass (fun _ => 0) (fun _ => 1) (1,1/2) (false,true,1) = 1/2 ∧
    binaryObservedMass (fun _ => 0) (fun _ => 1) (1,1/2) (true,true,1) = 1/4 ∧
    binaryObservedMass (fun _ => 0) (fun _ => 1) (1,1/2) (true,false,0) = 1/4) ∧
  (∀ {X : Type*} [MeasurableSpace X]
    (μ0 : (X × Unit) → ℝ) (PX : Measure (X × Unit)),
    (∀ c, maximumDeviation μ0 c = 0) ∧
    (∫ c, maximumDeviation μ0 c ∂PX) = 0) ∧
  (∀ record, singletonObservedMass 0 1 record = if record = (true,1) then 1 else 0)


end
end SAP.P006a
