import Mathlib
import SAP.P006b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def T16MainStatement : Prop :=
  ∀ {Ω X U : Type} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace U] [Nonempty U] {n : ℕ}
    (E : Experiment Ω (X × U) n) (hS : Standing E)
    (PX : Measure X) (hPX : IsProbabilityMeasure PX)
    (κ : Kernel X U) (hκ : IsMarkovKernel κ) (hjoint : E.PX = PX.compProd κ)
    (PiSet : Set ((X × U) → ℝ)) (hπ : ∀ π ∈ PiSet, Admissible π)
    (hq : ∀ π ∈ PiSet, ∀ᵐ x ∂PX, 0 < untreatedProbability κ π x)
    (hcond : ∀ᵐ x ∂PX, Integrable (fun u => E.μ0 (x,u)) (κ x))
    (hminmax : ∀ x, ∃ umin umax, ∀ u, E.μ0 (x,umin) ≤ E.μ0 (x,u) ∧
      E.μ0 (x,u) ≤ E.μ0 (x,umax))
    (hmax : ∀ c : X × U, ∃ v, ∀ u, |E.μ0 c-E.μ0 (c.1,u)| ≤
      |E.μ0 c-E.μ0 (c.1,v)|)
    (hest : ∀ π ∈ PiSet, ∀ ω c, E.μhat π ω c = selectedBaseline κ E.μ0 π c.1)
    (γ : ℝ) (hint : Integrable (maximumDeviation E.μ0) E.PX)
    (hγ : (∫ c, maximumDeviation E.μ0 c ∂E.PX) ≤ γ)
    (b s : (X × U) → ℝ) (hb : IsBest PiSet E.expectedTT b) (hs : IsBest PiSet E.V s),
    (∀ π ∈ PiSet,
      (∀ᵐ x ∂PX, IsProbabilityMeasure (untreatedConditionalLaw κ π x) ∧
        selectedBaseline κ E.μ0 π x =
          (∫ u, E.μ0 (x,u) ∂untreatedConditionalLaw κ π x) ∧
        sInf (Set.range (fun u => E.μ0 (x,u))) ≤ selectedBaseline κ E.μ0 π x ∧
        selectedBaseline κ E.μ0 π x ≤ sSup (Set.range (fun u => E.μ0 (x,u))) ∧
        ∀ u, |selectedBaseline κ E.μ0 π x-E.μ0 (x,u)| ≤
          maximumDeviation E.μ0 (x,u)) ∧
      normalizedTT E π = (∫ c, π c*(E.μ1 c-selectedBaseline κ E.μ0 π c.1) ∂E.PX) ∧
      |normalizedTT E π-E.V π| ≤
        (∫ c, |selectedBaseline κ E.μ0 π c.1-E.μ0 c| ∂E.PX) ∧
      (∫ c, |selectedBaseline κ E.μ0 π c.1-E.μ0 c| ∂E.PX) ≤
        (∫ c, maximumDeviation E.μ0 c ∂E.PX) ∧
      (∫ c, |selectedBaseline κ E.μ0 π c.1-E.μ0 c| ∂E.PX) ≤ γ ∧
      |normalizedTT E π-E.V π| ≤ γ) ∧
    regret PiSet E.V b = E.V s-E.V b ∧ regret PiSet E.V b ≤ 2*γ

def T16PositivityStatement : Prop :=
  ∀ {X U : Type} [MeasurableSpace X]
    [MeasurableSpace U] (κ : Kernel X U) (hκ : IsMarkovKernel κ)
    (π : (X × U) → ℝ) (hπ : Admissible π) (hlt : ∀ c, π c < 1),
    (∀ x, 0 < untreatedProbability κ π x) ∧
    (∀ b0 : X → ℝ, ∀ x,
      selectedBaseline κ (fun c => b0 c.1) π x = b0 x)

def T17SelectionStatement : Prop :=
  ∀ {K : ℕ} (p m : Fin K → ℝ) (hp : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) (j : Fin K),
    finiteMass p (fun i => 1-leaveOnlyType j i) = p j ∧
    finiteSelectedBaseline p m (leaveOnlyType j) = m j ∧
    ((∃ i : Fin K, i ≠ j) →
      0 < finiteMass p (fun i => 1-treatOnlyType j i) ∧
      finiteSelectedBaseline p m (treatOnlyType j) =
        (∑ i, if i = j then 0 else p i*m i) /
        (∑ i, if i = j then 0 else p i))

def T17ExampleStatement : Prop :=
  finiteSelectedBaseline (fun _ : Fin 3 => 1/3) ![0,1,3]
      (treatOnlyType 0) = 2 ∧
    finiteSelectedBaseline (fun _ : Fin 3 => 1/3) ![0,1,3]
      (leaveOnlyType 0) = 0 ∧ (2 : ℝ) ≠ 0

def T18Statement : Prop :=
  IsBest binaryPolicies (rewardP1 (1/2)) (0,1) ∧
    rewardP1 (1/2) (0,1) = 3/4 ∧
    IsBest binaryPolicies (binaryWelfare (1/2) (effectP1 4)) (1,0) ∧
    regret binaryPolicies (binaryWelfare (1/2) (effectP1 4)) (0,1) = 2 ∧
    (1 - (1/2 : ℝ)*4) = -1 ∧ (2 : ℝ) ≠ -1

def T19CoreStatement : Prop :=
  ∀ (p β : ℝ) (hp : 0 < p ∧ p < 1) (hβ : 1 < β),
    IsBest binaryPolicies (binaryWelfare p (effectP1 β)) (1,0) ∧
    bestValue binaryPolicies (binaryWelfare p (effectP1 β)) = 1-p ∧
    binaryWelfare p (effectP1 β) (0,1) = p*(1-β) ∧
    regret binaryPolicies (binaryWelfare p (effectP1 β)) (0,1) = 1-2*p+p*β ∧
    (1-2*p+p*β) - (1-p*β) = 2*p*(β-1) ∧ 0 < 2*p*(β-1)

def T20CoreStatement : Prop :=
  (∀ y0 y1, 0 ≤ logisticWitnessMass y0 y1) ∧
    (∑ y0 : Bool, ∑ y1 : Bool, logisticWitnessMass y0 y1) = 1 ∧
    (∑ y0 : Bool, ∑ y1 : Bool,
      logisticWitnessMass y0 y1 * bit y0) = 1/2 ∧
    (∑ y0 : Bool, ∑ y1 : Bool,
      logisticWitnessMass y0 y1 * bit y1) = 1/4 ∧
    logistic 0 = 1/2 ∧ logistic (-Real.log 3) = 1/4 ∧
    (∑ y0 : Bool, ∑ y1 : Bool,
      logisticWitnessMass y0 y1 * signedOutcome y0) = 0 ∧
    (∑ y0 : Bool, ∑ y1 : Bool,
      logisticWitnessMass y0 y1 * signedOutcome y1) = -1/2 ∧
    (if 0 < (-1/2 : ℝ) then (1 : ℝ) else 0) = 0 ∧
    (if 0 < logistic (-Real.log 3) then (1 : ℝ) else 0) = 1

def T21CoreStatement : Prop :=
  ∀ {d : ℕ} (β : LogisticFit d) (x : Fin d → ℝ),
    (∀ t, signedBernoulliMean (logistic (linearPredictor β x t)) =
        2*logistic (linearPredictor β x t)-1) ∧
    signedBernoulliMean (logistic (linearPredictor β x true)) -
      signedBernoulliMean (logistic (linearPredictor β x false)) =
        2*(logistic (linearPredictor β x true)-logistic (linearPredictor β x false)) ∧
    (∀ z : ℝ, 2*logistic z-1 ≠ logistic z)

def T22CoreStatement : Prop :=
  ∀ {C : Type} [DecidableEq C] {n : ℕ}
    (X : Fin n → C) (m : Fin n → ℝ) (hn : 0 < n),
    (∀ x, (empiricalGroup X x).Nonempty →
      (∀ l h : ℝ, (∀ i ∈ empiricalGroup X x, l ≤ m i ∧ m i ≤ h) →
        l ≤ empiricalMean X m x ∧ empiricalMean X m x ≤ h) ∧
      (∑ i ∈ empiricalGroup X x, (m i-empiricalMean X m x)) = 0) ∧
    (∑ i, empiricalMean X m (X i))/n = (∑ i, m i)/n

def T22ExampleStatement : Prop :=
  empiricalMean (fun _ : Fin 2 => (0:ℕ)) ![1,3] 0 = 2 ∧
    ((1+3 : ℝ)/1) = 4

/-- Full information: identify the population baseline at each stratum with untreated mass. -/
def FullInformationStatement : Prop :=
  ∀ {X U : Type} [MeasurableSpace X] [MeasurableSpace U]
    (κ : Kernel X U) [IsMarkovKernel κ] (p b0 : X → ℝ) (x : X), p x < 1 →
    selectedBaseline κ (fun c => b0 c.1) (fun c => p c.1) x = b0 x

def T16Statement : Prop :=
  T16MainStatement ∧ T16PositivityStatement ∧ FullInformationStatement

def T17Statement : Prop := T17SelectionStatement ∧ T17ExampleStatement

def T19Statement : Prop :=
  T19CoreStatement ∧
  (∀ p : ℝ, 0 < p → p < 1 →
    Tendsto (fun β : ℝ => 1-2*p+p*β) atTop atTop) ∧
  (∀ (p β : ℝ) (π : BinaryPolicy),
    effectP1 β false = 1 ∧ effectP1 β true = 1-β ∧
    binaryWelfare p (effectP1 β) π = (1-p)*π.1+p*(1-β)*π.2) ∧
  (∀ m : ℝ, 1/2 < m →
    regret binaryPolicies (binaryWelfare (1/2) (effectP1 (2*m))) (0,1) = m) ∧
  (∀ β : ℝ, 1 < β → effectP1 β true < 0) ∧
  (∀ p β : ℝ, binaryWelfare p (effectP1 β) (1,0) = 1-p ∧
    (1-p)-p*(1-β) = 1-2*p+p*β) ∧
  (∀ p : ℝ, 0 < p → p < 1 →
    Tendsto (fun β : ℝ => regret binaryPolicies (binaryWelfare p (effectP1 β)) (0,1))
      atTop atTop)

def T20Statement : Prop :=
  T20CoreStatement ∧
  (logistic 0 ≠ (0 : ℝ)) ∧ (logistic (-Real.log 3) ≠ (-1/2 : ℝ)) ∧
  ((-1/2 : ℝ)-0 = -1/2) ∧
  (logistic (-Real.log 3)-logistic 0 = -1/4)

def T21Statement : Prop :=
  T21CoreStatement ∧ (∀ z : ℝ, 0 < logistic z ∧ logistic z < 1) ∧
  (∀ z : ℝ, signedBernoulliMean (logistic z) =
    1*logistic z+(-1)*(1-logistic z))

def T22Statement : Prop :=
  T22CoreStatement ∧ T22ExampleStatement ∧
  (∀ {C : Type} [DecidableEq C] {n : ℕ} (X : Fin n → C) (m : Fin n → ℝ),
    0 < n → empiricalGamma X m = (∑ i, |empiricalMean X m (X i)-m i|)/n)

end
end SAP.P006b
