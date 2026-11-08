import Mathlib
import SAP.P027a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

def PeriodicOutcomeBias : Prop :=
  ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
  (r m : ℕ) (hr : 0 < r) (hm : 0 < m) (β σ2 : ℝ), 0 ≤ σ2 →
  ∀ (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ), NoiseMoments μ ε σ2 →
  let D := phaseOriginal r m hr
  let z := centeredOutcomes phaseSize β ε
  let Y := fun ξ => groupTotal (fun _ : Fin r × Fin 2 => m) (z ξ)
  let q : ℝ := 2*r
  let N : ℝ := m*q
  let L := 16*(m:ℝ)^2*β^2+(m:ℝ)*σ2*(1-1/q)
  let V := fun ξ => variance D (htTotal D (z ξ))
  let H := fun ξ => expect D (htVarianceEstimator D (z ξ))
  (Integrable V μ ∧ Integrable H μ ∧ Integrable (fun ξ => biasA D (z ξ)) μ) →
  (∀ g, Integrable (fun ξ => Y ξ g^2) μ ∧ outcomeE μ (fun ξ => Y ξ g^2) = L) ∧
  outcomeE μ (fun ξ => biasA D (z ξ)) = -q*L ∧
  outcomeE μ V = (9/5)*q^2*L ∧ outcomeE μ H = outcomeE μ V-q*L ∧
  (0 < L → (outcomeE μ H-outcomeE μ V)/outcomeE μ V = -5/(9*q)) ∧
  outcomeE μ (fun ξ => biasA D (z ξ)/N^2) = -16*β^2/q-σ2*(1-1/q)/N

def CalibratedBias : Prop :=
  ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
  (r m : ℕ) (hr : 0 < r) (hm : 0 < m) (ρ β : ℝ), |ρ| ≤ 1 →
  ∀ (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ),
  NoiseMoments μ ε (900*(1-ρ^2)) →
  β^2 = 900*ρ^2*((m:ℝ)*(2*r)-1)/(16*((m:ℝ)*(2*r))) →
  Integrable (fun ξ => biasA (phaseOriginal r m hr)
    (centeredOutcomes phaseSize β ε ξ)/((m:ℝ)*(2*r))^2) μ →
  outcomeE μ (fun ξ => biasA (phaseOriginal r m hr)
    (centeredOutcomes phaseSize β ε ξ)/((m:ℝ)*(2*r))^2) =
      calibratedMeanBias (2*r) ρ ((m:ℝ)*(2*r))

def FixedFractionLimit : Prop :=
  ∀ (r : ℕ), 0 < r → ∀ ρ : ℝ,
  Tendsto (fun m : ℕ => calibratedMeanBias (2*r) ρ (((m:ℝ)+1)*(2*r))) atTop
    (𝓝 (-900*ρ^2/(2*r)))

def T2Statement : Prop :=
  PeriodicStartLaw ∧ PeriodicInclusions ∧ PeriodicBiasClaim ∧ PeriodicOutcomeBias ∧ CalibratedBias ∧ FixedFractionLimit

def ClusterBiasIncrease : Prop :=
  
  variance cluster2 (htTotal cluster2 totalledOnes) = 1 ∧
  (expect cluster3 (c2Estimator cluster3 allOnes3)-variance cluster3 (htTotal cluster3 allOnes3)) = 8 ∧
  (expect cluster2 (c2Estimator cluster2 totalledOnes)-variance cluster2 (htTotal cluster2 totalledOnes)) = 9 ∧
  (expect cluster3 (c2Estimator cluster3 mixed3)-variance cluster3 (htTotal cluster3 mixed3)) = 9/8 ∧
  (expect cluster2 (c2Estimator cluster2 totalledMixed)-variance cluster2 (htTotal cluster2 totalledMixed)) = 49/16

def T3Statement : Prop :=
  ((Positive cluster3 ∧ Positive cluster2 ∧
    (∀ g, indicator cluster3 g 0 = indicator cluster3 g 1) ∧
    (∀ g, htTotal cluster3 allOnes3 g = htTotal cluster2 totalledOnes g) ∧
    variance cluster3 (htTotal cluster3 allOnes3) = 1 ∧
    biasA cluster3 allOnes3 = 4 ∧ quadraticA cluster3 allOnes3 = 4 ∧
    quadraticA cluster2 totalledOnes = 5 ∧
    expect cluster3 (c2Estimator cluster3 allOnes3) = 9 ∧
    expect cluster2 (c2Estimator cluster2 totalledOnes) = 10) ∧
  (variance cluster3 (htTotal cluster3 mixed3) = 81/16 ∧
    variance cluster2 (htTotal cluster2 totalledMixed) = 81/16 ∧
    biasA cluster3 mixed3 = -1 ∧ biasA cluster2 totalledMixed = -1 ∧
    quadraticA cluster3 mixed3 = 17/8 ∧ quadraticA cluster2 totalledMixed = 65/16 ∧
    expect cluster3 (c2Estimator cluster3 mixed3) = 99/16 ∧
    expect cluster2 (c2Estimator cluster2 totalledMixed) = 65/8)) ∧ ClusterBiasIncrease
end
end SAP.P027a
