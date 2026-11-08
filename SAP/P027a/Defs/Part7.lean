import Mathlib
import SAP.P027a.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

def PeriodicCorrectionClaim : Prop :=
  ∀ (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
  (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ), (∑ k, z k) = 0 →
let D := phaseOriginal r m hr
    let Dc := phaseGrouped r hr
    let Y := groupTotal (fun _ : Fin r × Fin 2 => m) z
    let Qg := groupSquares (fun _ : Fin r × Fin 2 => m) z
    let S := ∑ g, Y g^2
    let Q := ∑ g, Qg g
    let q : ℝ := 2*r
    let N : ℝ := m*q
    let V := variance D (htTotal D z)
    let H := expect D (htVarianceEstimator D z)
    let Uc := expect D (c2Estimator D z)
    let Gc := expect Dc (c2Estimator Dc Y)
    (∑ g, Y g) = 0 ∧
    biasA D z = -S ∧ 0 ≤ S ∧ (S = 0 ↔ ∀ g, Y g = 0) ∧
    expect D (htTotal D z) = 0 ∧ V = ∑ g, Y g^2 / phaseProb r g ∧
    H = V-S ∧ Uc = V-S+(N-m)*Q ∧ Gc = V+(q-2)*S ∧
    (∀ g, htTotal D z g = Y g / phaseProb r g ∧
      htVarianceEstimator D z g = (1-phaseProb r g)*Y g^2/(phaseProb r g)^2 ∧
      quadraticCorrection D z g = (N-m)*Qg g / phaseProb r g ∧
      quadraticCorrection Dc Y g = (q-1)*Y g^2 / phaseProb r g ∧
      c2Estimator D z g - c2Estimator Dc Y g =
        (q-1)/phaseProb r g * ((m:ℝ)*Qg g - Y g^2) ∧
      c2Estimator D z g - c2Estimator Dc Y g =
        (m:ℝ)*(q-1)/phaseProb r g *
          (∑ j : Fin m, (z ⟨g,j⟩-Y g/(m:ℝ))^2) ∧
      0 ≤ c2Estimator D z g - c2Estimator Dc Y g) ∧
    Uc - Gc = (q-1)*((m:ℝ)*Q-S) ∧ V ≤ Gc ∧ Gc ≤ Uc ∧
    (3*q/5)*S ≤ V ∧ V ≤ 3*q*S ∧
    (0 < V → -5/(3*q) ≤ biasA D z/V ∧ biasA D z/V ≤ -1/(3*q) ∧
      (q-2)/(3*q) ≤ (Gc-V)/V ∧ (Gc-V)/V ≤ 5*(q-2)/(3*q))

def PeriodicGroupedOutcome : Prop :=
  ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
  (r m : ℕ) (hr : 0 < r) (hm : 0 < m) (β σ2 : ℝ), 0 ≤ σ2 →
  ∀ (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ), NoiseMoments μ ε σ2 →
  let D := phaseOriginal r m hr
  let Dc := phaseGrouped r hr
  let z := centeredOutcomes phaseSize β ε
  let Y := fun ξ => groupTotal (fun _ : Fin r × Fin 2 => m) (z ξ)
  let q : ℝ := 2*r
  let L := 16*(m:ℝ)^2*β^2+(m:ℝ)*σ2*(1-1/q)
  let V := fun ξ => variance D (htTotal D (z ξ))
  let Gc := fun ξ => expect Dc (c2Estimator Dc (Y ξ))
  (Integrable V μ ∧ Integrable Gc μ ∧ (∀ g, Integrable (fun ξ => Y ξ g^2) μ)) →
  (∀ g, outcomeE μ (fun ξ => Y ξ g^2) = L) ∧
  outcomeE μ V = (9/5)*q^2*L ∧
  outcomeE μ Gc = outcomeE μ V+(q-2)*q*L ∧
  (0 < L → (outcomeE μ Gc-outcomeE μ V)/outcomeE μ V = (5/9)*(1-2/q))

def T6Statement : Prop :=
  PeriodicInclusions ∧ PeriodicCorrectionClaim ∧ PeriodicGroupedOutcome ∧ ((∑ g, ratioExampleTotals g^2) = 2 ∧
    variance groupedPeriodic4 (htTotal groupedPeriodic4 ratioExampleTotals) = 24 ∧
    expect groupedPeriodic4 (c2Estimator groupedPeriodic4 ratioExampleTotals) = 28 ∧
    (28-24:ℝ)/24 = 1/6)

def Random8Witness : Prop :=
  Valid random8 ∧ Positive random8 ∧
  ((∀ k, 1 ≤ randomSize8 k) ∧
    biasA random8 randomOutcome8 = -16 ∧ quadraticA random8 randomOutcome8 = 48 ∧
    expect random8 (htTotal random8 randomOutcome8) = 0 ∧
    variance random8 (htTotal random8 randomOutcome8) = 256/3 ∧
    expect random8 (htVarianceEstimator random8 randomOutcome8) = 208/3 ∧
    expect random8 (c2Estimator random8 randomOutcome8) = 352/3) ∧
  ((∑ k, randomSize8 k) = 16 ∧
    (∀ k, pi random8 k = printedPPS 2 randomSize8 k) ∧
    variance random8 (htMean random8 randomOutcome8) = 4/3 ∧
    expect random8 (fun ω => htVarianceEstimator random8 randomOutcome8 ω/64) = 13/12 ∧
    expect random8 (fun ω => htVarianceEstimator random8 randomOutcome8 ω/64)-
      variance random8 (htMean random8 randomOutcome8) = -1/4 ∧
    expect random8 (fun ω => htVarianceEstimator random8 randomOutcome8 ω/64) <
      variance random8 (htMean random8 randomOutcome8)) ∧
  (∀ g : Fin 4, htTotal random8 randomOutcome8 g = (if g.val % 2 = 0 then 16 else -16/3) ∧
    htVarianceEstimator random8 randomOutcome8 g =
      (if g.val % 2 = 0 then 224 else 160/9)) ∧
  (∀ (g : Fin 4) (u : ℝ),
    fourLeft 1 3 g ≤ u ∧ u < fourLeft 1 3 g+(if g.val % 2 = 0 then 1 else 3) →
    ∀ k, systematicSelected randomSize8 2 u k ↔ random8.selected g k = true) ∧
  (∀ y : Fin 8 → ℝ, (∀ k, |y k-randomOutcome8 k| < 1/8) → biasA random8 y ≤ -13/4)

def T10Statement : Prop :=
  Random8Witness

def OutcomeAverageConservativity : Prop :=
  ∀ {U Ω Ξ : Type} [Fintype U] [Fintype Ω] [MeasurableSpace Ξ]
  (μ : Measure Ξ) [IsProbabilityMeasure μ] (D : Design U Ω),
  Valid D → Positive D → 0 < Fintype.card U →
  ∀ (x : U → ℝ), (∀ k, 1 ≤ x k) → ∀ (β : ℝ) (ε : U → Ξ → ℝ),
  UncorrelatedNoise μ ε →
  (Integrable (fun ξ => biasA D (rawOutcomes x β ε ξ)) μ ∧
    Integrable (fun ξ => expect D (fun ω =>
      htVarianceEstimator D (rawOutcomes x β ε ξ) ω/(Fintype.card U : ℝ)^2)-
      variance D (htMean D (rawOutcomes x β ε ξ))) μ) →
(∀ k l, k ≠ l → outcomeE μ (fun ξ =>
      rawOutcomes x β ε ξ k * rawOutcomes x β ε ξ l) = β^2*x k*x l) ∧
    outcomeE μ (fun ξ => biasA D (rawOutcomes x β ε ξ)) = β^2*biasA D x ∧
    0 ≤ outcomeE μ (fun ξ => biasA D (rawOutcomes x β ε ξ)) ∧
    outcomeE μ (fun ξ => expect D (fun ω =>
      htVarianceEstimator D (rawOutcomes x β ε ξ) ω/(Fintype.card U : ℝ)^2) -
      variance D (htMean D (rawOutcomes x β ε ξ))) =
      β^2*biasA D x/(Fintype.card U : ℝ)^2 ∧
    0 ≤ outcomeE μ (fun ξ => expect D (fun ω =>
      htVarianceEstimator D (rawOutcomes x β ε ξ) ω/(Fintype.card U : ℝ)^2) -
      variance D (htMean D (rawOutcomes x β ε ξ)))

def T11Statement : Prop :=
  OutcomeAverageConservativity ∧ (biasA random8 randomSize8 = 176 ∧
    (3/2:ℝ)^2 * biasA random8 randomSize8 = 396)
end
end SAP.P027a
