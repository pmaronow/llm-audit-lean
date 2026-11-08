import SAP.P036.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P036

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- P036-T1: corrected symbol roles and conditional means, unique unadjusted OLS,
and the two exact and rounded coefficient calculations from Table 1 counts. -/
def T1Statement : Prop :=
  (∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (k : ℕ) (peer : Set Ω) (X : Ω → Fin k → ℝ)
      (β₀ β₁ : ℝ) (γ : Fin k → ℝ) (Y ε : Ω → ℝ),
    MeasurableSet peer → Measurable X →
    Integrable ε μ → Integrable (covariateContribution X γ) μ →
    Y =ᵐ[μ] (fun ω => linearPredictor peer X β₀ β₁ γ ω + ε ω) →
    μ[ε | regressorSigma peer X] =ᵐ[μ] (fun _ => 0) →
    μ[Y | regressorSigma peer X] =ᵐ[μ] linearPredictor peer X β₀ β₁ γ) ∧
  (∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (peer : Set Ω) (β₀ β₁ : ℝ) (Y ε : Ω → ℝ),
    MeasurableSet peer → Integrable ε μ →
    Y =ᵐ[μ] (fun ω => β₀ + β₁ * peers peer ω + ε ω) →
    μ[ε | assignmentSigma peer] =ᵐ[μ] (fun _ => 0) →
    0 < μ.real peer → μ.real peer < 1 →
    conditionalArmMean μ peer Y - conditionalArmMean μ peerᶜ Y = β₁ ∧
    conditionalArmMean μ peerᶜ Y = β₀) ∧
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : Finset ι) (Y : ι → ℝ),
    0 < s.card → 0 < sᶜ.card →
    (∀ i, peers (s : Set ι) i = 0 ∨ peers (s : Set ι) i = 1) ∧
    (∑ i, peers (s : Set ι) i) = (s.card : ℝ) ∧
    (∃! b : ℝ × ℝ, ∀ c : ℝ × ℝ, rss s Y b.1 b.2 ≤ rss s Y c.1 c.2) ∧
    (∀ b : ℝ × ℝ,
      (∀ c : ℝ × ℝ, rss s Y b.1 b.2 ≤ rss s Y c.1 c.2) ↔
        b = (armMean sᶜ Y, armMean s Y - armMean sᶜ Y))) ∧
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : Finset ι)
      (Y : ι → ℝ) (k₁ k₀ : ℕ),
    s.card = 94 → sᶜ.card = 95 →
    (∀ i, Y i = 0 ∨ Y i = 1) →
    (∑ i ∈ s, Y i) = (k₁ : ℝ) → (∑ i ∈ sᶜ, Y i) = (k₀ : ℝ) →
    olsCoefficients s Y = tableCoefficients k₁ k₀) ∧
  tableCoefficients 10 10 = ((2 : ℝ) / 19, (1 : ℝ) / 893) ∧
  tableCoefficients 10 7 = ((7 : ℝ) / 95, (146 : ℝ) / 4465) ∧
  roundsToThree (tableCoefficients 10 10).2 (1 / 1000) ∧
  roundsToThree (tableCoefficients 10 10).1 (105 / 1000) ∧
  roundsToThree (tableCoefficients 10 7).2 (33 / 1000) ∧
  roundsToThree (tableCoefficients 10 7).1 (74 / 1000)

/-- P036-T2: the corrected unadjusted HC2 claim, including the assignment-wise
matrix and variance identities, all randomization moments and the equality case,
and the two exact variances and rounded standard errors from Table 1 counts. -/
def T2Statement : Prop :=
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : Finset ι) (Y : ι → ℝ),
    2 ≤ s.card → 2 ≤ sᶜ.card →
    (∀ a b : Fin 2,
      gram s a b = if a = 0 ∧ b = 0 then (Fintype.card ι : ℝ) else (s.card : ℝ)) ∧
    (∀ a b : Fin 2,
      (∑ c, gramInverse s a c * gram s c b) = (if a = b then 1 else 0) ∧
      (∑ c, gram s a c * gramInverse s c b) = (if a = b then 1 else 0)) ∧
    (regressionCoefficient s Y 0, regressionCoefficient s Y 1) =
      (armMean sᶜ Y, armMean s Y - armMean sᶜ Y) ∧
    (∀ i, leverage s i = if i ∈ s then 1 / (s.card : ℝ) else 1 / (sᶜ.card : ℝ)) ∧
    hc2Variance s Y =
      (∑ i ∈ s, (olsResidual s Y i)^2 /
        ((s.card : ℝ)^2 * (1 - 1 / (s.card : ℝ)))) +
      ∑ i ∈ sᶜ, (olsResidual s Y i)^2 /
        ((sᶜ.card : ℝ)^2 * (1 - 1 / (sᶜ.card : ℝ))) ∧
    hc2Variance s Y = sampleVariance s Y / (s.card : ℝ) +
      sampleVariance sᶜ Y / (sᶜ.card : ℝ)) ∧
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n₁ n₀ : ℕ),
    2 ≤ n₁ → 2 ≤ n₀ → n₁ + n₀ = Fintype.card ι → ∀ Y₁ Y₀ : ι → ℝ,
    let E := designExpectation n₁ (fun s => hc2Variance s (observedOutcome s Y₁ Y₀))
    let V := designVariance n₁ (estimatedEffect Y₁ Y₀)
    designExpectation n₁ (estimatedEffect Y₁ Y₀) =
      populationMean Y₁ - populationMean Y₀ ∧
    V = populationVariance Y₁ / (n₁ : ℝ) + populationVariance Y₀ / (n₀ : ℝ) -
      populationVariance (unitEffect Y₁ Y₀) / (Fintype.card ι : ℝ) ∧
    designExpectation n₁ (fun s => sampleVariance s (observedOutcome s Y₁ Y₀)) =
      populationVariance Y₁ ∧
    designExpectation n₁ (fun s => sampleVariance sᶜ (observedOutcome s Y₁ Y₀)) =
      populationVariance Y₀ ∧
    E = populationVariance Y₁ / (n₁ : ℝ) + populationVariance Y₀ / (n₀ : ℝ) ∧
    E - V = populationVariance (unitEffect Y₁ Y₀) / (Fintype.card ι : ℝ) ∧
    0 ≤ populationVariance (unitEffect Y₁ Y₀) / (Fintype.card ι : ℝ) ∧
    V ≤ E ∧
    (E = V ↔ ∃ c : ℝ, ∀ i, unitEffect Y₁ Y₀ i = c)) ∧
  (∀ (ι : Type) (s : Finset ι) (Y : ι → ℝ),
    2 ≤ s.card → ∀ k : ℕ, (∀ i ∈ s, Y i = 0 ∨ Y i = 1) →
    (∑ i ∈ s, Y i) = (k : ℝ) →
    sampleVariance s Y = (k : ℝ) * ((s.card : ℝ) - (k : ℝ)) /
      ((s.card : ℝ) * ((s.card : ℝ) - 1))) ∧
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : Finset ι)
      (Y : ι → ℝ) (k₁ k₀ : ℕ),
    s.card = 94 → sᶜ.card = 95 → (∀ i, Y i = 0 ∨ Y i = 1) →
    (∑ i ∈ s, Y i) = (k₁ : ℝ) → (∑ i ∈ sᶜ, Y i) = (k₀ : ℝ) →
    hc2Variance s Y = tableHC2 k₁ k₀) ∧
  tableHC2 10 10 = (50039 : ℝ) / 24720919 ∧
  tableHC2 10 7 = (1080506 : ℝ) / 618022975 ∧
  roundsToThree (Real.sqrt (tableHC2 10 10)) (45 / 1000) ∧
  roundsToThree (Real.sqrt (tableHC2 10 7)) (42 / 1000)

end

end SAP.P036
