import SAP.P017.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u1 u2 u3 u4 u5

namespace SAP.P017

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

/-- Mathematical statement for P017-T12. -/
def T12Statement : Prop :=
    (∀ (p : ℕ → ℝ)
    (hp : ∀ n : ℕ, 1 ≤ n → 0 < p n ∧ p n ≤ 1) (hplim : Tendsto p atTop (𝓝 0)),
    Measurable slowEffect ∧ Integrable slowEffect slowPopulation ∧
    populationMean slowPopulation slowEffect = 0 ∧
    effectSupport slowPopulation slowEffect = Icc (-1) 1 ∧ effectRadius slowPopulation slowEffect = 1 ∧
    RootNNormal (iidSamples slowPopulation) (rareEstimator p) 0 ∧
    (∀ n : ℕ, 1 ≤ n →
      (iidSamples slowPopulation).map (rareUniform n) = uniformHalfOpen01 ∧
      pr (iidSamples slowPopulation) {s | rareFlag p n s = 1} = p n ∧
      IndepFun (rareFlag p n) (smallNormalMean n) (iidSamples slowPopulation) ∧
      (iidSamples slowPopulation).map (fun s => sqrtN n * smallNormalMean n s) = gaussianReal 0 1 ∧
      (∀ s, sqrtN n * rareEstimator p n s = sqrtN n * smallNormalMean n s + rareRemainder p n s) ∧
      (∀ δ : ℝ, 0 < δ → pr (iidSamples slowPopulation) {s | |rareRemainder p n s| > δ} ≤ 4 / (n : ℝ) + p n) ∧
      {s | rareEstimator p n s ∉ effectSupport slowPopulation slowEffect} = {s | rareFlag p n s = 1} ∧
      {s | |rareEstimator p n s| > 1} = {s | rareFlag p n s = 1} ∧
      {s | rareEstimator p n s ≠ clipReal 0 1 (rareEstimator p n s)} = {s | rareFlag p n s = 1} ∧
      pr (iidSamples slowPopulation) {s | rareEstimator p n s ≠ clipReal 0 1 (rareEstimator p n s)} = p n ∧
      pr (iidSamples slowPopulation) {s | rareEstimator p n s ∈ effectSupport slowPopulation slowEffect} = 1 - p n ∧
      (∀ s, rareFlag p n s = 0 → rareEstimator p n s = smallNormalClip n s ∧
        rareEstimator p n s - clipReal 0 1 (rareEstimator p n s) = 0) ∧
      (∀ s, rareFlag p n s = 1 → (19 / 2 : ℝ) ≤ rareEstimator p n s ∧
        rareEstimator p n s ≤ 21 / 2 ∧ clipReal 0 1 (rareEstimator p n s) = 1 ∧
        rareEstimator p n s - clipReal 0 1 (rareEstimator p n s) = smallNormalClip n s + 9) ∧
      (289 / 4 : ℝ) * p n ≤
        (∫ s, (rareEstimator p n s - clipReal 0 1 (rareEstimator p n s)) ^ 2 ∂iidSamples slowPopulation) ∧
      (∫ s, (rareEstimator p n s - clipReal 0 1 (rareEstimator p n s)) ^ 2 ∂iidSamples slowPopulation) ≤
        (361 / 4 : ℝ) * p n) ∧
    (∀ n : ℕ, 4 ≤ n → (∫ s, rareRemainder p n s ^ 2 ∂iidSamples slowPopulation) ≥
      100 * ((n : ℝ) - 4) * p n) ∧
    LittleOp (iidSamples slowPopulation) (rareRemainder p) (fun _ => 1) ∧
    LittleOp (iidSamples slowPopulation)
      (fun n s => sqrtN n * (rareEstimator p n s - clipReal 0 1 (rareEstimator p n s))) (fun _ => 1)) ∧
    ((∀ n : ℕ, 1 ≤ n → 0 < slowP n ∧ slowP n ≤ 1) ∧ Tendsto slowP atTop (𝓝 0) ∧
    RootNNormal (iidSamples slowPopulation) (rareEstimator slowP) 0 ∧
    Measurable slowEffect ∧ Integrable slowEffect slowPopulation ∧
    populationMean slowPopulation slowEffect = 0 ∧
    effectSupport slowPopulation slowEffect = Icc (-1) 1 ∧ effectRadius slowPopulation slowEffect = 1 ∧
    (∀ n : ℕ, 1 ≤ n → pr (iidSamples slowPopulation)
      {s | rareEstimator slowP n s ≠ clipReal 0 1 (rareEstimator slowP n s)} = slowP n) ∧
    slowP 1000 = 1 / 10 ∧ slowP (10 ^ 12) = 1 / 40 ∧
    (∀ k : ℕ, slowP (2 ^ k) = 1 / ((k + 1 : ℕ) : ℝ)) ∧
    (∀ α : ℝ, 0 < α → Tendsto
      (fun k : ℕ => ((2 ^ k : ℕ) : ℝ) ^ α * slowP (2 ^ k)) atTop atTop) ∧
    (∀ α : ℝ, 0 < α → ¬ ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, slowP n ≤ C / (n : ℝ) ^ α) ∧
    ¬ SmallRemainderMS (iidSamples slowPopulation) (rareRemainder slowP) ∧
    (∀ r : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → 0 < r n) → Tendsto r atTop (𝓝 0) →
      ∃ p : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → 0 < p n ∧ p n ≤ 1) ∧ Tendsto p atTop (𝓝 0) ∧
        RootNNormal (iidSamples slowPopulation) (rareEstimator p) 0 ∧
        (∀ n : ℕ, 1 ≤ n → pr (iidSamples slowPopulation)
          {s | rareEstimator p n s ≠ clipReal 0 1 (rareEstimator p n s)} = p n) ∧
        Tendsto (fun n => p n / r n) atTop atTop)) ∧
    (∀ p : ℕ → ℝ, ∀ n : ℕ, 1 ≤ n → ∀ s,
      (-(1 / 2 : ℝ) ≤ smallNormalClip n s ∧ smallNormalClip n s ≤ 1 / 2) ∧
      (rareFlag p n s = 1 →
        (17 / 2 : ℝ) ≤ rareEstimator p n s - clipReal 0 1 (rareEstimator p n s) ∧
        rareEstimator p n s - clipReal 0 1 (rareEstimator p n s) ≤ 19 / 2) ∧
      (|smallNormalMean n s| ≤ 1 / 2 → rareFlag p n s = 0 → rareRemainder p n s = 0)) ∧
    (¬ ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      slowP n ≤ C * (2 * normalCDF (-sqrtN n)))

/-- Mathematical statement for P017-T13.
The usual measure-theoretic conditions are assumed. -/
def T13Statement : Prop :=
    (∀ {Ω : Type u1} {Ξ : Type u2} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hc : 0 < effectRadius G τ)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
    (hhm : ∀ n, Measurable (hat n)) (hh : RootNNormal P hat (populationMean G τ)),
    (∀ n, {ω | inside (populationMean G τ) (effectRadius G τ) (hat n ω)} =
      {ω | hat n ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω)}) ∧
    Tendsto (fun n => pr P {ω | inside (populationMean G τ) (effectRadius G τ) (hat n ω)}) atTop (𝓝 1)) ∧
    (∀ p : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → 0 < p n ∧ p n ≤ 1) →
      Tendsto p atTop (𝓝 0) →
      Measurable slowEffect ∧ Integrable slowEffect slowPopulation ∧
      populationMean slowPopulation slowEffect = 0 ∧
      effectSupport slowPopulation slowEffect = Icc (-1) 1 ∧
      effectRadius slowPopulation slowEffect = 1 ∧
      RootNNormal (iidSamples slowPopulation) (rareEstimator p) 0 ∧
      ∀ n : ℕ, 1 ≤ n →
        pr (iidSamples slowPopulation) {s | |rareEstimator p n s| > 1} = p n ∧
        pr (iidSamples slowPopulation)
          {s | rareEstimator p n s ≠ clipReal 0 1 (rareEstimator p n s)} = p n) ∧
    (∀ {Ξ : Type u3} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (tilde u : Ξ → ℝ)
    (htm : Measurable tilde) (hum : Measurable u) (μ c σ : ℝ)
    (hc : 0 < c) (hσ : 0 < σ) (n : ℕ) (hn : 1 ≤ n)
    (hlaw : P.map tilde = gaussianReal μ ⟨σ ^ 2 / (n : ℝ), by positivity⟩),
    pr P {ω | |tilde ω + u ω - μ| > c} ≤
      2 * normalCDF (-c * sqrtN n / (2 * σ)) + pr P {ω | |u ω| > c / 2})

/-- Mathematical statement for P017-T14. -/
def T14Statement : Prop :=
    ∀ {Ω : Type u1} {Ξ : Type u2} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hc : 0 < effectRadius G τ)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
    (hh : RootNNormal P hat (populationMean G τ)),
    LittleOp P (fun n ω => sqrtN n *
      (hat n ω - clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω))) (fun _ => 1)

/-- Mathematical statement for P017-T15. -/
def T15Statement : Prop :=
    ∀ {Ω : Type u1} {Ξ : Type u2} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hc : 0 < effectRadius G τ)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat Z ε : ℕ → Ξ → ℝ)
    (hhm : ∀ n, Measurable (hat n)) (v : ℝ≥0) (hv : 0 < v)
    (hr : NormalRemainder P hat Z ε (populationMean G τ) v) (he : SmallRemainderMS P ε),
    SmallMSE P (fun n ω => hat n ω - clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω))

/-- Mathematical statement for P017-T16. -/
def T16Statement : Prop :=
    ∀ {Ω : Type u1} {Ξ : Type u2} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
    (hh : RootNNormal P hat (populationMean G τ)),
    (BoundedInProbability P (fun n ω => sqrtN n *
      (clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω) - populationMean G τ))) ∧
    (∀ n ω, |clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω) - populationMean G τ| ≤
      |hat n ω - populationMean G τ|)

end
end SAP.P017
