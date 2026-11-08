import SAP.P017.Defs
import AronowAudit.P017.P017_Audit
import AronowAudit.P017.Wave1.Checks.FidP017Contracts
import AronowAudit.P017.Wave1.Gap.GLP017B1
import AronowAudit.P017.Wave1.Gap.GLP017B2
import AronowAudit.P017.Wave1.Gap.GLP017B4
import AronowAudit.P017.Wave1.Gap.GP017B1
import AronowAudit.P017.Wave1.Gap.GP017B1b
import AronowAudit.P017.Wave1.Gap.GP017B2
import AronowAudit.P017.Wave1.Gap.GP017B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u1 u2 u3 u4 u5

namespace SAP.P017.Bridge

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

/-- The SAP statement differs only in names of definitionally equal notions. -/
theorem T12_correspondence : SAP.P017.T12Statement ↔
    ((∀ (p : ℕ → ℝ)
    (hp : ∀ n : ℕ, 1 ≤ n → 0 < p n ∧ p n ≤ 1) (hplim : Tendsto p atTop (𝓝 0)),
    Measurable AronowAudit.P017.slowEffect ∧ Integrable AronowAudit.P017.slowEffect AronowAudit.P017.slowPopulation ∧
    AronowAudit.P017.populationMean AronowAudit.P017.slowPopulation AronowAudit.P017.slowEffect = 0 ∧
    AronowAudit.P017.effectSupport AronowAudit.P017.slowPopulation AronowAudit.P017.slowEffect = Icc (-1) 1 ∧ AronowAudit.P017.effectRadius AronowAudit.P017.slowPopulation AronowAudit.P017.slowEffect = 1 ∧
    AronowAudit.P017.RootNNormal (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation) (AronowAudit.P017.rareEstimator p) 0 ∧
    (∀ n : ℕ, 1 ≤ n →
      (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation).map (AronowAudit.P017.rareUniform n) = AronowAudit.P017.uniformHalfOpen01 ∧
      AronowAudit.P017.pr (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation) {s | AronowAudit.P017.rareFlag p n s = 1} = p n ∧
      IndepFun (AronowAudit.P017.rareFlag p n) (AronowAudit.P017.smallNormalMean n) (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation) ∧
      (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation).map (fun s => AronowAudit.P017.sqrtN n * AronowAudit.P017.smallNormalMean n s) = gaussianReal 0 1 ∧
      (∀ s, AronowAudit.P017.sqrtN n * AronowAudit.P017.rareEstimator p n s = AronowAudit.P017.sqrtN n * AronowAudit.P017.smallNormalMean n s + AronowAudit.P017.rareRemainder p n s) ∧
      (∀ δ : ℝ, 0 < δ → AronowAudit.P017.pr (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation) {s | |AronowAudit.P017.rareRemainder p n s| > δ} ≤ 4 / (n : ℝ) + p n) ∧
      {s | AronowAudit.P017.rareEstimator p n s ∉ AronowAudit.P017.effectSupport AronowAudit.P017.slowPopulation AronowAudit.P017.slowEffect} = {s | AronowAudit.P017.rareFlag p n s = 1} ∧
      {s | |AronowAudit.P017.rareEstimator p n s| > 1} = {s | AronowAudit.P017.rareFlag p n s = 1} ∧
      {s | AronowAudit.P017.rareEstimator p n s ≠ AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.rareEstimator p n s)} = {s | AronowAudit.P017.rareFlag p n s = 1} ∧
      AronowAudit.P017.pr (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation) {s | AronowAudit.P017.rareEstimator p n s ≠ AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.rareEstimator p n s)} = p n ∧
      AronowAudit.P017.pr (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation) {s | AronowAudit.P017.rareEstimator p n s ∈ AronowAudit.P017.effectSupport AronowAudit.P017.slowPopulation AronowAudit.P017.slowEffect} = 1 - p n ∧
      (∀ s, AronowAudit.P017.rareFlag p n s = 0 → AronowAudit.P017.rareEstimator p n s = AronowAudit.P017.smallNormalClip n s ∧
        AronowAudit.P017.rareEstimator p n s - AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.rareEstimator p n s) = 0) ∧
      (∀ s, AronowAudit.P017.rareFlag p n s = 1 → (19 / 2 : ℝ) ≤ AronowAudit.P017.rareEstimator p n s ∧
        AronowAudit.P017.rareEstimator p n s ≤ 21 / 2 ∧ AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.rareEstimator p n s) = 1 ∧
        AronowAudit.P017.rareEstimator p n s - AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.rareEstimator p n s) = AronowAudit.P017.smallNormalClip n s + 9) ∧
      (289 / 4 : ℝ) * p n ≤
        (∫ s, (AronowAudit.P017.rareEstimator p n s - AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.rareEstimator p n s)) ^ 2 ∂AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation) ∧
      (∫ s, (AronowAudit.P017.rareEstimator p n s - AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.rareEstimator p n s)) ^ 2 ∂AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation) ≤
        (361 / 4 : ℝ) * p n) ∧
    (∀ n : ℕ, 4 ≤ n → (∫ s, AronowAudit.P017.rareRemainder p n s ^ 2 ∂AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation) ≥
      100 * ((n : ℝ) - 4) * p n) ∧
    AronowAudit.P017.LittleOp (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation) (AronowAudit.P017.rareRemainder p) (fun _ => 1) ∧
    AronowAudit.P017.LittleOp (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation)
      (fun n s => AronowAudit.P017.sqrtN n * (AronowAudit.P017.rareEstimator p n s - AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.rareEstimator p n s))) (fun _ => 1)) ∧
    ((∀ n : ℕ, 1 ≤ n → 0 < AronowAudit.P017.slowP n ∧ AronowAudit.P017.slowP n ≤ 1) ∧ Tendsto AronowAudit.P017.slowP atTop (𝓝 0) ∧
    AronowAudit.P017.RootNNormal (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation) (AronowAudit.P017.rareEstimator AronowAudit.P017.slowP) 0 ∧
    Measurable AronowAudit.P017.slowEffect ∧ Integrable AronowAudit.P017.slowEffect AronowAudit.P017.slowPopulation ∧
    AronowAudit.P017.populationMean AronowAudit.P017.slowPopulation AronowAudit.P017.slowEffect = 0 ∧
    AronowAudit.P017.effectSupport AronowAudit.P017.slowPopulation AronowAudit.P017.slowEffect = Icc (-1) 1 ∧ AronowAudit.P017.effectRadius AronowAudit.P017.slowPopulation AronowAudit.P017.slowEffect = 1 ∧
    (∀ n : ℕ, 1 ≤ n → AronowAudit.P017.pr (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation)
      {s | AronowAudit.P017.rareEstimator AronowAudit.P017.slowP n s ≠ AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.rareEstimator AronowAudit.P017.slowP n s)} = AronowAudit.P017.slowP n) ∧
    AronowAudit.P017.slowP 1000 = 1 / 10 ∧ AronowAudit.P017.slowP (10 ^ 12) = 1 / 40 ∧
    (∀ k : ℕ, AronowAudit.P017.slowP (2 ^ k) = 1 / ((k + 1 : ℕ) : ℝ)) ∧
    (∀ α : ℝ, 0 < α → Tendsto
      (fun k : ℕ => ((2 ^ k : ℕ) : ℝ) ^ α * AronowAudit.P017.slowP (2 ^ k)) atTop atTop) ∧
    (∀ α : ℝ, 0 < α → ¬ ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, AronowAudit.P017.slowP n ≤ C / (n : ℝ) ^ α) ∧
    ¬ AronowAudit.P017.SmallRemainderMS (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation) (AronowAudit.P017.rareRemainder AronowAudit.P017.slowP) ∧
    (∀ r : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → 0 < r n) → Tendsto r atTop (𝓝 0) →
      ∃ p : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → 0 < p n ∧ p n ≤ 1) ∧ Tendsto p atTop (𝓝 0) ∧
        AronowAudit.P017.RootNNormal (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation) (AronowAudit.P017.rareEstimator p) 0 ∧
        (∀ n : ℕ, 1 ≤ n → AronowAudit.P017.pr (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation)
          {s | AronowAudit.P017.rareEstimator p n s ≠ AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.rareEstimator p n s)} = p n) ∧
        Tendsto (fun n => p n / r n) atTop atTop)) ∧
    (∀ p : ℕ → ℝ, ∀ n : ℕ, 1 ≤ n → ∀ s,
      (-(1 / 2 : ℝ) ≤ AronowAudit.P017.smallNormalClip n s ∧ AronowAudit.P017.smallNormalClip n s ≤ 1 / 2) ∧
      (AronowAudit.P017.rareFlag p n s = 1 →
        (17 / 2 : ℝ) ≤ AronowAudit.P017.rareEstimator p n s - AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.rareEstimator p n s) ∧
        AronowAudit.P017.rareEstimator p n s - AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.rareEstimator p n s) ≤ 19 / 2) ∧
      (|AronowAudit.P017.smallNormalMean n s| ≤ 1 / 2 → AronowAudit.P017.rareFlag p n s = 0 → AronowAudit.P017.rareRemainder p n s = 0)) ∧
    (¬ ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      AronowAudit.P017.slowP n ≤ C * (2 * AronowAudit.P017.normalCDF (-AronowAudit.P017.sqrtN n)))) := Iff.rfl

/-- The SAP statement differs only in names of definitionally equal notions. -/
theorem T13_correspondence : SAP.P017.T13Statement.{u1, u2, u3} ↔
    ((∀ {Ω : Type u1} {Ξ : Type u2} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hc : 0 < AronowAudit.P017.effectRadius G τ)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
    (hhm : ∀ n, Measurable (hat n)) (hh : AronowAudit.P017.RootNNormal P hat (AronowAudit.P017.populationMean G τ)),
    (∀ n, {ω | AronowAudit.P017.inside (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω)} =
      {ω | hat n ω = AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω)}) ∧
    Tendsto (fun n => AronowAudit.P017.pr P {ω | AronowAudit.P017.inside (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω)}) atTop (𝓝 1)) ∧
    (∀ p : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → 0 < p n ∧ p n ≤ 1) →
      Tendsto p atTop (𝓝 0) →
      Measurable AronowAudit.P017.slowEffect ∧ Integrable AronowAudit.P017.slowEffect AronowAudit.P017.slowPopulation ∧
      AronowAudit.P017.populationMean AronowAudit.P017.slowPopulation AronowAudit.P017.slowEffect = 0 ∧
      AronowAudit.P017.effectSupport AronowAudit.P017.slowPopulation AronowAudit.P017.slowEffect = Icc (-1) 1 ∧
      AronowAudit.P017.effectRadius AronowAudit.P017.slowPopulation AronowAudit.P017.slowEffect = 1 ∧
      AronowAudit.P017.RootNNormal (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation) (AronowAudit.P017.rareEstimator p) 0 ∧
      ∀ n : ℕ, 1 ≤ n →
        AronowAudit.P017.pr (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation) {s | |AronowAudit.P017.rareEstimator p n s| > 1} = p n ∧
        AronowAudit.P017.pr (AronowAudit.P017.iidSamples AronowAudit.P017.slowPopulation)
          {s | AronowAudit.P017.rareEstimator p n s ≠ AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.rareEstimator p n s)} = p n) ∧
    (∀ {Ξ : Type u3} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (tilde u : Ξ → ℝ)
    (htm : Measurable tilde) (hum : Measurable u) (μ c σ : ℝ)
    (hc : 0 < c) (hσ : 0 < σ) (n : ℕ) (hn : 1 ≤ n)
    (hlaw : P.map tilde = gaussianReal μ ⟨σ ^ 2 / (n : ℝ), by positivity⟩),
    AronowAudit.P017.pr P {ω | |tilde ω + u ω - μ| > c} ≤
      2 * AronowAudit.P017.normalCDF (-c * AronowAudit.P017.sqrtN n / (2 * σ)) + AronowAudit.P017.pr P {ω | |u ω| > c / 2})) := Iff.rfl

/-- The SAP statement differs only in names of definitionally equal notions. -/
theorem T14_correspondence : SAP.P017.T14Statement.{u1, u2} ↔
    (∀ {Ω : Type u1} {Ξ : Type u2} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hc : 0 < AronowAudit.P017.effectRadius G τ)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
    (hh : AronowAudit.P017.RootNNormal P hat (AronowAudit.P017.populationMean G τ)),
    AronowAudit.P017.LittleOp P (fun n ω => AronowAudit.P017.sqrtN n *
      (hat n ω - AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω))) (fun _ => 1)) := Iff.rfl

/-- The SAP statement differs only in names of definitionally equal notions. -/
theorem T15_correspondence : SAP.P017.T15Statement.{u1, u2} ↔
    (∀ {Ω : Type u1} {Ξ : Type u2} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hc : 0 < AronowAudit.P017.effectRadius G τ)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat Z ε : ℕ → Ξ → ℝ)
    (hhm : ∀ n, Measurable (hat n)) (v : ℝ≥0) (hv : 0 < v)
    (hr : AronowAudit.P017.NormalRemainder P hat Z ε (AronowAudit.P017.populationMean G τ) v) (he : AronowAudit.P017.SmallRemainderMS P ε),
    AronowAudit.P017.SmallMSE P (fun n ω => hat n ω - AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω))) := Iff.rfl

/-- The SAP statement differs only in names of definitionally equal notions. -/
theorem T16_correspondence : SAP.P017.T16Statement.{u1, u2} ↔
    (∀ {Ω : Type u1} {Ξ : Type u2} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
    (hh : AronowAudit.P017.RootNNormal P hat (AronowAudit.P017.populationMean G τ)),
    (AronowAudit.P017.BoundedInProbability P (fun n ω => AronowAudit.P017.sqrtN n *
      (AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω) - AronowAudit.P017.populationMean G τ))) ∧
    (∀ n ω, |AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω) - AronowAudit.P017.populationMean G τ| ≤
      |hat n ω - AronowAudit.P017.populationMean G τ|)) := Iff.rfl

end
end SAP.P017.Bridge
