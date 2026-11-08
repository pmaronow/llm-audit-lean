import SAP.P017.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u1 u2 u3 u4 u5

namespace SAP.P017

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

/-- Mathematical statement for P017-T5. -/
def T5Statement : Prop :=
    Measurable normalEffect ∧ Integrable normalEffect normalPopulation ∧
    populationMean normalPopulation normalEffect = 0 ∧
    effectSupport normalPopulation normalEffect = {-1, 1} ∧ effectRadius normalPopulation normalEffect = 1 ∧
    RootNNormal (iidSamples normalPopulation) shiftedNormalMean 0 ∧
    NormalRemainder (iidSamples normalPopulation) shiftedNormalMean normalZ normalEpsilon 0 1 ∧
    LittleOp (iidSamples normalPopulation) (fun n (_ : ℕ → ℝ × ℝ) => sqrtN n / (n : ℝ)) (fun _ => 1) ∧
    (∀ n : ℕ, 1 ≤ n →
      (iidSamples normalPopulation).map (normalMean n) = gaussianReal 0 ⟨1 / (n : ℝ), by positivity⟩ ∧
      (∀ s, shiftedDifference n s =
        if normalMean n s < -1 - 1 / (n : ℝ) then normalMean n s + 1
        else if normalMean n s ≤ 1 - 1 / (n : ℝ) then -1 / (n : ℝ) else normalMean n s - 1) ∧
      (∀ s, shiftedDifference n s = 0 ↔ normalMean n s = 1) ∧
      pr (iidSamples normalPopulation) {s | shiftedDifference n s ≠ 0} = 1 ∧
      pr (iidSamples normalPopulation) {s | |normalMean n s| > 1} = 2 * normalCDF (-sqrtN n) ∧
      2 * normalCDF (-sqrtN n) < 1 ∧ 2 * normalCDF (-sqrtN n) ≤ 1 / (n : ℝ)) ∧
    (∀ n : ℕ, 2 ≤ n →
      (∀ s, |normalMean n s| ≤ 1 / 2 → shiftedDifference n s = -1 / (n : ℝ) ∧
        shiftedNormalMean n s - clipReal 0 1 (shiftedNormalMean n s) = 0) ∧
      pr (iidSamples normalPopulation) {s | |normalMean n s| ≤ 1 / 2} ≥ 1 - 4 / (n : ℝ) ∧
      pr (iidSamples normalPopulation) {s | |shiftedDifference n s| / (1 / (n : ℝ)) ≥ 1 / 2} ≥ 1 - 4 / (n : ℝ)) ∧
    LittleOp (iidSamples normalPopulation) (fun n s => (n : ℝ) * shiftedDifference n s + 1) (fun _ => 1) ∧
    ¬ LittleOp (iidSamples normalPopulation) shiftedDifference (fun n => 1 / (n : ℝ))

/-- Mathematical statement for P017-T6. -/
def T6Statement : Prop :=
    (Measurable normalEffect ∧ Integrable normalEffect normalPopulation ∧
    populationMean normalPopulation normalEffect = 0 ∧
    effectSupport normalPopulation normalEffect = {-1, 1} ∧ effectRadius normalPopulation normalEffect = 1 ∧
    NormalRemainder (iidSamples normalPopulation) shiftedNormalMean normalZ normalEpsilon 0 1 ∧
    SmallRemainderMS (iidSamples normalPopulation) normalEpsilon ∧
    (∀ n : ℕ, 1 ≤ n → (∫ s, normalEpsilon n s ^ 2 ∂iidSamples normalPopulation) = 1 / (n : ℝ)) ∧
    (∀ s, |normalMean 25 s| ≤ 1 / 2 →
      clipReal 0 1 (shiftedNormalMean 25 s) = shiftedNormalMean 25 s ∧ shiftedDifference 25 s ^ 2 = 1 / 625) ∧
    pr (iidSamples normalPopulation) {s | |normalMean 25 s| ≤ 1 / 2} ≥ 21 / 25 ∧
    (∫ s, shiftedDifference 25 s ^ 2 ∂iidSamples normalPopulation) ≥ 21 / 15625 ∧
    normalTail 25 1 1 =
      (∫ s, if |normalMean 25 s| > 1 then normalMean 25 s ^ 2 else 0 ∂iidSamples normalPopulation) ∧
    normalTail 25 1 1 ≤ (∫ s, normalMean 25 s ^ 6 ∂iidSamples normalPopulation) ∧
    (∫ s, normalMean 25 s ^ 6 ∂iidSamples normalPopulation) = 15 / 15625 ∧
    (∫ s, shiftedDifference 25 s ^ 2 ∂iidSamples normalPopulation) - normalTail 25 1 1 ≥ 6 / 15625 ∧
    (0 : ℝ) < 6 / 15625) ∧
    (∀ s, |normalMean 25 s| ≤ 1 / 2 →
      -(23 / 50 : ℝ) ≤ shiftedNormalMean 25 s ∧ shiftedNormalMean 25 s ≤ 27 / 50) ∧
    SmallMSE (iidSamples normalPopulation)
      (fun n s => shiftedNormalMean n s - clipReal 0 1 (shiftedNormalMean n s)) ∧
    SmallMSE (iidSamples normalPopulation) shiftedDifference

/-- Mathematical statement for P017-T7. -/
def T7Statement : Prop :=
    ∀ {Ω : Type u1} {Ξ : Type u2} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hc : 0 < effectRadius G τ)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
    (hh : RootNNormal P hat (populationMean G τ)),
    (BoundedInProbability P (fun n ω => sqrtN n * (hat n ω - populationMean G τ)) ∧
    Consistent P hat (populationMean G τ) ∧
    (∀ a : ℕ → ℝ, (∀ n, 0 < a n) → LittleOp P
      (fun n ω => hat n ω - clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω)) a) ∧
    (effectRadius G τ = ⊤ → ∀ n ω,
      hat n ω - clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω) = 0)) ∧
    (∀ n ω, inside (populationMean G τ) (effectRadius G τ) (hat n ω) →
      hat n ω - clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω) = 0) ∧
    (∀ n (η a : ℝ), 0 < η → 0 < a →
      {ω | |hat n ω - clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω)| > η * a} ⊆
        {ω | ¬ inside (populationMean G τ) (effectRadius G τ) (hat n ω)} ∧
      pr P {ω | |hat n ω - clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω)| > η * a} ≤
        pr P {ω | ¬ inside (populationMean G τ) (effectRadius G τ) (hat n ω)}) ∧
    Tendsto (fun n => pr P {ω | ¬ inside (populationMean G τ) (effectRadius G τ) (hat n ω)})
      atTop (𝓝 0) ∧
    LittleOp P (fun n ω => sqrtN n *
      (hat n ω - clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω))) (fun _ => 1)

end
end SAP.P017
