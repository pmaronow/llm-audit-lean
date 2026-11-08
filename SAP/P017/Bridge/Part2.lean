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
theorem T5_correspondence : SAP.P017.T5Statement ↔
    (Measurable AronowAudit.P017.normalEffect ∧ Integrable AronowAudit.P017.normalEffect AronowAudit.P017.normalPopulation ∧
    AronowAudit.P017.populationMean AronowAudit.P017.normalPopulation AronowAudit.P017.normalEffect = 0 ∧
    AronowAudit.P017.effectSupport AronowAudit.P017.normalPopulation AronowAudit.P017.normalEffect = {-1, 1} ∧ AronowAudit.P017.effectRadius AronowAudit.P017.normalPopulation AronowAudit.P017.normalEffect = 1 ∧
    AronowAudit.P017.RootNNormal (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) AronowAudit.P017.shiftedNormalMean 0 ∧
    AronowAudit.P017.NormalRemainder (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) AronowAudit.P017.shiftedNormalMean AronowAudit.P017.normalZ AronowAudit.P017.normalEpsilon 0 1 ∧
    AronowAudit.P017.LittleOp (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) (fun n (_ : ℕ → ℝ × ℝ) => AronowAudit.P017.sqrtN n / (n : ℝ)) (fun _ => 1) ∧
    (∀ n : ℕ, 1 ≤ n →
      (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation).map (AronowAudit.P017.normalMean n) = gaussianReal 0 ⟨1 / (n : ℝ), by positivity⟩ ∧
      (∀ s, AronowAudit.P017.shiftedDifference n s =
        if AronowAudit.P017.normalMean n s < -1 - 1 / (n : ℝ) then AronowAudit.P017.normalMean n s + 1
        else if AronowAudit.P017.normalMean n s ≤ 1 - 1 / (n : ℝ) then -1 / (n : ℝ) else AronowAudit.P017.normalMean n s - 1) ∧
      (∀ s, AronowAudit.P017.shiftedDifference n s = 0 ↔ AronowAudit.P017.normalMean n s = 1) ∧
      AronowAudit.P017.pr (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) {s | AronowAudit.P017.shiftedDifference n s ≠ 0} = 1 ∧
      AronowAudit.P017.pr (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) {s | |AronowAudit.P017.normalMean n s| > 1} = 2 * AronowAudit.P017.normalCDF (-AronowAudit.P017.sqrtN n) ∧
      2 * AronowAudit.P017.normalCDF (-AronowAudit.P017.sqrtN n) < 1 ∧ 2 * AronowAudit.P017.normalCDF (-AronowAudit.P017.sqrtN n) ≤ 1 / (n : ℝ)) ∧
    (∀ n : ℕ, 2 ≤ n →
      (∀ s, |AronowAudit.P017.normalMean n s| ≤ 1 / 2 → AronowAudit.P017.shiftedDifference n s = -1 / (n : ℝ) ∧
        AronowAudit.P017.shiftedNormalMean n s - AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.shiftedNormalMean n s) = 0) ∧
      AronowAudit.P017.pr (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) {s | |AronowAudit.P017.normalMean n s| ≤ 1 / 2} ≥ 1 - 4 / (n : ℝ) ∧
      AronowAudit.P017.pr (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) {s | |AronowAudit.P017.shiftedDifference n s| / (1 / (n : ℝ)) ≥ 1 / 2} ≥ 1 - 4 / (n : ℝ)) ∧
    AronowAudit.P017.LittleOp (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) (fun n s => (n : ℝ) * AronowAudit.P017.shiftedDifference n s + 1) (fun _ => 1) ∧
    ¬ AronowAudit.P017.LittleOp (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) AronowAudit.P017.shiftedDifference (fun n => 1 / (n : ℝ))) := Iff.rfl

/-- The SAP statement differs only in names of definitionally equal notions. -/
theorem T6_correspondence : SAP.P017.T6Statement ↔
    ((Measurable AronowAudit.P017.normalEffect ∧ Integrable AronowAudit.P017.normalEffect AronowAudit.P017.normalPopulation ∧
    AronowAudit.P017.populationMean AronowAudit.P017.normalPopulation AronowAudit.P017.normalEffect = 0 ∧
    AronowAudit.P017.effectSupport AronowAudit.P017.normalPopulation AronowAudit.P017.normalEffect = {-1, 1} ∧ AronowAudit.P017.effectRadius AronowAudit.P017.normalPopulation AronowAudit.P017.normalEffect = 1 ∧
    AronowAudit.P017.NormalRemainder (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) AronowAudit.P017.shiftedNormalMean AronowAudit.P017.normalZ AronowAudit.P017.normalEpsilon 0 1 ∧
    AronowAudit.P017.SmallRemainderMS (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) AronowAudit.P017.normalEpsilon ∧
    (∀ n : ℕ, 1 ≤ n → (∫ s, AronowAudit.P017.normalEpsilon n s ^ 2 ∂AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) = 1 / (n : ℝ)) ∧
    (∀ s, |AronowAudit.P017.normalMean 25 s| ≤ 1 / 2 →
      AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.shiftedNormalMean 25 s) = AronowAudit.P017.shiftedNormalMean 25 s ∧ AronowAudit.P017.shiftedDifference 25 s ^ 2 = 1 / 625) ∧
    AronowAudit.P017.pr (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) {s | |AronowAudit.P017.normalMean 25 s| ≤ 1 / 2} ≥ 21 / 25 ∧
    (∫ s, AronowAudit.P017.shiftedDifference 25 s ^ 2 ∂AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) ≥ 21 / 15625 ∧
    AronowAudit.P017.normalTail 25 1 1 =
      (∫ s, if |AronowAudit.P017.normalMean 25 s| > 1 then AronowAudit.P017.normalMean 25 s ^ 2 else 0 ∂AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) ∧
    AronowAudit.P017.normalTail 25 1 1 ≤ (∫ s, AronowAudit.P017.normalMean 25 s ^ 6 ∂AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) ∧
    (∫ s, AronowAudit.P017.normalMean 25 s ^ 6 ∂AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) = 15 / 15625 ∧
    (∫ s, AronowAudit.P017.shiftedDifference 25 s ^ 2 ∂AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) - AronowAudit.P017.normalTail 25 1 1 ≥ 6 / 15625 ∧
    (0 : ℝ) < 6 / 15625) ∧
    (∀ s, |AronowAudit.P017.normalMean 25 s| ≤ 1 / 2 →
      -(23 / 50 : ℝ) ≤ AronowAudit.P017.shiftedNormalMean 25 s ∧ AronowAudit.P017.shiftedNormalMean 25 s ≤ 27 / 50) ∧
    AronowAudit.P017.SmallMSE (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation)
      (fun n s => AronowAudit.P017.shiftedNormalMean n s - AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.shiftedNormalMean n s)) ∧
    AronowAudit.P017.SmallMSE (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) AronowAudit.P017.shiftedDifference) := Iff.rfl

/-- The SAP statement differs only in names of definitionally equal notions. -/
theorem T7_correspondence : SAP.P017.T7Statement.{u1, u2} ↔
    (∀ {Ω : Type u1} {Ξ : Type u2} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hc : 0 < AronowAudit.P017.effectRadius G τ)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
    (hh : AronowAudit.P017.RootNNormal P hat (AronowAudit.P017.populationMean G τ)),
    (AronowAudit.P017.BoundedInProbability P (fun n ω => AronowAudit.P017.sqrtN n * (hat n ω - AronowAudit.P017.populationMean G τ)) ∧
    AronowAudit.P017.Consistent P hat (AronowAudit.P017.populationMean G τ) ∧
    (∀ a : ℕ → ℝ, (∀ n, 0 < a n) → AronowAudit.P017.LittleOp P
      (fun n ω => hat n ω - AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω)) a) ∧
    (AronowAudit.P017.effectRadius G τ = ⊤ → ∀ n ω,
      hat n ω - AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω) = 0)) ∧
    (∀ n ω, AronowAudit.P017.inside (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω) →
      hat n ω - AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω) = 0) ∧
    (∀ n (η a : ℝ), 0 < η → 0 < a →
      {ω | |hat n ω - AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω)| > η * a} ⊆
        {ω | ¬ AronowAudit.P017.inside (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω)} ∧
      AronowAudit.P017.pr P {ω | |hat n ω - AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω)| > η * a} ≤
        AronowAudit.P017.pr P {ω | ¬ AronowAudit.P017.inside (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω)}) ∧
    Tendsto (fun n => AronowAudit.P017.pr P {ω | ¬ AronowAudit.P017.inside (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω)})
      atTop (𝓝 0) ∧
    AronowAudit.P017.LittleOp P (fun n ω => AronowAudit.P017.sqrtN n *
      (hat n ω - AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω))) (fun _ => 1)) := Iff.rfl

end
end SAP.P017.Bridge
