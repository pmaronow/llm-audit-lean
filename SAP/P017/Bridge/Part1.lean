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
theorem T1_correspondence : SAP.P017.T1Statement ↔
    (Measurable AronowAudit.P017.ipwEffect ∧ Integrable AronowAudit.P017.ipwEffect AronowAudit.P017.ipwPopulation ∧
    AronowAudit.P017.populationMean AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect = 1 / 2 ∧
    AronowAudit.P017.effectSupport AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect = Icc 0 1 ∧
    AronowAudit.P017.effectRadius AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect = (1 / 2 : ℝ≥0∞) ∧
    0 < AronowAudit.P017.effectRadius AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect ∧
    AronowAudit.P017.pr AronowAudit.P017.ipwPopulation {ω | AronowAudit.P017.ipwEffect ω = 0} = 0 ∧
    AronowAudit.P017.pr AronowAudit.P017.ipwPopulation {ω | AronowAudit.P017.ipwEffect ω = 1} = 0 ∧
    (∀ᵐ ω ∂AronowAudit.P017.ipwPopulation, 0 < AronowAudit.P017.ipwEffect ω ∧ AronowAudit.P017.ipwEffect ω < 1 ∧ |AronowAudit.P017.ipwSummand ω| < 4) ∧
    AronowAudit.P017.populationMean AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwSummand = 1 / 2 ∧
    (∫ ω, AronowAudit.P017.ipwSummand ω ^ 2 ∂AronowAudit.P017.ipwPopulation) = 14 / 3 ∧
    (∫ ω, (AronowAudit.P017.ipwSummand ω - 1 / 2) ^ 2 ∂AronowAudit.P017.ipwPopulation) = 53 / 12 ∧
    (∀ n : ℕ, 1 ≤ n →
      AronowAudit.P017.populationMean (AronowAudit.P017.iidSamples AronowAudit.P017.ipwPopulation) (AronowAudit.P017.sampleMean AronowAudit.P017.ipwSummand n) = 1 / 2 ∧
      (∫ s, (AronowAudit.P017.sampleMean AronowAudit.P017.ipwSummand n s - 1 / 2) ^ 2 ∂AronowAudit.P017.iidSamples AronowAudit.P017.ipwPopulation) =
        53 / (12 * (n : ℝ))) ∧
    TendstoInDistribution (fun n s => AronowAudit.P017.sqrtN n * (AronowAudit.P017.sampleMean AronowAudit.P017.ipwSummand n s - 1 / 2))
      atTop (fun x : ℝ => x) (fun _ => AronowAudit.P017.iidSamples AronowAudit.P017.ipwPopulation)
      (gaussianReal 0 (53 / 12)) ∧
    (∀ w : (ℝ × (ℝ × ℝ)) → ℝ, Measurable w → (∀ ω, 0 ≤ w ω) →
      Integrable w AronowAudit.P017.ipwPopulation → 0 < (∫ ω, w ω ∂AronowAudit.P017.ipwPopulation) →
      0 < AronowAudit.P017.weightedMean AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect w ∧ AronowAudit.P017.weightedMean AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect w < 1) ∧
    (∀ n : ℕ, 1 ≤ n →
      AronowAudit.P017.pr (AronowAudit.P017.iidSamples AronowAudit.P017.ipwPopulation) (AronowAudit.P017.ipwBadEvent (-1) n) = (1 / 4 : ℝ) ^ n ∧
      AronowAudit.P017.pr (AronowAudit.P017.iidSamples AronowAudit.P017.ipwPopulation) (AronowAudit.P017.ipwBadEvent 1 n) = (1 / 4 : ℝ) ^ n ∧
      0 < (1 / 4 : ℝ) ^ n ∧ Disjoint (AronowAudit.P017.ipwBadEvent (-1) n) (AronowAudit.P017.ipwBadEvent 1 n) ∧
      (∀ s ∈ AronowAudit.P017.ipwBadEvent (-1) n,
        (∀ i ∈ Finset.range n, AronowAudit.P017.ipwSummand (s i) = 2) ∧ AronowAudit.P017.sampleMean AronowAudit.P017.ipwSummand n s = 2 ∧
        AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect) (AronowAudit.P017.effectRadius AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect)
          (AronowAudit.P017.sampleMean AronowAudit.P017.ipwSummand n s) = 1 ∧
        AronowAudit.P017.empiricalObserved AronowAudit.P017.ipwObserved n s = Measure.dirac (0, -1) ∧
        ¬ AronowAudit.P017.Representable AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect
          (AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect) (AronowAudit.P017.effectRadius AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect)
            (AronowAudit.P017.sampleMean AronowAudit.P017.ipwSummand n s))) ∧
      (∀ s ∈ AronowAudit.P017.ipwBadEvent 1 n,
        (∀ i ∈ Finset.range n, AronowAudit.P017.ipwSummand (s i) = -2) ∧ AronowAudit.P017.sampleMean AronowAudit.P017.ipwSummand n s = -2 ∧
        AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect) (AronowAudit.P017.effectRadius AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect)
          (AronowAudit.P017.sampleMean AronowAudit.P017.ipwSummand n s) = 0 ∧
        AronowAudit.P017.empiricalObserved AronowAudit.P017.ipwObserved n s = Measure.dirac (0, 1) ∧
        ¬ AronowAudit.P017.Representable AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect
          (AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect) (AronowAudit.P017.effectRadius AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect)
            (AronowAudit.P017.sampleMean AronowAudit.P017.ipwSummand n s))))) := Iff.rfl

/-- The SAP statement differs only in names of definitionally equal notions. -/
theorem T2_correspondence : SAP.P017.T2Statement.{u1} ↔
    (∀ {Ω : Type u1} [MeasurableSpace Ω] (G : Measure Ω) [IsProbabilityMeasure G]
    (τ : Ω → ℝ) (hτm : Measurable τ) (hτi : Integrable τ G),
    (∀ t : ℝ, AronowAudit.P017.Representable G τ t ↔
      0 < AronowAudit.P017.pr G {ω | τ ω = t} ∨
        (0 < AronowAudit.P017.pr G {ω | τ ω < t} ∧ 0 < AronowAudit.P017.pr G {ω | t < τ ω})) ∧
    ((∀ t : ℝ, AronowAudit.P017.supportInf (AronowAudit.P017.effectSupport G τ) < (t : EReal) →
      (t : EReal) < AronowAudit.P017.supportSup (AronowAudit.P017.effectSupport G τ) → AronowAudit.P017.Representable G τ t) ∧
    (∀ t : ℝ, ((t : EReal) = AronowAudit.P017.supportInf (AronowAudit.P017.effectSupport G τ) ∨
      (t : EReal) = AronowAudit.P017.supportSup (AronowAudit.P017.effectSupport G τ)) →
      (AronowAudit.P017.Representable G τ t ↔ 0 < AronowAudit.P017.pr G {ω | τ ω = t})) ∧
    (∀ t : ℝ, ((t : EReal) < AronowAudit.P017.supportInf (AronowAudit.P017.effectSupport G τ) ∨
      AronowAudit.P017.supportSup (AronowAudit.P017.effectSupport G τ) < (t : EReal)) → ¬ AronowAudit.P017.Representable G τ t)) ∧
    (∀ t : ℝ, 0 < AronowAudit.P017.pr G {ω | τ ω = t} →
      ∃ w, AronowAudit.P017.AdmissibleWeight G τ w ∧ (∫ ω, w ω ∂G) = 1 ∧ AronowAudit.P017.weightedMean G τ w = t)) := Iff.rfl

/-- The SAP statement differs only in names of definitionally equal notions. -/
theorem T3_correspondence : SAP.P017.T3Statement.{u1, u2} ↔
    (∀ {Ω : Type u1} {Ξ : Type u2} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G)
    (hc : 0 < AronowAudit.P017.effectRadius G τ) (P : Measure Ξ) [IsProbabilityMeasure P]
    (hat : ℕ → Ξ → ℝ) (hhm : ∀ n, Measurable (hat n)),
    ((∀ x : ℝ,
      AronowAudit.P017.supportInf (AronowAudit.P017.effectSupport G τ) ≤ (AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) x : EReal) ∧
      (AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) x : EReal) ≤ AronowAudit.P017.supportSup (AronowAudit.P017.effectSupport G τ) ∧
      (AronowAudit.P017.Representable G τ (AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) x) ↔
        AronowAudit.P017.InteriorOrEndpointAtom G τ (AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) x))) ∧
    (∀ x : ℝ, ENNReal.ofReal |x - AronowAudit.P017.populationMean G τ| < AronowAudit.P017.effectRadius G τ →
      AronowAudit.P017.Representable G τ (AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) x)) ∧
    ((AronowAudit.P017.effectRadius G τ = ⊤ ∨
      (∀ t : ℝ, (t = AronowAudit.P017.populationMean G τ - (AronowAudit.P017.effectRadius G τ).toReal ∨
        t = AronowAudit.P017.populationMean G τ + (AronowAudit.P017.effectRadius G τ).toReal) →
        ((t : EReal) = AronowAudit.P017.supportInf (AronowAudit.P017.effectSupport G τ) ∨
          (t : EReal) = AronowAudit.P017.supportSup (AronowAudit.P017.effectSupport G τ)) → 0 < AronowAudit.P017.pr G {ω | τ ω = t})) →
      ∀ x, AronowAudit.P017.Representable G τ (AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) x)) ∧
    (AronowAudit.P017.RootNNormal P hat (AronowAudit.P017.populationMean G τ) →
      Tendsto (fun n => AronowAudit.P017.pr P {ω | ENNReal.ofReal |hat n ω - AronowAudit.P017.populationMean G τ| < AronowAudit.P017.effectRadius G τ})
        atTop (𝓝 1) ∧
      Tendsto (fun n => AronowAudit.P017.pr P {ω | AronowAudit.P017.Representable G τ
        (AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n ω))}) atTop (𝓝 1))) ∧
    (∀ x : ℝ, ENNReal.ofReal |x - AronowAudit.P017.populationMean G τ| < AronowAudit.P017.effectRadius G τ →
      AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) x = x)) := Iff.rfl

/-- The SAP statement differs only in names of definitionally equal notions. -/
theorem T4_correspondence : SAP.P017.T4Statement.{u1, u2} ↔
    (∀ {Ω : Type u1} [MeasurableSpace Ω] (G : Measure Ω) [IsProbabilityMeasure G]
    (τ : Ω → ℝ) (hτm : Measurable τ) (hτi : Integrable τ G)
    (hc : 0 < AronowAudit.P017.effectRadius G τ),
    (∃ d : ℝ, 0 < d ∧ ENNReal.ofReal d < AronowAudit.P017.effectRadius G τ) ∧
    (∀ d : ℝ, 0 < d → ENNReal.ofReal d < AronowAudit.P017.effectRadius G τ →
      (∀ x : ℝ, AronowAudit.P017.Representable G τ (AronowAudit.P017.clipReal (AronowAudit.P017.populationMean G τ) d x)) ∧
      (∀ x : ℝ, |AronowAudit.P017.clipReal (AronowAudit.P017.populationMean G τ) d x - AronowAudit.P017.populationMean G τ| ≤
        |x - AronowAudit.P017.populationMean G τ|) ∧
      (∀ x : ℝ, AronowAudit.P017.clipReal (AronowAudit.P017.populationMean G τ) d x = x ↔ |x - AronowAudit.P017.populationMean G τ| ≤ d) ∧
      (∀ {Ξ : Type u2} [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
        (hat : Ξ → ℝ),
        (∀ η a : ℝ, 0 < η → 0 < a →
          AronowAudit.P017.pr P {ω | |hat ω - AronowAudit.P017.clipReal (AronowAudit.P017.populationMean G τ) d (hat ω)| > η * a} ≤
            AronowAudit.P017.pr P {ω | |hat ω - AronowAudit.P017.populationMean G τ| > d}) ∧
        (Measurable hat → max
          (AronowAudit.P017.supportSup (AronowAudit.P017.effectSupport P hat) - (AronowAudit.P017.populationMean G τ : EReal))
          ((AronowAudit.P017.populationMean G τ : EReal) - AronowAudit.P017.supportInf (AronowAudit.P017.effectSupport P hat)) ≤ (d : EReal) →
          AronowAudit.P017.pr P {ω | hat ω = AronowAudit.P017.clipReal (AronowAudit.P017.populationMean G τ) d (hat ω)} = 1)) ∧
      (∀ c : ℝ, d < c → ∃ x : ℝ, |x - AronowAudit.P017.populationMean G τ| ≤ c ∧
        AronowAudit.P017.clipReal (AronowAudit.P017.populationMean G τ) c x = x ∧ AronowAudit.P017.clipReal (AronowAudit.P017.populationMean G τ) d x ≠ x)) ∧
    (AronowAudit.P017.effectRadius G τ ≠ ⊤ → 0 < (AronowAudit.P017.effectRadius G τ).toReal / 2 ∧
      ENNReal.ofReal ((AronowAudit.P017.effectRadius G τ).toReal / 2) < AronowAudit.P017.effectRadius G τ) ∧
    (AronowAudit.P017.effectRadius G τ = ⊤ → ∀ d : ℝ, 0 < d → ENNReal.ofReal d < AronowAudit.P017.effectRadius G τ) ∧
    ((∀ t : ℝ, AronowAudit.P017.supportInf (AronowAudit.P017.effectSupport G τ) < (t : EReal) →
      (t : EReal) < AronowAudit.P017.supportSup (AronowAudit.P017.effectSupport G τ) → AronowAudit.P017.Representable G τ t) ∧
    (∀ t : ℝ, ((t : EReal) = AronowAudit.P017.supportInf (AronowAudit.P017.effectSupport G τ) ∨
      (t : EReal) = AronowAudit.P017.supportSup (AronowAudit.P017.effectSupport G τ)) →
      (AronowAudit.P017.Representable G τ t ↔ 0 < AronowAudit.P017.pr G {ω | τ ω = t})) ∧
    (∀ t : ℝ, ((t : EReal) < AronowAudit.P017.supportInf (AronowAudit.P017.effectSupport G τ) ∨
      AronowAudit.P017.supportSup (AronowAudit.P017.effectSupport G τ) < (t : EReal)) → ¬ AronowAudit.P017.Representable G τ t)) ∧
    ((AronowAudit.P017.effectRadius G τ = ⊤ ∨
      (∀ t : ℝ, (t = AronowAudit.P017.populationMean G τ - (AronowAudit.P017.effectRadius G τ).toReal ∨
        t = AronowAudit.P017.populationMean G τ + (AronowAudit.P017.effectRadius G τ).toReal) →
        ((t : EReal) = AronowAudit.P017.supportInf (AronowAudit.P017.effectSupport G τ) ∨
          (t : EReal) = AronowAudit.P017.supportSup (AronowAudit.P017.effectSupport G τ)) → 0 < AronowAudit.P017.pr G {ω | τ ω = t})) →
      ∀ x, AronowAudit.P017.Representable G τ (AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) x))) := Iff.rfl

end
end SAP.P017.Bridge
