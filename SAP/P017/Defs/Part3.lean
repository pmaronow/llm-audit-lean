import SAP.P017.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u1 u2 u3 u4 u5

namespace SAP.P017

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

/-- Mathematical statement for P017-T1. -/
def T1Statement : Prop :=
    Measurable ipwEffect ∧ Integrable ipwEffect ipwPopulation ∧
    populationMean ipwPopulation ipwEffect = 1 / 2 ∧
    effectSupport ipwPopulation ipwEffect = Icc 0 1 ∧
    effectRadius ipwPopulation ipwEffect = (1 / 2 : ℝ≥0∞) ∧
    0 < effectRadius ipwPopulation ipwEffect ∧
    pr ipwPopulation {ω | ipwEffect ω = 0} = 0 ∧
    pr ipwPopulation {ω | ipwEffect ω = 1} = 0 ∧
    (∀ᵐ ω ∂ipwPopulation, 0 < ipwEffect ω ∧ ipwEffect ω < 1 ∧ |ipwSummand ω| < 4) ∧
    populationMean ipwPopulation ipwSummand = 1 / 2 ∧
    (∫ ω, ipwSummand ω ^ 2 ∂ipwPopulation) = 14 / 3 ∧
    (∫ ω, (ipwSummand ω - 1 / 2) ^ 2 ∂ipwPopulation) = 53 / 12 ∧
    (∀ n : ℕ, 1 ≤ n →
      populationMean (iidSamples ipwPopulation) (sampleMean ipwSummand n) = 1 / 2 ∧
      (∫ s, (sampleMean ipwSummand n s - 1 / 2) ^ 2 ∂iidSamples ipwPopulation) =
        53 / (12 * (n : ℝ))) ∧
    TendstoInDistribution (fun n s => sqrtN n * (sampleMean ipwSummand n s - 1 / 2))
      atTop (fun x : ℝ => x) (fun _ => iidSamples ipwPopulation)
      (gaussianReal 0 (53 / 12)) ∧
    (∀ w : (ℝ × (ℝ × ℝ)) → ℝ, Measurable w → (∀ ω, 0 ≤ w ω) →
      Integrable w ipwPopulation → 0 < (∫ ω, w ω ∂ipwPopulation) →
      0 < weightedMean ipwPopulation ipwEffect w ∧ weightedMean ipwPopulation ipwEffect w < 1) ∧
    (∀ n : ℕ, 1 ≤ n →
      pr (iidSamples ipwPopulation) (ipwBadEvent (-1) n) = (1 / 4 : ℝ) ^ n ∧
      pr (iidSamples ipwPopulation) (ipwBadEvent 1 n) = (1 / 4 : ℝ) ^ n ∧
      0 < (1 / 4 : ℝ) ^ n ∧ Disjoint (ipwBadEvent (-1) n) (ipwBadEvent 1 n) ∧
      (∀ s ∈ ipwBadEvent (-1) n,
        (∀ i ∈ Finset.range n, ipwSummand (s i) = 2) ∧ sampleMean ipwSummand n s = 2 ∧
        clipTarget (populationMean ipwPopulation ipwEffect) (effectRadius ipwPopulation ipwEffect)
          (sampleMean ipwSummand n s) = 1 ∧
        empiricalObserved ipwObserved n s = Measure.dirac (0, -1) ∧
        ¬ Representable ipwPopulation ipwEffect
          (clipTarget (populationMean ipwPopulation ipwEffect) (effectRadius ipwPopulation ipwEffect)
            (sampleMean ipwSummand n s))) ∧
      (∀ s ∈ ipwBadEvent 1 n,
        (∀ i ∈ Finset.range n, ipwSummand (s i) = -2) ∧ sampleMean ipwSummand n s = -2 ∧
        clipTarget (populationMean ipwPopulation ipwEffect) (effectRadius ipwPopulation ipwEffect)
          (sampleMean ipwSummand n s) = 0 ∧
        empiricalObserved ipwObserved n s = Measure.dirac (0, 1) ∧
        ¬ Representable ipwPopulation ipwEffect
          (clipTarget (populationMean ipwPopulation ipwEffect) (effectRadius ipwPopulation ipwEffect)
            (sampleMean ipwSummand n s))))

/-- Mathematical statement for P017-T2. -/
def T2Statement : Prop :=
    ∀ {Ω : Type u1} [MeasurableSpace Ω] (G : Measure Ω) [IsProbabilityMeasure G]
    (τ : Ω → ℝ) (hτm : Measurable τ) (hτi : Integrable τ G),
    (∀ t : ℝ, Representable G τ t ↔
      0 < pr G {ω | τ ω = t} ∨
        (0 < pr G {ω | τ ω < t} ∧ 0 < pr G {ω | t < τ ω})) ∧
    ((∀ t : ℝ, supportInf (effectSupport G τ) < (t : EReal) →
      (t : EReal) < supportSup (effectSupport G τ) → Representable G τ t) ∧
    (∀ t : ℝ, ((t : EReal) = supportInf (effectSupport G τ) ∨
      (t : EReal) = supportSup (effectSupport G τ)) →
      (Representable G τ t ↔ 0 < pr G {ω | τ ω = t})) ∧
    (∀ t : ℝ, ((t : EReal) < supportInf (effectSupport G τ) ∨
      supportSup (effectSupport G τ) < (t : EReal)) → ¬ Representable G τ t)) ∧
    (∀ t : ℝ, 0 < pr G {ω | τ ω = t} →
      ∃ w, AdmissibleWeight G τ w ∧ (∫ ω, w ω ∂G) = 1 ∧ weightedMean G τ w = t)

/-- Mathematical statement for P017-T3. -/
def T3Statement : Prop :=
    ∀ {Ω : Type u1} {Ξ : Type u2} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G)
    (hc : 0 < effectRadius G τ) (P : Measure Ξ) [IsProbabilityMeasure P]
    (hat : ℕ → Ξ → ℝ) (hhm : ∀ n, Measurable (hat n)),
    ((∀ x : ℝ,
      supportInf (effectSupport G τ) ≤ (clipTarget (populationMean G τ) (effectRadius G τ) x : EReal) ∧
      (clipTarget (populationMean G τ) (effectRadius G τ) x : EReal) ≤ supportSup (effectSupport G τ) ∧
      (Representable G τ (clipTarget (populationMean G τ) (effectRadius G τ) x) ↔
        InteriorOrEndpointAtom G τ (clipTarget (populationMean G τ) (effectRadius G τ) x))) ∧
    (∀ x : ℝ, ENNReal.ofReal |x - populationMean G τ| < effectRadius G τ →
      Representable G τ (clipTarget (populationMean G τ) (effectRadius G τ) x)) ∧
    ((effectRadius G τ = ⊤ ∨
      (∀ t : ℝ, (t = populationMean G τ - (effectRadius G τ).toReal ∨
        t = populationMean G τ + (effectRadius G τ).toReal) →
        ((t : EReal) = supportInf (effectSupport G τ) ∨
          (t : EReal) = supportSup (effectSupport G τ)) → 0 < pr G {ω | τ ω = t})) →
      ∀ x, Representable G τ (clipTarget (populationMean G τ) (effectRadius G τ) x)) ∧
    (RootNNormal P hat (populationMean G τ) →
      Tendsto (fun n => pr P {ω | ENNReal.ofReal |hat n ω - populationMean G τ| < effectRadius G τ})
        atTop (𝓝 1) ∧
      Tendsto (fun n => pr P {ω | Representable G τ
        (clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω))}) atTop (𝓝 1))) ∧
    (∀ x : ℝ, ENNReal.ofReal |x - populationMean G τ| < effectRadius G τ →
      clipTarget (populationMean G τ) (effectRadius G τ) x = x)

/-- Mathematical statement for P017-T4. -/
def T4Statement : Prop :=
    ∀ {Ω : Type u1} [MeasurableSpace Ω] (G : Measure Ω) [IsProbabilityMeasure G]
    (τ : Ω → ℝ) (hτm : Measurable τ) (hτi : Integrable τ G)
    (hc : 0 < effectRadius G τ),
    (∃ d : ℝ, 0 < d ∧ ENNReal.ofReal d < effectRadius G τ) ∧
    (∀ d : ℝ, 0 < d → ENNReal.ofReal d < effectRadius G τ →
      (∀ x : ℝ, Representable G τ (clipReal (populationMean G τ) d x)) ∧
      (∀ x : ℝ, |clipReal (populationMean G τ) d x - populationMean G τ| ≤
        |x - populationMean G τ|) ∧
      (∀ x : ℝ, clipReal (populationMean G τ) d x = x ↔ |x - populationMean G τ| ≤ d) ∧
      (∀ {Ξ : Type u2} [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
        (hat : Ξ → ℝ),
        (∀ η a : ℝ, 0 < η → 0 < a →
          pr P {ω | |hat ω - clipReal (populationMean G τ) d (hat ω)| > η * a} ≤
            pr P {ω | |hat ω - populationMean G τ| > d}) ∧
        (Measurable hat → max
          (supportSup (effectSupport P hat) - (populationMean G τ : EReal))
          ((populationMean G τ : EReal) - supportInf (effectSupport P hat)) ≤ (d : EReal) →
          pr P {ω | hat ω = clipReal (populationMean G τ) d (hat ω)} = 1)) ∧
      (∀ c : ℝ, d < c → ∃ x : ℝ, |x - populationMean G τ| ≤ c ∧
        clipReal (populationMean G τ) c x = x ∧ clipReal (populationMean G τ) d x ≠ x)) ∧
    (effectRadius G τ ≠ ⊤ → 0 < (effectRadius G τ).toReal / 2 ∧
      ENNReal.ofReal ((effectRadius G τ).toReal / 2) < effectRadius G τ) ∧
    (effectRadius G τ = ⊤ → ∀ d : ℝ, 0 < d → ENNReal.ofReal d < effectRadius G τ) ∧
    ((∀ t : ℝ, supportInf (effectSupport G τ) < (t : EReal) →
      (t : EReal) < supportSup (effectSupport G τ) → Representable G τ t) ∧
    (∀ t : ℝ, ((t : EReal) = supportInf (effectSupport G τ) ∨
      (t : EReal) = supportSup (effectSupport G τ)) →
      (Representable G τ t ↔ 0 < pr G {ω | τ ω = t})) ∧
    (∀ t : ℝ, ((t : EReal) < supportInf (effectSupport G τ) ∨
      supportSup (effectSupport G τ) < (t : EReal)) → ¬ Representable G τ t)) ∧
    ((effectRadius G τ = ⊤ ∨
      (∀ t : ℝ, (t = populationMean G τ - (effectRadius G τ).toReal ∨
        t = populationMean G τ + (effectRadius G τ).toReal) →
        ((t : EReal) = supportInf (effectSupport G τ) ∨
          (t : EReal) = supportSup (effectSupport G τ)) → 0 < pr G {ω | τ ω = t})) →
      ∀ x, Representable G τ (clipTarget (populationMean G τ) (effectRadius G τ) x))

end
end SAP.P017
