import Mathlib
import SAP.P017.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace SAP.P017

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

/-- The specified normalized atom weight; used only when its atom has positive mass. -/
def atomWeight {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ : Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  {ω | τ ω = t}.indicator (fun _ => 1 / pr G {ω | τ ω = t})

/-- The conditional mean below a threshold, used only with positive lower mass. -/
def lowerMean {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ : Ω → ℝ) (t : ℝ) : ℝ :=
  (∫ ω, {ω | τ ω < t}.indicator τ ω ∂G) / pr G {ω | τ ω < t}

/-- The conditional mean above a threshold, used only with positive upper mass. -/
def upperMean {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ : Ω → ℝ) (t : ℝ) : ℝ :=
  (∫ ω, {ω | t < τ ω}.indicator τ ω ∂G) / pr G {ω | t < τ ω}

/-- The specified mixing coefficient; its denominator is positive in the two-sided branch. -/
def mixtureCoefficient {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ : Ω → ℝ) (t : ℝ) : ℝ :=
  (upperMean G τ t - t) / (upperMean G τ t - lowerMean G τ t)

/-- The specified two-region weight with a supplied mixing coefficient. -/
def twoRegionWeight {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ : Ω → ℝ) (t a : ℝ) : Ω → ℝ :=
  fun ω => (a / pr G {ω | τ ω < t}) * {ω | τ ω < t}.indicator (fun _ => 1) ω +
    ((1 - a) / pr G {ω | t < τ ω}) * {ω | t < τ ω}.indicator (fun _ => 1) ω

/-- P017-T2; the fact cited after Proposition 1, PDF p. 2, corrected.
An admissible weighted mean is attainable exactly at an atom or between positive
masses on both sides, with all interior, endpoint and exterior support consequences.
The prescribed normalized atom indicator and two-region mixture are bounded,
nonnegative, admissible, and have weight mean one and weighted-effect mean equal
to the target; the conditional means straddle the target and the specified
mixing coefficient is strictly between zero and one. -/
def T2WholeStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (G : Measure Ω) [IsProbabilityMeasure G]
    (τ : Ω → ℝ), Measurable τ → Integrable τ G →
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
      AdmissibleWeight G τ (atomWeight G τ t) ∧
      (∀ ω, 0 ≤ atomWeight G τ t ω ∧
        atomWeight G τ t ω ≤ 1 / pr G {ω | τ ω = t}) ∧
      (∫ ω, atomWeight G τ t ω ∂G) = 1 ∧
      (∫ ω, atomWeight G τ t ω * τ ω ∂G) = t) ∧
    (∀ t : ℝ, 0 < pr G {ω | τ ω < t} → 0 < pr G {ω | t < τ ω} →
      lowerMean G τ t < t ∧ t < upperMean G τ t ∧
      0 < upperMean G τ t - lowerMean G τ t ∧
      0 < mixtureCoefficient G τ t ∧ mixtureCoefficient G τ t < 1 ∧
      AdmissibleWeight G τ (twoRegionWeight G τ t (mixtureCoefficient G τ t)) ∧
      (∀ ω, 0 ≤ twoRegionWeight G τ t (mixtureCoefficient G τ t) ω ∧
        twoRegionWeight G τ t (mixtureCoefficient G τ t) ω ≤
          mixtureCoefficient G τ t / pr G {ω | τ ω < t} +
            (1 - mixtureCoefficient G τ t) / pr G {ω | t < τ ω}) ∧
      (∫ ω, twoRegionWeight G τ t (mixtureCoefficient G τ t) ω ∂G) = 1 ∧
      (∫ ω, twoRegionWeight G τ t (mixtureCoefficient G τ t) ω * τ ω ∂G) = t)

/-- P017-T3; Proposition 1 and its gloss, PDF p. 2, corrected.
The original clipped target is representable exactly when strictly between the
effect-support bounds or at a support endpoint with positive mass. A strictly inside estimate equals its
target and satisfies the full chain of clipping and support bounds. Infinite
radius, atoms at binding clipping endpoints, and almost surely finite-valued
effects give representation on every realization. Under root-n asymptotic
normality, both the strictly inside and representation probabilities tend to one. -/
def T3WholeStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (G : Measure Ω) [IsProbabilityMeasure G]
    (τ : Ω → ℝ), Measurable τ → Integrable τ G → 0 < effectRadius G τ →
    (∀ x : ℝ,
      supportInf (effectSupport G τ) ≤
        (clipTarget (populationMean G τ) (effectRadius G τ) x : EReal) ∧
      (clipTarget (populationMean G τ) (effectRadius G τ) x : EReal) ≤
        supportSup (effectSupport G τ) ∧
      (Representable G τ (clipTarget (populationMean G τ) (effectRadius G τ) x) ↔
        InteriorOrEndpointAtom G τ (clipTarget (populationMean G τ) (effectRadius G τ) x))) ∧
    (∀ x : ℝ, ENNReal.ofReal |x - populationMean G τ| < effectRadius G τ →
      clipTarget (populationMean G τ) (effectRadius G τ) x = x ∧
      Representable G τ (clipTarget (populationMean G τ) (effectRadius G τ) x) ∧
      (effectRadius G τ ≠ ⊤ →
        supportInf (effectSupport G τ) ≤
          ((populationMean G τ - (effectRadius G τ).toReal : ℝ) : EReal) ∧
        populationMean G τ - (effectRadius G τ).toReal < x ∧
        x < populationMean G τ + (effectRadius G τ).toReal ∧
        ((populationMean G τ + (effectRadius G τ).toReal : ℝ) : EReal) ≤
          supportSup (effectSupport G τ))) ∧
    (effectRadius G τ = ⊤ →
      supportInf (effectSupport G τ) = ⊥ ∧ supportSup (effectSupport G τ) = ⊤ ∧
      ∀ x, Representable G τ (clipTarget (populationMean G τ) (effectRadius G τ) x)) ∧
    (effectRadius G τ ≠ ⊤ →
      (∀ t : ℝ, (t = populationMean G τ - (effectRadius G τ).toReal ∨
        t = populationMean G τ + (effectRadius G τ).toReal) →
        ((t : EReal) = supportInf (effectSupport G τ) ∨
          (t : EReal) = supportSup (effectSupport G τ)) → 0 < pr G {ω | τ ω = t}) →
      ∀ x, Representable G τ (clipTarget (populationMean G τ) (effectRadius G τ) x)) ∧
    ((∃ S : Finset ℝ, ∀ᵐ ω ∂G, τ ω ∈ S) →
      ∀ x, Representable G τ (clipTarget (populationMean G τ) (effectRadius G τ) x)) ∧
    (∀ {Ξ : Type v} [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
      (hat : ℕ → Ξ → ℝ), (∀ n, 1 ≤ n → Measurable (hat n)) →
      RootNNormal P hat (populationMean G τ) →
      Tendsto (fun n => pr P {ω | ENNReal.ofReal |hat n ω - populationMean G τ| <
        effectRadius G τ}) atTop (𝓝 1) ∧
      Tendsto (fun n => pr P {ω | Representable G τ
        (clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω))}) atTop (𝓝 1))

/-- A positive extension of the reciprocal sample-size rate to the unused index zero. -/
def positiveReciprocal (n : ℕ) : ℝ := if n = 0 then 1 else 1 / (n : ℝ)

/-- The printed claim is false: P017-T14; Proposition 3 and its printed proof,
PDF p. 2. In the admissible shifted-normal example the intermediate error from
the actual target fails a positive-sequence little-o assertion, and its nonzero
probability is one rather than the asserted Gaussian tail. The proposition's
actual root-n error conclusion remains valid under all its original assumptions.
The usual measure-theoretic conditions are assumed. -/
def T14WholeStatement : Prop :=
  T14Statement.{u, v} ∧
  Measurable normalEffect ∧ Integrable normalEffect normalPopulation ∧
  populationMean normalPopulation normalEffect = 0 ∧
  effectSupport normalPopulation normalEffect = {-1, 1} ∧
  effectRadius normalPopulation normalEffect = 1 ∧
  RootNNormal (iidSamples normalPopulation) shiftedNormalMean 0 ∧
  NormalRemainder (iidSamples normalPopulation) shiftedNormalMean normalZ normalEpsilon 0 1 ∧
  LittleOp (iidSamples normalPopulation)
    (fun n (_ : ℕ → ℝ × ℝ) => sqrtN n / (n : ℝ)) (fun _ => 1) ∧
  (∀ n s, shiftedDifference n s = normalMean n s -
    clipTarget (populationMean normalPopulation normalEffect)
      (effectRadius normalPopulation normalEffect) (shiftedNormalMean n s)) ∧
  (∀ n : ℕ, 1 ≤ n →
    (iidSamples normalPopulation).map (normalMean n) =
      gaussianReal 0 ⟨1 / (n : ℝ), by positivity⟩ ∧
    (∀ s, shiftedNormalMean n s = normalMean n s + 1 / (n : ℝ)) ∧
    pr (iidSamples normalPopulation) {s | shiftedDifference n s ≠ 0} = 1 ∧
    2 * normalCDF (-sqrtN n) < 1) ∧
  (∀ n, 0 < positiveReciprocal n) ∧
  ¬ LittleOp (iidSamples normalPopulation) shiftedDifference positiveReciprocal

/-- The printed claim is false: P017-T15; Proposition 4 and its printed proof,
PDF p. 3. The shifted-normal example satisfies the exact Gaussian-plus-remainder
condition and its moment rate, yet has positive intermediate squared error in
the central region at size 25 and an intermediate mean-square error strictly
above the printed Gaussian-tail bound. The proposition's actual mean-square
conclusion remains valid without independence.
The usual measure-theoretic conditions are assumed. -/
def T15WholeStatement : Prop :=
  (∀ {Ω : Type u} {Ξ : Type v} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ),
    Measurable τ → Integrable τ G → 0 < effectRadius G τ →
    ∀ (P : Measure Ξ) [IsProbabilityMeasure P] (hat Z ε : ℕ → Ξ → ℝ),
    (∀ n, 1 ≤ n → Measurable (hat n)) → ∀ (v : ℝ≥0), 0 < v →
    NormalRemainder P hat Z ε (populationMean G τ) v → SmallRemainderMS P ε →
    SmallMSE P (fun n ω => hat n ω -
      clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω))) ∧
  Measurable normalEffect ∧ Integrable normalEffect normalPopulation ∧
  populationMean normalPopulation normalEffect = 0 ∧
  effectSupport normalPopulation normalEffect = {-1, 1} ∧
  effectRadius normalPopulation normalEffect = 1 ∧
  NormalRemainder (iidSamples normalPopulation) shiftedNormalMean normalZ normalEpsilon 0 1 ∧
  SmallRemainderMS (iidSamples normalPopulation) normalEpsilon ∧
  (∀ n : ℕ, 1 ≤ n →
    (∫ s, normalEpsilon n s ^ 2 ∂iidSamples normalPopulation) = 1 / (n : ℝ)) ∧
  (∀ n s, shiftedDifference n s = normalMean n s -
    clipTarget (populationMean normalPopulation normalEffect)
      (effectRadius normalPopulation normalEffect) (shiftedNormalMean n s)) ∧
  (∀ s, |normalMean 25 s| ≤ 1 / 2 →
    clipReal 0 1 (shiftedNormalMean 25 s) = shiftedNormalMean 25 s ∧
      shiftedDifference 25 s ^ 2 = 1 / 625) ∧
  pr (iidSamples normalPopulation) {s | |normalMean 25 s| ≤ 1 / 2} ≥ 21 / 25 ∧
  Integrable (fun s => shiftedDifference 25 s ^ 2) (iidSamples normalPopulation) ∧
  (∫ s, shiftedDifference 25 s ^ 2 ∂iidSamples normalPopulation) - normalTail 25 1 1 ≥
    6 / 15625 ∧ (0 : ℝ) < 6 / 15625

/-- A deterministic consistent sequence whose root-n errors diverge. The index
zero is unused; all sample-size assertions concern n at least one. -/
def slowDet (n : ℕ) (_ : ℝ) : ℝ := (n : ℝ) ^ (-(1 / 4 : ℝ))

/-- The printed claim is false: P017-T7; the corrected argument for Proposition 3,
PDF p. 2. Its final consistency-only assertion includes root-n boundedness in
part (b). In a heterogeneous population with mean zero and radius one, the
measurable deterministic estimator n^(-1/4) is consistent but its root-n errors
are not bounded in probability. The clipping conclusions under the stated
asymptotic-normality assumption remain valid. -/
def T7WholeStatement : Prop :=
  T7Statement.{u, v} ∧
  Measurable normalEffect ∧ Integrable normalEffect normalPopulation ∧
  populationMean normalPopulation normalEffect = 0 ∧
  effectSupport normalPopulation normalEffect = {-1, 1} ∧
  effectRadius normalPopulation normalEffect = 1 ∧
  (∀ n, Measurable (slowDet n)) ∧
  Consistent (Measure.dirac (0 : ℝ)) slowDet (populationMean normalPopulation normalEffect) ∧
  ¬ BoundedInProbability (Measure.dirac (0 : ℝ))
    (fun n ω => sqrtN n * (slowDet n ω - populationMean normalPopulation normalEffect))

end
end SAP.P017
