import Mathlib
import SAP.P017.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P017

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

/-- The Lebesgue integrand in the corrected normal-tail display. -/
def wholeTailIntegrand (n : ℕ) (σ x : ℝ) : ℝ :=
  x ^ 2 * (sqrtN n / (σ * Real.sqrt (2 * Real.pi))) *
    Real.exp (-(x ^ 2 * (n : ℝ)) / (2 * σ ^ 2))

/-- Extended-radius version of the positive half-tail integral. At infinite radius
the integration set is empty; no conversion of infinity to a real number occurs. -/
def extendedNormalTail (n : ℕ) (c : ℝ≥0∞) (σ : ℝ) : ℝ :=
  2 * ∫ x in {x : ℝ | c < ENNReal.ofReal x}, wholeTailIntegrand n σ x

/-- The explicit sequence used to defeat a prescribed positive vanishing rate. -/
def sqrtFailureRate (r : ℕ → ℝ) (n : ℕ) : ℝ := min 1 (Real.sqrt (r n))

/-- Observed empirical-law functional for the rare-outlier estimator. Only the
observed X and U coordinates enter; it contains no population mean or effect. -/
def rareEmpiricalFunctional (p : ℕ → ℝ) (n : ℕ)
    (F : Measure (ℝ × (ℝ × (ℝ × ℝ)))) : ℝ :=
  clipReal 0 (1 / 2) (∫ z, z.1 ∂F) +
    10 * (if Int.fract ((n : ℝ) * (∫ z, z.2.1 ∂F)) < p n then 1 else 0)

/-- Finite moments and measurability needed to interpret the rare-outlier
construction's expectations, together with its Gaussian central-event bound. -/
def RareFiniteCertificate (p : ℕ → ℝ) (n : ℕ) : Prop :=
  Measurable (rareUniform n) ∧ Measurable (rareFlag p n) ∧
  Measurable (smallNormalMean n) ∧ Measurable (smallNormalClip n) ∧
  Measurable (rareEstimator p n) ∧ Measurable (rareRemainder p n) ∧
  Integrable (fun s => smallNormalMean n s ^ 2) (iidSamples slowPopulation) ∧
  Integrable (fun s => rareRemainder p n s ^ 2) (iidSamples slowPopulation) ∧
  Integrable (fun s =>
    (rareEstimator p n s - clipReal 0 1 (rareEstimator p n s)) ^ 2)
    (iidSamples slowPopulation) ∧
  pr (iidSamples slowPopulation) {s | |smallNormalMean n s| > 1 / 2} ≤ 4 / (n : ℝ)

/-- P017-T11; the normal-tail display in the proof of Proposition 4, PDF p. 3,
corrected. The displayed Lebesgue tail integral equals its closed form, the
truncated second moment of any random variable with the specified Gaussian law,
and the scale-s density/CDF expression. The standardized density integral has
the stated integration-by-parts value. The relevant integrands are integrable,
and the common value decays faster than every positive power of sample size.
At infinite radius the tail set is empty, its integral and truncated moment are
zero, and the same power limits hold.
The usual measure-theoretic conditions are assumed. -/
def T11WholeStatement : Prop :=
  T11Statement ∧
  (Integrable (fun z : ℝ => z ^ 2 * gaussianPDFReal 0 1 z) ∧
    ∀ a : ℝ, 0 < a →
      (∫ z in Ioi a, z ^ 2 * gaussianPDFReal 0 1 z) =
        a * gaussianPDFReal 0 1 a + normalCDF (-a)) ∧
  (∀ (n : ℕ), 1 ≤ n → ∀ c σ : ℝ, 0 < c → 0 < σ →
    let s := σ / sqrtN n
    let a := c / s
    0 < s ∧ 0 < a ∧
    IntegrableOn (wholeTailIntegrand n σ) (Ioi c) ∧
    normalTail n c σ =
      2 * s ^ 2 * (∫ z in Ioi a, z ^ 2 * gaussianPDFReal 0 1 z) ∧
    normalTail n c σ =
      2 * c * s * gaussianPDFReal 0 1 (c / s) + 2 * s ^ 2 * normalCDF (-c / s) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : Ω → ℝ), Measurable W →
      P.map W = gaussianReal 0 ⟨s ^ 2, sq_nonneg s⟩ →
      Integrable (fun ω => W ω ^ 2) P ∧
      Integrable (fun ω => if |W ω| > c then W ω ^ 2 else 0) P ∧
      (∫ ω, if |W ω| > c then W ω ^ 2 else 0 ∂P) = normalTail n c σ)) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ c σ : ℝ, 0 < c → 0 < σ →
    extendedNormalTail n (ENNReal.ofReal c) σ = normalTail n c σ) ∧
  ((∀ (n : ℕ) (σ : ℝ), extendedNormalTail n ⊤ σ = 0) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : Ω → ℝ),
      Integrable (fun ω => if (⊤ : ℝ≥0∞) < ENNReal.ofReal |W ω|
        then W ω ^ 2 else 0) P ∧
      (∫ ω, if (⊤ : ℝ≥0∞) < ENNReal.ofReal |W ω| then W ω ^ 2 else 0 ∂P) = 0) ∧
    (∀ σ : ℝ,
      Tendsto (fun n : ℕ => (n : ℝ) * extendedNormalTail n ⊤ σ) atTop (𝓝 0) ∧
      ∀ k : ℝ, 0 < k →
        Tendsto (fun n : ℕ => (n : ℝ) ^ k * extendedNormalTail n ⊤ σ) atTop (𝓝 0)))

/-- P017-T12; the sentence after Proposition 3, PDF p. 2.
The IID rare-outlier construction realizes every positive vanishing clipping-
failure sequence under the stated hypotheses. It is a statistic of the observed
empirical distribution and has the stated exact events, normal decomposition,
finite moment bounds, central-event probability bounds and probability limits.
The logarithmic example has the stated numerical values and slow rates, and
fails the mean-square remainder condition. For each prescribed positive
vanishing rate r, the explicit sequence min(1, sqrt(r)) equals sqrt(r) eventually,
tends to zero, and its ratio to r tends to infinity; the same construction
realizes it. These facts refute a universal-rate interpretation of "quickly";
the printed sentence specifies no numerical rate. -/
def T12WholeStatement : Prop :=
  T12Statement ∧ Measurable slowObserved ∧
  (∀ (p : ℕ → ℝ) (n : ℕ), 1 ≤ n →
    RareFiniteCertificate p n ∧
    ∀ s : ℕ → ℝ × (ℝ × (ℝ × ℝ)),
      rareEstimator p n s =
        rareEmpiricalFunctional p n (empiricalObserved slowObserved n s)) ∧
  (∀ (p : ℕ → ℝ), (∀ n : ℕ, 1 ≤ n → 0 < p n ∧ p n ≤ 1) →
    Tendsto p atTop (𝓝 0) → ∀ n : ℕ, 1 ≤ n → ∀ δ : ℝ, 0 < δ →
    pr (iidSamples slowPopulation) {s | |rareRemainder p n s| > δ} ≤
      pr (iidSamples slowPopulation) {s | |smallNormalMean n s| > 1 / 2} + p n ∧
    pr (iidSamples slowPopulation) {s | |smallNormalMean n s| > 1 / 2} + p n ≤
      4 / (n : ℝ) + p n ∧
    pr (iidSamples slowPopulation)
      {s | sqrtN n * |rareEstimator p n s - clipReal 0 1 (rareEstimator p n s)| > δ} ≤ p n) ∧
  (∀ r : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → 0 < r n) → Tendsto r atTop (𝓝 0) →
    (∀ n : ℕ, 1 ≤ n → 0 < sqrtFailureRate r n ∧ sqrtFailureRate r n ≤ 1) ∧
    Tendsto (sqrtFailureRate r) atTop (𝓝 0) ∧
    (∀ᶠ n in atTop, sqrtFailureRate r n = Real.sqrt (r n)) ∧
    Tendsto (fun n => sqrtFailureRate r n / r n) atTop atTop ∧
    RootNNormal (iidSamples slowPopulation) (rareEstimator (sqrtFailureRate r)) 0 ∧
    ∀ n : ℕ, 1 ≤ n →
      pr (iidSamples slowPopulation)
        {s | rareEstimator (sqrtFailureRate r) n s ≠
          clipReal 0 1 (rareEstimator (sqrtFailureRate r) n s)} = sqrtFailureRate r n)

end
end SAP.P017
