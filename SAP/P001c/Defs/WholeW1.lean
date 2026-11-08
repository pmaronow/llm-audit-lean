import Mathlib
import SAP.P001c.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c

universe u

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical

noncomputable section

/-- The residual of a finite-dimensional affine predictor, including its intercept. -/
def affineResidual {Ω : Type*} {K : ℕ} (X : Ω → Fin K → ℝ) (Y : Ω → ℝ)
    (b : Fin (K + 1) → ℝ) : Ω → ℝ :=
  fun ω => Y ω - affinePredictor b (X ω)

/-- The absolute-convergence convention for every candidate in the BLP objective. -/
def finiteAffineLosses {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) (X : Ω → Fin K → ℝ) (Y : Ω → ℝ) : Prop :=
  ∀ b : Fin (K + 1) → ℝ, Integrable (fun ω => (affineResidual X Y b ω)^2) μ

/-- Global MSE minimization; no uniqueness or nonsingularity is built into BLP. -/
def minimizesAffineLoss {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) (X : Ω → Fin K → ℝ) (Y : Ω → ℝ)
    (b : Fin (K + 1) → ℝ) : Prop :=
  ∀ c : Fin (K + 1) → ℝ,
    expectation μ (fun ω => (affineResidual X Y b ω)^2) ≤
      expectation μ (fun ω => (affineResidual X Y c ω)^2)

/-- P001-T49; p. 87 (PDF p. 105), opening paragraph and Theorems 2.3.7–8;
Definition 2.3.6, p. 86 (PDF p. 104).
Every affine predictor has its intercept as its value at zero and each slope as
its unit coordinate increment and partial derivative. Every MSE-minimizing affine
predictor has a residual with zero mean, zero coordinate-product expectations,
and zero coordinate covariances, including singular designs and zero regressors. -/
def T49WholeStatement : Prop :=
  T49Statement ∧
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ) (X : Ω → Fin K → ℝ) (Y : Ω → ℝ),
    (∀ k, Measurable (fun ω => X ω k)) → Measurable Y →
    finiteAffineLosses μ X Y → ∀ b : Fin (K + 1) → ℝ,
    minimizesAffineLoss μ X Y b →
    expectation μ (affineResidual X Y b) = 0 ∧
    ∀ k : Fin K,
      expectation μ (fun ω => X ω k * affineResidual X Y b ω) = 0 ∧
      covariance (fun ω => X ω k) (affineResidual X Y b) μ = 0

/-- A concrete endpoint counterexample law, with atom k of mass 2^(-(k+1)). -/
def endpointLaw : Measure ℕ := geometricMeasure ⟨1/2, by norm_num, by norm_num⟩

def endpointSequence (n k : ℕ) : ℝ := if k = n then 1 else 0

/-- P001-T51; p. 99 (PDF p. 117), Definition 3.2.6 and the following paragraph.
The bad-event limit zero, within-epsilon limit one, and every eventual probability
lower bound in [0,1) are equivalent. The measurable singleton-indicator sequence
under the geometric law converges in probability to zero, but its within-1/2
probability is 1-2^(-(n+1)) at every n, so the printed endpoint p=1 fails. -/
def T51WholeStatement : Prop :=
  (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℝ), (∀ n, Measurable (Z n)) → ∀ c : ℝ,
    (convergesInProbability μ Z c ↔
      ∀ ε : ℝ, 0 < ε → Tendsto
        (fun n => probability μ {ω | |Z n ω - c| < ε}) atTop (nhds 1)) ∧
    (convergesInProbability μ Z c ↔
      ∀ p : ℝ, 0 ≤ p → p < 1 → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ n, N ≤ n → p ≤ probability μ {ω | |Z n ω - c| < ε})) ∧
  IsProbabilityMeasure endpointLaw ∧
  (∀ n, Measurable (endpointSequence n)) ∧
  convergesInProbability endpointLaw endpointSequence 0 ∧
  (∀ n, probability endpointLaw {k | |endpointSequence n k| < 1/2} =
      1 - (1/2 : ℝ)^(n+1) ∧
    probability endpointLaw {k | |endpointSequence n k| < 1/2} < 1) ∧
  ¬ (∃ N : ℕ, ∀ n, N ≤ n →
    1 ≤ probability endpointLaw {k | |endpointSequence n k| < 1/2})

/-- The validator's power-tail law is the geometric law with success probability 7/8. -/
def powerTailLaw : Measure ℕ := geometricMeasure ⟨7/8, by norm_num, by norm_num⟩

def powerTailValue (k : ℕ) : ℝ := (2 : ℝ)^k

def powerTailProduct : Measure (ℕ → ℕ) :=
  Measure.infinitePi (fun _ : ℕ => powerTailLaw)

def powerTailSample (i : ℕ) (ω : ℕ → ℕ) : ℝ := powerTailValue (ω i)

/-- P001-T53; proof of Theorem 3.2.19, p. 107 (PDF p. 125);
Theorem 3.2.19, p. 106 (PDF p. 124), and Theorem 3.2.8, p. 100 (PDF p. 118).
The normalized masses 7/8^(k+1) at 2^k are realized by an infinite IID sequence
with mean 7/6, second moment 7/4, variance 7/18, and infinite fourth moment.
Its squares are integrable but have infinite extended variance, refuting the
printed proof's inference of the finite-variance WLLN hypothesis for the squares.
The finite-variance WLLN and the sample-variance expectation and consistency
theorems still hold, in particular for this sequence. -/
def T53WholeStatement : Prop :=
  T53Statement ∧ IsProbabilityMeasure powerTailProduct ∧
  isIID powerTailProduct powerTailSample ∧
  (∀ i : ℕ,
    (∀ k : ℕ, probability powerTailProduct {ω | powerTailSample i ω = (2 : ℝ)^k} =
      powerTailMass k) ∧
    MemLp (powerTailSample i) 2 powerTailProduct ∧
    expectation powerTailProduct (fun ω => |powerTailSample i ω|) = 7/6 ∧
    expectation powerTailProduct (powerTailSample i) = 7/6 ∧
    Integrable (fun ω => (powerTailSample i ω)^2) powerTailProduct ∧
    expectation powerTailProduct (fun ω => (powerTailSample i ω)^2) = 7/4 ∧
    variance (powerTailSample i) powerTailProduct = 7/18 ∧
    (∫⁻ ω, ENNReal.ofReal ((powerTailSample i ω)^4) ∂powerTailProduct) = ∞ ∧
    ¬ MemLp (fun ω => (powerTailSample i ω)^2) 2 powerTailProduct ∧
    evariance (fun ω => (powerTailSample i ω)^2) powerTailProduct = ∞) ∧
  (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), isIID μ X → MemLp (X 0) 2 μ →
    0 < variance (X 0) μ →
    convergesInProbability μ (sampleAverage X) (expectation μ (X 0)) ∧
    (∀ n : ℕ, 0 < n → expectation μ (pluginVariance X n) =
      ((n : ℝ)-1)/n * variance (X 0) μ) ∧
    convergesInProbability μ (pluginVariance X) (variance (X 0) μ)) ∧
  (∀ n : ℕ, 0 < n → expectation powerTailProduct (pluginVariance powerTailSample n) =
    ((n : ℝ)-1)/n * (7/18)) ∧
  convergesInProbability powerTailProduct (pluginVariance powerTailSample) (7/18) ∧
  convergesInProbability powerTailProduct (sampleAverage powerTailSample) (7/6) ∧
  convergesInProbability powerTailProduct
    (sampleAverage (fun i ω => (powerTailSample i ω)^2)) (7/4)

/-- P001-T54; Theorem 3.2.19 and its proof, pp. 106–107 (PDF pp. 124–125);
Theorem 3.2.7, p. 100 (PDF p. 118).
The WLLN holds for IID integrable variables, and the two-variable continuous
mapping theorem holds without independence. Under finite positive population
variance, the sample mean and sample second moment converge to their population
values; the plug-in variance has expectation (n-1)/n times population variance
and converges to that variance. Only a second moment is needed. -/
def T54WholeStatement : Prop :=
  (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℝ), isIID μ Z → Integrable (Z 0) μ →
    convergesInProbability μ (sampleAverage Z) (expectation μ (Z 0))) ∧
  (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S T : ℕ → Ω → ℝ) (a b : ℝ),
    (∀ n, Measurable (S n)) → (∀ n, Measurable (T n)) →
    convergesInProbability μ S a → convergesInProbability μ T b →
    ∀ g : ℝ × ℝ → ℝ, Continuous g →
    convergesInProbability μ (fun n ω => g (S n ω, T n ω)) (g (a,b))) ∧
  (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), isIID μ X → MemLp (X 0) 2 μ →
    0 < variance (X 0) μ →
    convergesInProbability μ (sampleAverage X) (expectation μ (X 0)) ∧
    convergesInProbability μ (sampleAverage (fun i ω => (X i ω)^2))
      (expectation μ (fun ω => (X 0 ω)^2)) ∧
    expectation μ (fun ω => (X 0 ω)^2) - (expectation μ (X 0))^2 = variance (X 0) μ ∧
    (∀ n : ℕ, 0 < n → expectation μ (pluginVariance X n) =
      ((n : ℝ)-1)/n * variance (X 0) μ) ∧
    convergesInProbability μ (pluginVariance X) (variance (X 0) μ))

/-- A statistical functional is defined on CDFs. Its value elsewhere is a harmless
extension used only to state sequential limits; all positive-size plug-ins are CDFs. -/
def cdfFunctionalValue (T : cdfSet → ℝ) (f : CDFSpace) : ℝ :=
  if hf : f ∈ cdfSet then T ⟨f, hf⟩ else 0

/-- Sequential Hadamard differentiation on the CDF domain, tangentially to an
arbitrary real subspace, with the derivative defined only on that subspace. -/
def cdfHadamardOn (T : cdfSet → ℝ) (F : CDFSpace)
    (H : Submodule ℝ CDFSpace) (L : H →L[ℝ] ℝ) : Prop :=
  ∀ h : H, ∀ t : ℕ → ℝ, ∀ hn : ℕ → CDFSpace,
    (∀ n, 0 < t n) → Tendsto t atTop (nhds 0) →
    Tendsto hn atTop (nhds (h : CDFSpace)) →
    (∀ n, F + t n • hn n ∈ cdfSet) →
    Tendsto (fun n => (cdfFunctionalValue T (F + t n • hn n) -
      cdfFunctionalValue T F) / t n) atTop (nhds (L h))

/-- P001-T57; Theorem 3.3.6 and footnote 31, p. 120 (PDF p. 138);
Definition 3.2.28, p. 112 (PDF p. 130), with the non-degeneracy correction.
Every real IID empirical-CDF process has a tight Brownian-bridge outer limit in
the sup norm. A CDF-domain functional Hadamard differentiable on any subspace
carrying that bridge almost surely has a centered Gaussian derivative limit,
possibly degenerate, with finite variance. Its measurable scalar plug-in converges
in distribution to that law. Positive derivative variance gives asymptotic
normality with phi squared equal to that variance; zero variance gives a point mass.
No closedness of the tangent subspace or moment assumption on the observations
is required. -/
def T57WholeStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω]
    [MeasurableSpace CDFSpace] [BorelSpace CDFSpace]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ), isIID μ X →
    ∃ ν : Measure CDFSpace, IsProbabilityMeasure ν ∧
      IsTightMeasureSet ({ν} : Set (Measure CDFSpace)) ∧
      isCDFBridge (cdfAt μ (X 0)) ν ∧
      outerWeakConvergence μ
        (fun n ω => Real.sqrt n • (empiricalCDF X n ω - embedCDF (cdfAt μ (X 0)))) ν ∧
      ∀ (H : Submodule ℝ CDFSpace) (ell : H →L[ℝ] ℝ) (T : cdfSet → ℝ),
        ν (H : Set CDFSpace)ᶜ = 0 →
        cdfHadamardOn T (embedCDF (cdfAt μ (X 0))) H ell →
        (∀ n : ℕ, 0 < n → Measurable (fun ω => cdfFunctionalValue T (empiricalCDF X n ω))) →
        ∃ L : CDFSpace →L[ℝ] ℝ,
          (∀ h : H, L h = ell h) ∧ MemLp (fun h => L h) 2 ν ∧
          expectation ν (fun h => L h) = 0 ∧ 0 ≤ variance (fun h => L h) ν ∧
          ν.map L = gaussianReal 0 (variance (fun h => L h) ν).toNNReal ∧
          convergesInDistribution μ
            (fun n ω => Real.sqrt n * (cdfFunctionalValue T (empiricalCDF X n ω) -
              cdfFunctionalValue T (embedCDF (cdfAt μ (X 0))))) (ν.map L) ∧
          (variance (fun h => L h) ν = 0 → ν.map L = Measure.dirac 0) ∧
          (0 < variance (fun h => L h) ν → ∃ phi : ℝ, 0 < phi ∧
            phi^2 = variance (fun h => L h) ν ∧
            convergesInDistribution μ
              (fun n ω => Real.sqrt n * (cdfFunctionalValue T (empiricalCDF X n ω) -
                cdfFunctionalValue T (embedCDF (cdfAt μ (X 0)))))
              (gaussianReal 0 ⟨phi^2, sq_nonneg phi⟩)) ∧
          (∀ L' : CDFSpace →L[ℝ] ℝ, (∀ h : H, L' h = ell h) → ν.map L' = ν.map L)

end
end SAP.P001c
