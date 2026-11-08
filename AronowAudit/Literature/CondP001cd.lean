import AronowAudit.P001.P001_Foundations
import Mathlib.MeasureTheory.Measure.Tight

/-!
Statement-only assessment for cond-P001cd. No held theorem is used as a proof.
The literature interfaces below are independent of P001's statistical definitions.
See runs/cond-P001cd/REPORT.md for source fidelity and outstanding adapters.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
universe uΩ uE uG

namespace AronowAudit.Literature
local instance instDecidableCondP001cd (p : Prop) : Decidable p := Classical.propDecidable p

/-- Outer expectation for bounded real maps: infimum of the expectations of
measurable integrable pointwise majorants. Only bounded maps are tested below. -/
def boundedOuterExpectation {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℝ) : ℝ :=
  sInf {r | ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧
    (∀ ω, Z ω ≤ g ω) ∧ (∫ ω, g ω ∂μ) = r}

/-- Hoffmann-Jørgensen weak convergence, with possibly varying probability bases.
Testing -f gives
inner as well as outer expectations. No measurability of the approximating maps
is imposed. -/
def outerConverges {Ω : ℕ → Type uΩ} [∀ n, MeasurableSpace (Ω n)]
    {E : Type uE} [TopologicalSpace E] [MeasurableSpace E]
    (μ : ∀ n, Measure (Ω n)) (Z : ∀ n, Ω n → E) (ν : Measure E) : Prop :=
  ∀ f : E → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Tendsto (fun n => boundedOuterExpectation (μ n) (fun ω => f (Z n ω)))
      atTop (nhds (∫ x, f x ∂ν))

/-- Outer convergence in probability on varying bases. Measure application to
an arbitrary set is the outer measure of that set. -/
def outerNull {Ω : ℕ → Type uΩ} [∀ n, MeasurableSpace (Ω n)]
    {E : Type uE} [NormedAddCommGroup E]
    (μ : ∀ n, Measure (Ω n)) (Z : ∀ n, Ω n → E) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => (μ n {ω | ε ≤ ‖Z n ω‖}).toReal) atTop (nhds 0)

/-- Tangential Hadamard differentiability between arbitrary real normed spaces.
An algebraic extension A of the derivative is used to avoid restricting the
(possibly nonclosed) tangent set to a Banach subspace. Only its restriction to H
must be continuous. The arbitrary extension outside H is immaterial to the first
conclusion of the delta theorem. -/
def tangentialHadamard {E : Type uE} {G : Type uG}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (D H : Set E) (φ : E → G) (θ : E) (A : E →ₗ[ℝ] G) : Prop :=
  θ ∈ D ∧ ContinuousOn A H ∧
  ∀ h ∈ H, ∀ t : ℕ → ℝ, ∀ hseq : ℕ → E,
    (∀ n, 0 < t n) → Tendsto t atTop (nhds 0) →
    Tendsto hseq atTop (nhds h) → (∀ n, θ + t n • hseq n ∈ D) →
    Tendsto (fun n => (t n)⁻¹ • (φ (θ + t n • hseq n) - φ θ))
      atTop (nhds (A h))

/-- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press,
1998, Theorem 20.8, p. 297 (definitions pp. 296-297).
Full real-normed-space, arbitrary-rate, varying-base version: the derivative may
be continuous only on the tangent set. The limit is a Borel random element supported on that set. No additional
tightness condition is imposed (Chapter 18, pp. 258-260). Both conclusions are included: the delta limit, and,
when the derivative extends continuously to the ambient space, the asymptotic
linear expansion in outer probability. The law formulation transports the
source's random limit to its distribution; it does not posit a Gaussian limit.
-/
def VanDerVaart1998Delta : Prop :=
  ∀ (E : Type uE) (G : Type uG)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace G] [BorelSpace G]
    (Ω : ℕ → Type uΩ) [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)),
    (∀ n, IsProbabilityMeasure (μ n)) →
    ∀ (D H : Set E) (θ : E) (φ : E → G) (A : E →ₗ[ℝ] G),
    tangentialHadamard D H φ θ A →
    ∀ (T : ∀ n, Ω n → E), (∀ n ω, T n ω ∈ D) →
    ∀ (r : ℕ → ℝ), Tendsto r atTop atTop →
    ∀ (ν : Measure E), IsProbabilityMeasure ν →
    ν Hᶜ = 0 →
    outerConverges μ (fun n ω => r n • (T n ω - θ)) ν →
    outerConverges μ (fun n ω => r n • (φ (T n ω) - φ θ)) (ν.map A) ∧
    (Continuous A →
      outerNull μ (fun n ω => r n • (φ (T n ω) - φ θ) -
        A (r n • (T n ω - θ))))

/-- Bounded real functions with their actual supremum norm, without an a.e.
quotient. This is an ambient representation, not a statistical assumption. -/
abbrev BoundedRealFunctions := lp (fun _ : ℝ => ℝ) ∞

/-- Inclusion of a bounded function in the supremum-norm space. The fallback is
irrelevant for CDFs, whose values lie in [0,1]. -/
def boundedRealEmbedding (f : ℝ → ℝ) : BoundedRealFunctions :=
  if hf : Memℓp f ∞ then ⟨f, hf⟩ else 0

/-- The cadlag space D[-∞,∞], represented by its restriction to the real line.
Finite limits at both infinities specify the endpoint values. Its topology here
is the inherited uniform norm, not the Skorohod J1 topology. -/
def extendedCadlag (f : BoundedRealFunctions) : Prop :=
  (∀ x : ℝ, ContinuousWithinAt (fun t : ℝ => f t) (Set.Ici x) x) ∧
  (∀ x : ℝ, ∃ l : ℝ, Tendsto (fun t : ℝ => f t)
    (nhdsWithin x (Set.Iio x)) (nhds l)) ∧
  (∃ l : ℝ, Tendsto (fun t : ℝ => f t) atBot (nhds l)) ∧
  (∃ l : ℝ, Tendsto (fun t : ℝ => f t) atTop (nhds l))

/-- The CDF of a real random variable. -/
def realLawCDF {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  (μ {ω | X ω ≤ t}).toReal

/-- The actual empirical CDF, with an arbitrary zero-size convention. -/
def empiricalRealCDF {Ω : Type uΩ} (X : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, if X i ω ≤ t then (1 : ℝ) else 0) / (n : ℝ)

/-- Centered Gaussian process with the CDF bridge covariance. All finite linear
combinations are specified, including singular/zero covariance. This is a
process-law definition, independent of every estimator or functional. -/
def gaussianCDFCovariance [MeasurableSpace BoundedRealFunctions]
    (F : ℝ → ℝ) (ν : Measure BoundedRealFunctions) : Prop :=
  ∀ k : ℕ, ∀ t a : Fin k → ℝ,
    let v := ∑ i, ∑ j, a i * (F (min (t i) (t j)) - F (t i) * F (t j)) * a j
    0 ≤ v ∧ ν.map (fun z => ∑ i, a i * z (t i)) =
      gaussianReal 0 ⟨max v 0, le_max_right _ _⟩

/-- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press,
1998, Theorem 19.3 (Donsker), p. 266, covariance (19.2).
Every IID real sample, with arbitrary CDF (atoms allowed), has an outer weak
empirical-process limit which is a tight centered Gaussian random element in
D[-∞,∞] with that covariance. The closed uniform-norm path space is included
isometrically in the bounded-function space; the concentration clause records
its domain. No preselected bridge, functional, estimator, or delta conclusion
occurs in this literature hypothesis. -/
def VanDerVaart1998Donsker : Prop :=
  ∀ [MeasurableSpace BoundedRealFunctions] [BorelSpace BoundedRealFunctions],
  ∀ (Ω : Type uΩ) [MeasurableSpace Ω] (μ : Measure Ω),
  IsProbabilityMeasure μ → ∀ (X : ℕ → Ω → ℝ),
  (∀ i, Measurable (X i)) → iIndepFun X μ →
  (∀ i, μ.map (X i) = μ.map (X 0)) →
  ∃ ν : Measure BoundedRealFunctions,
    IsProbabilityMeasure ν ∧ IsTightMeasureSet ({ν} : Set (Measure BoundedRealFunctions)) ∧
    ν {f | ¬ extendedCadlag f} = 0 ∧
    gaussianCDFCovariance (realLawCDF μ (X 0)) ν ∧
    outerConverges (fun _ : ℕ => μ)
      (fun n ω => Real.sqrt n •
        (boundedRealEmbedding (empiricalRealCDF X n ω) -
          boundedRealEmbedding (realLawCDF μ (X 0)))) ν

/-- A finite sample's lower empirical 1/2-quantile: for positive n this equals
inf {x : F_n(x) ≥ 1/2}. The zero-size convention never affects a limit. -/
def lowerEmpiricalMedian {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ((List.ofFn x).mergeSort (fun a b => a ≤ b)).getD ((n - 1) / 2) 0

/-- Expectation under the ordinary n-out-of-n empirical resampling distribution.
The sum is over index maps, so repeated observations retain their multiplicities. -/
def finiteResamplingExpectation {n : ℕ} (T : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (g : ℝ → ℝ) : ℝ :=
  (∑ a : Fin n → Fin n, g (T (fun i => x (a i)))) / ((n : ℝ) ^ n)

/-- Conditional variance under that same finite resampling distribution. -/
def finiteResamplingVariance {n : ℕ} (T : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  finiteResamplingExpectation T x
    (fun y => (y - finiteResamplingExpectation T x id) ^ 2)

/-- The precise local CDF regularity used by Ghosh et al.: a unique median and
a positive derivative continuous throughout a neighborhood of it. No density
or atomlessness is imposed away from that neighborhood. -/
def regularMedianCDF (F : ℝ → ℝ) (m : ℝ) (f : ℝ → ℝ) : Prop :=
  F m = 1 / 2 ∧ (∀ x, x < m → F x < 1 / 2) ∧
  (∀ x, m < x → 1 / 2 < F x) ∧
  ∃ δ : ℝ, 0 < δ ∧ ContinuousOn f (Metric.ball m δ) ∧
    ∀ x ∈ Metric.ball m δ, HasDerivAt F (f x) x ∧ 0 < f x

/-- M. Ghosh, W. C. Parr, K. Singh and G. J. Babu, "A Note on Bootstrapping
the Sample Median", Annals of Statistics 12(3) (1984), 1130-1135,
Lemma 1, p. 1131 (their citation of Bickel-Freedman Proposition 5.1).
For every IID real sample satisfying the stated unique-median/local-C1
conditions, the conditional law of sqrt(n)(m_n^* - m_n) converges weakly,
along almost every sample sequence, to N(0,1/(4 f(m)^2)).
All bounded continuous tests are inside the almost-everywhere quantifier.
-/
def GhoshEtAl1984MedianWeak : Prop :=
  ∀ (Ω : Type uΩ) [MeasurableSpace Ω] (μ : Measure Ω),
  IsProbabilityMeasure μ → ∀ (X : ℕ → Ω → ℝ),
  (∀ i, Measurable (X i)) → iIndepFun X μ →
  (∀ i, μ.map (X i) = μ.map (X 0)) →
  ∀ (m : ℝ) (f : ℝ → ℝ), regularMedianCDF (realLawCDF μ (X 0)) m f →
  ∀ᵐ ω ∂μ, ∀ g : ℝ → ℝ, Continuous g → (∃ C : ℝ, ∀ z, |g z| ≤ C) →
    Tendsto (fun n => finiteResamplingExpectation lowerEmpiricalMedian
      (fun i : Fin n => X i ω)
      (fun y => g (Real.sqrt n * (y - lowerEmpiricalMedian (fun i : Fin n => X i ω)))))
      atTop (nhds (∫ z, g z ∂(gaussianReal 0 ⟨(1 / (2 * f m)) ^ 2, sq_nonneg _⟩)))

/-- M. Ghosh, W. C. Parr, K. Singh and G. J. Babu, "A Note on Bootstrapping
the Sample Median", Annals of Statistics 12(3) (1984), 1130-1135,
Theorem 1, p. 1133; the conditions of Lemma 1 are on p. 1131.
For every IID real sample with those local CDF conditions and a finite absolute
moment of some positive order, the bootstrap estimate of the root-n median
variance converges almost surely to 1/(4 f(m)^2). This is a strong-convergence
statement, with no integrability assumption on the estimator across samples.
-/
def GhoshEtAl1984MedianVariance : Prop :=
  ∀ (Ω : Type uΩ) [MeasurableSpace Ω] (μ : Measure Ω),
  IsProbabilityMeasure μ → ∀ (X : ℕ → Ω → ℝ),
  (∀ i, Measurable (X i)) → iIndepFun X μ →
  (∀ i, μ.map (X i) = μ.map (X 0)) →
  ∀ (m : ℝ) (f : ℝ → ℝ), regularMedianCDF (realLawCDF μ (X 0)) m f →
  ∀ α : ℝ, 0 < α → Integrable (fun ω => |X 0 ω| ^ α) μ →
  ∀ᵐ ω ∂μ, Tendsto
    (fun n : ℕ => (n : ℝ) * finiteResamplingVariance lowerEmpiricalMedian (fun i : Fin n => X i ω))
    atTop (nhds (1 / (4 * (f m) ^ 2)))

set_option pp.universes true in
#check @GhoshEtAl1984MedianWeak
set_option pp.universes true in
#check @GhoshEtAl1984MedianVariance
#print GhoshEtAl1984MedianWeak
#print GhoshEtAl1984MedianVariance

set_option pp.universes true in
#check @VanDerVaart1998Delta
set_option pp.universes true in
#check @VanDerVaart1998Donsker
#print VanDerVaart1998Delta
#print VanDerVaart1998Donsker

end AronowAudit.Literature

namespace AronowAudit.P001
set_option linter.unusedVariables false

/-- Exact held proposition at P001_Foundations.lean:6755, with only universal
published results prefixed. Source hypotheses are not paper-specific premises. -/
def empirical_cdf_delta_nondegenerate_supporting_conditional_statement : Prop :=
  AronowAudit.Literature.VanDerVaart1998Delta.{uΩ, 0, 0} →
  ∀ {Ω : Type uΩ} [MeasurableSpace Ω]
    [MeasurableSpace KolmogorovSpace] [BorelSpace KolmogorovSpace]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X)
    (T : (ℝ → ℝ) → ℝ) (H : Set KolmogorovSpace)
    (L : KolmogorovSpace →L[ℝ] ℝ)
    (hd : HadamardAt cdfDomain H (fun f => T (fun x => f x))
      (kolmogorovEmbed (cdf μ (X 0))) L)
    (νB : Measure KolmogorovSpace) [IsProbabilityMeasure νB]
    (htangent : νB Hᶜ = 0)
    (hprocess : OuterWeakLimit μ (fun n ω =>
      Real.sqrt n • (empiricalCDFElement X n ω - kolmogorovEmbed (cdf μ (X 0)))) νB)
    (v : ℝ≥0) (hv : 0 < v) (hgauss : νB.map L = gaussianReal 0 v)
    (hstat : ∀ n, Measurable (fun ω => T (cdf (empirical X n ω) id))),
    CD μ (fun n ω => Real.sqrt n *
      (T (cdf (empirical X n ω) id) - T (cdf μ (X 0)))) (gaussianReal 0 v)

/-- Exact held proposition at P001_Foundations.lean:3021. The source's outer
convergence permits a possibly nonmeasurable transformed statistic, as does CD's
use of measure application to its threshold events. -/
def functional_delta_nondegenerate_correction_supporting_conditional_statement : Prop :=
  AronowAudit.Literature.VanDerVaart1998Delta.{uΩ, uE, 0} →
  ∀ {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D H : Set E) (F : E)
    (T : E → ℝ) (L : E →L[ℝ] ℝ) (hd : HadamardAt D H T F L)
    (Fhat : ℕ → Ω → E) (hmeas : ∀ n, Measurable (Fhat n))
    (hvalid : ∀ n ω, 0 < n → Fhat n ω ∈ D)
    (νB : Measure E) [IsProbabilityMeasure νB] (htangent : νB Hᶜ = 0)
    (hprocess : WeakLimit μ (fun n ω => Real.sqrt n • (Fhat n ω - F)) νB)
    (v : ℝ≥0) (hv : 0 < v) (hgauss : νB.map L = gaussianReal 0 v),
    CD μ (fun n ω => Real.sqrt n * (T (Fhat n ω) - T F)) (gaussianReal 0 v)

/-- Exact held proposition at P001_Foundations.lean:6665. The source hypotheses
are applied to a monotone locally-uniformizing transformation; no extra
continuity premise is added to the held density f. -/
def bootstrap_median_primitive_moment_condition_supporting_conditional_statement : Prop :=
  AronowAudit.Literature.GhoshEtAl1984MedianWeak.{uΩ} →
  AronowAudit.Literature.GhoshEtAl1984MedianVariance.{uΩ} →
  ∀ {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X) (m : ℝ) (f : ℝ → ℝ)
    (hf : HasPDF (μ.map (X 0)) f) (hcont : ContinuousAt f m) (hpos : 0 < f m)
    (hmed : cdf μ (X 0) m = 1 / 2 ∧
      (∀ x, x < m → cdf μ (X 0) x < 1 / 2) ∧
      (∀ x, m < x → 1 / 2 < cdf μ (X 0) x))
    (η : ℝ) (hη : 0 < η) (hmoment : Integrable (fun ω => |X 0 ω| ^ η) μ),
    CP μ (fun k ω => ((2 * k + 1 : ℕ) : ℝ) *
      bootVar sampleMedian (firstSample X (2 * k + 1) ω)) (1 / (4 * (f m) ^ 2)) ∧
    CP μ (fun k ω => Real.sqrt (2 * k + 1) *
      Real.sqrt (bootVar sampleMedian (firstSample X (2 * k + 1) ω))) (1 / (2 * f m))

/-- Exact held proposition at P001_Foundations.lean:9264, with the universal
published Donsker theorem prefixed, without changing the bridge premise. -/
def iid_empirical_cdf_bridge_limit_conditional_statement : Prop :=
  AronowAudit.Literature.VanDerVaart1998Donsker.{uΩ} →
  ∀ {Ω : Type uΩ} [MeasurableSpace Ω]
    [MeasurableSpace KolmogorovSpace] [BorelSpace KolmogorovSpace]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X)
    (νB : Measure KolmogorovSpace) [IsProbabilityMeasure νB]
    (hbridge : IsCDFBridge (cdf μ (X 0)) νB),
    OuterWeakLimit μ (fun n ω => Real.sqrt n •
      (empiricalCDFElement X n ω - kolmogorovEmbed (cdf μ (X 0)))) νB

set_option pp.universes true in
#check @empirical_cdf_delta_nondegenerate_supporting_conditional_statement
set_option pp.universes true in
#check @iid_empirical_cdf_bridge_limit_conditional_statement

set_option pp.universes true in
#check @functional_delta_nondegenerate_correction_supporting_conditional_statement

set_option pp.universes true in
#check @bootstrap_median_primitive_moment_condition_supporting_conditional_statement

end AronowAudit.P001

#print axioms AronowAudit.Literature.VanDerVaart1998Delta
#print axioms AronowAudit.Literature.VanDerVaart1998Donsker
#print axioms AronowAudit.P001.empirical_cdf_delta_nondegenerate_supporting_conditional_statement
#print axioms AronowAudit.P001.iid_empirical_cdf_bridge_limit_conditional_statement

#print axioms AronowAudit.P001.functional_delta_nondegenerate_correction_supporting_conditional_statement

#print axioms AronowAudit.Literature.GhoshEtAl1984MedianWeak
#print axioms AronowAudit.Literature.GhoshEtAl1984MedianVariance
#print axioms AronowAudit.P001.bootstrap_median_primitive_moment_condition_supporting_conditional_statement

-- Read-only signature diagnostics for the held universe binders.
set_option pp.universes true in
#check @AronowAudit.P001.functional_delta_nondegenerate_correction_supporting
set_option pp.universes true in
#check @AronowAudit.P001.bootstrap_median_primitive_moment_condition_supporting
