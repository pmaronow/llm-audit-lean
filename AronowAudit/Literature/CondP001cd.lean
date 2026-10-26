import AronowAudit.P001.P001_Foundations
import Mathlib.MeasureTheory.Measure.Tight

/-!
Statements of the functional delta theorem and its conditional applications.
The literature interfaces are independent of P001's statistical definitions;
the delta theorem is an explicit hypothesis of the application statements.
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


/-- The actual empirical CDF, with an arbitrary zero-size convention. -/
def empiricalRealCDF {Ω : Type uΩ} (X : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, if X i ω ≤ t then (1 : ℝ) else 0) / (n : ℝ)


end AronowAudit.Literature

namespace AronowAudit.P001
set_option linter.unusedVariables false

/-- Conditional empirical-CDF delta statement with the published delta theorem
as a hypothesis. Source hypotheses are not paper-specific premises. -/
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

/-- Conditional functional delta statement. The source's outer convergence
permits a possibly nonmeasurable transformed statistic, as does CD's use of
measure application to its threshold events. -/
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


end AronowAudit.P001

