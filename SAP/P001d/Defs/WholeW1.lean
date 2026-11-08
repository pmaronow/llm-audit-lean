import Mathlib
import SAP.P001d.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d

/-- The book's unbiased empirical variance, with real subtraction in n - 1. -/
def wholeEmpiricalVariance {n : ℕ} (e : Fin n → ℝ) : ℝ :=
  (n : ℝ) / ((n : ℝ) - 1) *
    ((∑ i, (e i)^2) / (n : ℝ) - ((∑ i, e i) / (n : ℝ))^2)

/-- P001-T66; p. 153 (PDF p. 171) and p. 155 (PDF p. 173).
The usual measure-theoretic conditions are assumed.
For a sample of size at least two with an intercept and invertible Gram matrix,
the OLS residuals are centered and their unbiased empirical variance is the
residual sum of squares divided by n - 1. The normalized outer-product formulas
equal the robust and classical matrix covariance estimates. Both estimates have
nonnegative diagonals, and the standard error of coefficient k is the square
root of entry (k,k), the book's ordinal row and column k + 1. -/
def T66WholeStatement : Prop :=
  ∀ {n K : ℕ}, 2 ≤ n →
    ∀ (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ),
    (∀ i, X i 0 = 1) → IsUnit (X.transpose * X).det →
    let β := olsCoef X Y
    let e := Y - X.mulVec β
    let s2 := wholeEmpiricalVariance e
    let A : Matrix (Fin (K+1)) (Fin (K+1)) ℝ :=
      fun j k => (∑ i, X i j * X i k) / (n : ℝ)
    let B : Matrix (Fin (K+1)) (Fin (K+1)) ℝ :=
      fun j k => (∑ i, (e i)^2 * X i j * X i k) / (n : ℝ)
    (∀ b, olsRSS X Y β ≤ olsRSS X Y b ∧
      (olsRSS X Y b = olsRSS X Y β ↔ b = β)) ∧
    (∑ i, e i) / (n : ℝ) = 0 ∧
    s2 = (∑ i, (e i)^2) / ((n : ℝ) - 1) ∧ 0 ≤ s2 ∧
    A = (n : ℝ)⁻¹ • (X.transpose * X) ∧
    B = (n : ℝ)⁻¹ • (X.transpose * Matrix.diagonal (fun i => (e i)^2) * X) ∧
    (n : ℝ)⁻¹ • (A⁻¹ * B * A⁻¹) = robustCov X e ∧
    (s2 / (n : ℝ)) • A⁻¹ = classicalCov X s2 ∧
    (∀ k : Fin (K+1),
      0 ≤ robustCov X e k k ∧ 0 ≤ classicalCov X s2 k k ∧
      coefficientSE ((n : ℝ)⁻¹ • (A⁻¹ * B * A⁻¹)) k =
        Real.sqrt (robustCov X e k k) ∧
      coefficientSE ((s2 / (n : ℝ)) • A⁻¹) k =
        Real.sqrt (classicalCov X s2 k k))

/-- The positive-scale Gaussian-model likelihood for a fixed realized sample. -/
def wholeNormalLikelihood {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ)
    (Y : Fin n → ℝ) (b : Fin (K+1) → ℝ) (s : ℝ) : ℝ :=
  ∏ i, normalDensity ((X.mulVec b) i) s (Y i)

/-- P001-T76; pp. 190–191 (PDF pp. 208–209).
The usual measure-theoretic conditions are assumed.
At every fixed positive scale, the Gaussian likelihood is a positive product of
the displayed normal densities; its logarithm is the displayed sum and the
closed-form normal log-likelihood. Likelihood maximizers, log-likelihood
maximizers and residual-sum-of-squares minimizers in R^(K+1) coincide, so their
sets do not depend on the positive scale. If the Gram matrix is invertible,
the maximizer exists uniquely and equals (X^T X)^(-1) X^T Y. At positive sample
sizes, minimizing the sum is equivalent to minimizing the OLS mean square. -/
def T76WholeStatement : Prop :=
  ∀ {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ),
    (∀ (b : Fin (K+1) → ℝ) (s : ℝ), 0 < s →
      wholeNormalLikelihood X Y b s =
        ∏ i, (1 / (s * Real.sqrt (2 * Real.pi))) *
          Real.exp (-(Y i - (X.mulVec b) i)^2 / (2 * s^2)) ∧
      0 < wholeNormalLikelihood X Y b s ∧
      Real.log (wholeNormalLikelihood X Y b s) =
        ∑ i, (Real.log (1 / (s * Real.sqrt (2 * Real.pi))) -
          (Y i - (X.mulVec b) i)^2 / (2 * s^2)) ∧
      Real.log (wholeNormalLikelihood X Y b s) = normalLogLikelihood X Y b s) ∧
    (∀ (b : Fin (K+1) → ℝ) (s : ℝ), 0 < s →
      ((∀ c, wholeNormalLikelihood X Y c s ≤ wholeNormalLikelihood X Y b s) ↔
        (∀ c, normalLogLikelihood X Y c s ≤ normalLogLikelihood X Y b s)) ∧
      ((∀ c, normalLogLikelihood X Y c s ≤ normalLogLikelihood X Y b s) ↔
        (∀ c, olsRSS X Y b ≤ olsRSS X Y c))) ∧
    (∀ (b : Fin (K+1) → ℝ) (s t : ℝ), 0 < s → 0 < t →
      ((∀ c, wholeNormalLikelihood X Y c s ≤ wholeNormalLikelihood X Y b s) ↔
        (∀ c, wholeNormalLikelihood X Y c t ≤ wholeNormalLikelihood X Y b t))) ∧
    (IsUnit (X.transpose * X).det →
      ∀ s : ℝ, 0 < s →
      (∀ b, (∀ c, wholeNormalLikelihood X Y c s ≤ wholeNormalLikelihood X Y b s) ↔
        b = olsCoef X Y) ∧
      ∃! b, ∀ c, wholeNormalLikelihood X Y c s ≤ wholeNormalLikelihood X Y b s) ∧
    (0 < n → ∀ b : Fin (K+1) → ℝ,
      ((∀ c, olsRSS X Y b ≤ olsRSS X Y c) ↔
        (∀ c, olsRSS X Y b / (n : ℝ) ≤ olsRSS X Y c / (n : ℝ))))

/-- Coordinate derivative, using an increment in coordinate k at t = 0. -/
def wholePartial {d : ℕ} (m : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (k : Fin d) : ℝ :=
  deriv (fun t : ℝ => m (x + t • Pi.single k 1)) (0 : ℝ)

/-- The empirical probability law of a nonempty finite sample. -/
def wholeEmpiricalLaw {d n : ℕ} (x : Fin n → Fin d → ℝ) : Measure (Fin d → ℝ) :=
  (ENNReal.ofReal (1 / (n : ℝ))) • ∑ i, Measure.dirac (x i)

/-- The APD plug-in statistic, indexed by the coordinate and a chosen fitted CEF. -/
def wholePluginAPD {d n : ℕ} (x : Fin n → Fin d → ℝ)
    (mhat : (Fin d → ℝ) → ℝ) (k : Fin d) : ℝ :=
  ∫ z, wholePartial mhat z k ∂wholeEmpiricalLaw x

/-- P001-T69; pp. 166–167 (PDF pp. 184–185).
The usual measure-theoretic conditions are assumed.
For independent U(0,1) covariates and the specified piecewise CEF, its first
partial derivative is -1 on the branch of probability 4/5 and 9 on the branch
of probability 1/5. The covariate means are (1/2,1/2), APD_1 is
(-1)(4/5) + 9(1/5) = 1, and PDA_1 is -1, so they differ. For any nonempty
sample and fitted CEF with the coordinate derivatives used by the formula,
the empirical-law APD plug-in is the average of those derivatives. Its index
is the coordinate k, with no individual-observation subscript. -/
def T69WholeStatement : Prop :=
  (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X1 X2 Y : Ω → ℝ),
    Measurable X1 → Measurable X2 → Integrable Y μ → IndepFun X1 X2 μ →
    μ.map X1 = uniformLaw 0 1 → μ.map X2 = uniformLaw 0 1 →
    IsCEF μ (fun ω => (X1 ω, X2 ω)) Y (fun xy => apdExample xy.1 xy.2) →
    (∀ x y : ℝ, HasDerivAt (fun t => apdExample t y)
      (if y ≤ 4/5 then -1 else 9) x) ∧
    prob μ {ω | X2 ω ≤ 4/5} = 4/5 ∧ prob μ {ω | 4/5 < X2 ω} = 1/5 ∧
    (∫ ω, X1 ω ∂μ) = 1/2 ∧ (∫ ω, X2 ω ∂μ) = 1/2 ∧
    Integrable (fun ω => deriv (fun t => apdExample t (X2 ω)) (X1 ω)) μ ∧
    (∫ ω, deriv (fun t => apdExample t (X2 ω)) (X1 ω) ∂μ) =
      (-1) * prob μ {ω | X2 ω ≤ 4/5} + 9 * prob μ {ω | 4/5 < X2 ω} ∧
    (∫ ω, deriv (fun t => apdExample t (X2 ω)) (X1 ω) ∂μ) = 1 ∧
    deriv (fun t => apdExample t (∫ ω, X2 ω ∂μ)) (∫ ω, X1 ω ∂μ) = -1 ∧
    (∫ ω, deriv (fun t => apdExample t (X2 ω)) (X1 ω) ∂μ) ≠
      deriv (fun t => apdExample t (∫ ω, X2 ω ∂μ)) (∫ ω, X1 ω ∂μ)) ∧
  (∀ {d n : ℕ}, 0 < n → ∀ (x : Fin n → Fin d → ℝ)
    (mhat : (Fin d → ℝ) → ℝ) (k : Fin d),
    (∀ i, DifferentiableAt ℝ (fun t : ℝ => mhat (x i + t • Pi.single k 1)) (0 : ℝ)) →
    IsProbabilityMeasure (wholeEmpiricalLaw x) ∧
    Integrable (fun z => wholePartial mhat z k) (wholeEmpiricalLaw x) ∧
    wholePluginAPD x mhat k = (1 / (n : ℝ)) * ∑ i, wholePartial mhat (x i) k)

/-- Conditional variance as a sample-space version, using the genuine
conditional expectation for the sigma algebra generated by X. -/
def wholeConditionalVariance {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (Y : Ω → ℝ) : Ω → ℝ :=
  μ[(fun ω => (Y ω - μ[Y | MeasurableSpace.comap X inferInstance] ω)^2) |
    MeasurableSpace.comap X inferInstance]

/-- Existence and both identities for the conditional residual variance.
The IsCEF certificate supplies all integrability of the selected version v. -/
def WholeResidualVarianceFacts {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (Y : Ω → ℝ) (m : E → ℝ) : Prop :=
  let ε := fun ω => Y ω - m (X ω)
  ∃ v : E → ℝ,
    IsCEF μ X (fun ω => (ε ω)^2) v ∧
    wholeConditionalVariance μ X ε =ᵐ[μ] wholeConditionalVariance μ X Y ∧
    wholeConditionalVariance μ X Y =ᵐ[μ] (v ∘ X) ∧
    Integrable (wholeConditionalVariance μ X Y) μ ∧
    variance ε μ = ∫ ω, wholeConditionalVariance μ X Y ω ∂μ

/-- A specified conditional probability kernel, characterized on rectangles.
The instances used below are Borel Gaussian probability kernels. -/
def WholeConditionalLaw {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (Y : Ω → ℝ) (κ : E → Measure ℝ) : Prop :=
  (∀ x, IsProbabilityMeasure (κ x)) ∧
  (∀ B : Set ℝ, MeasurableSet B → Measurable (fun x => κ x B)) ∧
  ∀ (A : Set E) (B : Set ℝ), MeasurableSet A → MeasurableSet B →
    μ {ω | X ω ∈ A ∧ Y ω ∈ B} = ∫⁻ x in A, κ x B ∂(μ.map X)

/-- The classical model's conditional location, with the intercept coordinate. -/
def wholeLinearMean {K : ℕ} (β x : Fin (K+1) → ℝ) : ℝ := ∑ k, x k * β k

/-- The model-compatible conditional normal kernel, specified also off support. -/
def wholeNormalKernel {K : ℕ} (β : Fin (K+1) → ℝ) (s : ℝ)
    (x : Fin (K+1) → ℝ) : Measure ℝ :=
  gaussianReal (wholeLinearMean β x) ⟨s^2, sq_nonneg _⟩

/-- P001-T74; p. 181 (PDF p. 199); Theorem 2.2.19, pp. 74–75
(PDF pp. 92–93).
The usual measure-theoretic conditions are assumed; functions of X are
measurable functions. For an integrable response and a chosen conditional mean,
the residual has conditional and unconditional mean zero and is uncorrelated
with every measurable function of X whenever the means and residual product
moment exist. If the residual second moment exists, its conditional variance
equals that of Y, and its variance is the expectation of that conditional
variance; a conditional-variance version exists. Residuals need not be
independent of X, as the four-point example shows. In the classical conditional
normal model at positive scale, the specified residual conditional law is
N(0,sigma^2) at every covariate value; the residual has that marginal law and
is independent of X. Pointwise conditional laws refer to the specified model
version, and conditional-expectation identities are almost-sure identities. -/
def T74WholeStatement : Prop :=
  (∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E), Measurable X →
    ∀ (Y : Ω → ℝ), Measurable Y → ∀ m : E → ℝ, IsCEF μ X Y m →
    let ε := fun ω => Y ω - m (X ω)
    Integrable ε μ ∧ IsCEF μ X ε (fun _ => 0) ∧
    (∫ ω, ε ω ∂μ) = 0 ∧
    ((fun _ : Ω => (0 : ℝ)) =ᵐ[μ] μ[ε | MeasurableSpace.comap X inferInstance]) ∧
    (∀ g : E → ℝ, Measurable g → Integrable (g ∘ X) μ →
      Integrable (fun ω => g (X ω) * ε ω) μ → covariance (g ∘ X) ε μ = 0) ∧
    (Integrable (fun ω => (ε ω)^2) μ → WholeResidualVarianceFacts μ X Y m)) ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K : ℕ} (X : Ω → Fin (K+1) → ℝ) (Y : Ω → ℝ),
    Measurable X → Measurable Y → (∀ ω, X ω 0 = 1) →
    ∀ (β : Fin (K+1) → ℝ) (s : ℝ), 0 < s →
    WholeConditionalLaw μ X Y (wholeNormalKernel β s) →
    (∀ x : Fin (K+1) → ℝ,
      (wholeNormalKernel β s x).map (fun y => y - wholeLinearMean β x) =
        gaussianReal 0 ⟨s^2, sq_nonneg _⟩) ∧
    WholeConditionalLaw μ X (fun ω => Y ω - wholeLinearMean β (X ω))
      (fun _ => gaussianReal 0 ⟨s^2, sq_nonneg _⟩) ∧
    μ.map (fun ω => Y ω - wholeLinearMean β (X ω)) =
      gaussianReal 0 ⟨s^2, sq_nonneg _⟩ ∧
    IndepFun X (fun ω => Y ω - wholeLinearMean β (X ω)) μ) ∧
  T73Statement

/-- P001-T68; p. 163 (PDF p. 181), Example 4.3.5.
The usual measure-theoretic conditions are assumed; g is measurable.
For independent integrable mean-zero noise and an integrable signal g(X),
the outcome Y = g(X) plus the noise is integrable and has g as a conditional
mean version: E[Y given X = x] = g(x). Equivalently, its conditional expectation
given the sigma algebra generated by X equals g(X) almost surely. -/
def T68WholeStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X ε : Ω → ℝ),
    Measurable X → Measurable ε → IndepFun X ε μ → Integrable ε μ →
    (∫ ω, ε ω ∂μ) = 0 → ∀ g : ℝ → ℝ, Measurable g → Integrable (g ∘ X) μ →
    Integrable (fun ω => g (X ω) + ε ω) μ ∧
    IsCEF μ X (fun ω => g (X ω) + ε ω) g ∧
    (g ∘ X) =ᵐ[μ] μ[(fun ω => g (X ω) + ε ω) | MeasurableSpace.comap X inferInstance]

end SAP.P001d
