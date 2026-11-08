import Mathlib
import SAP.P015a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015a

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

/-- The complex extension of the inverse logit. Its Taylor disks below contain no poles. -/
def complexInverseLogit (z : ℂ) : ℂ := (1 + Complex.exp (-z))⁻¹

/-- Distance from a real center to the nearest complex inverse-logit poles. -/
def inverseLogitRadius (c : ℝ) : ℝ := Real.sqrt (c ^ 2 + Real.pi ^ 2)

def inverseLogitCircleImage (c ρ : ℝ) : Set ℝ :=
  (fun z : ℂ => ‖complexInverseLogit z‖) '' Metric.sphere (c : ℂ) ρ

def inverseLogitErrorImage (c r : ℝ) (N : ℕ) : Set ℝ :=
  (fun a : ℝ => |inverseLogit a - inverseLogitTaylor N c a|) '' {a | |a - c| ≤ r}

/-- Two groups of 100 binary observations: one and 99 successes respectively. -/
def outsideTaylorDesign : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 1]

/-- The grouped Bernoulli likelihood is the likelihood of those 200 individual observations. -/
def outsideTaylorLikelihood (θ : Fin 2 → ℝ) : ℝ :=
  logLikelihood outsideTaylorDesign (fun _ => 100) ![1, 99] inverseLogit θ

def outsideTaylorWitness : Prop :=
  let L := Real.log 99
  let θ : Fin 2 → ℝ := ![-L, 2 * L]
  ((100 : ℝ) • (outsideTaylorDesign.transpose * outsideTaylorDesign)).det = 10000 ∧
  (∀ t, outsideTaylorLikelihood t ≤ outsideTaylorLikelihood θ) ∧
  (∀ t, outsideTaylorLikelihood t = outsideTaylorLikelihood θ → t = θ) ∧
  ((1 + 99 : ℝ) / 200 = 1 / 2 ∧ logOdds ((1 + 99) / 200) = 0) ∧
  outsideTaylorDesign.mulVec θ = ![-L, L] ∧
  Real.pi < L ∧
  (∀ i, inverseLogitRadius (logOdds ((1 + 99) / 200)) <
    |outsideTaylorDesign.mulVec θ i - logOdds ((1 + 99) / 200)|) ∧
  (∀ N : ℕ,
    49 / 100 ≤ |inverseLogit L - inverseLogitTaylor N 0 L| ∧
    49 / 100 ≤ |inverseLogit (-L) - inverseLogitTaylor N 0 (-L)|)

/-- P015-T12; p. 257 (PDF p. 8), left column. At logit(p), for 0 < p < 1, the
inverse-logit's first Taylor polynomial is p + p(1-p)(a-logit(p)), with a local
quadratic remainder. The complex Taylor radius is exactly sqrt(logit(p)^2+pi^2).
On every smaller real closed interval the Taylor errors have the stated uniform
Cauchy bound, using the attained finite maximum on an intermediate complex circle,
and this bound tends to zero. The explicit 200-observation, full-rank binary data
have a unique finite logistic ML estimate with both predictors outside the disk;
every Taylor degree has probability error at least 49/100 there. No accuracy of
coefficients or weights is asserted. -/
def T12WholeStatement : Prop :=
  (∀ p : ℝ, 0 < p → p < 1 →
    (∀ a, firstTaylorPolynomial inverseLogit (logOdds p) a =
      p + p * (1 - p) * (a - logOdds p)) ∧
    (fun a => inverseLogit a - (p + p * (1 - p) * (a - logOdds p)))
      =O[𝓝 (logOdds p)] (fun a => (a - logOdds p) ^ 2)) ∧
  (∀ p : ℝ, 0 < p → p < 1 →
    ∃ s : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt complexInverseLogit s (logOdds p : ℂ) ∧
      s.radius = ENNReal.ofReal (inverseLogitRadius (logOdds p))) ∧
  (∀ p r ρ : ℝ, 0 < p → p < 1 → 0 ≤ r → r < ρ →
    ρ < inverseLogitRadius (logOdds p) →
    let c := logOdds p
    let M := sSup (inverseLogitCircleImage c ρ)
    (inverseLogitCircleImage c ρ).Nonempty ∧
    BddAbove (inverseLogitCircleImage c ρ) ∧
    (∃ z ∈ Metric.sphere (c : ℂ) ρ, M = ‖complexInverseLogit z‖) ∧
    (∀ N : ℕ, (inverseLogitErrorImage c r N).Nonempty ∧
      BddAbove (inverseLogitErrorImage c r N) ∧
      sSup (inverseLogitErrorImage c r N) ≤ M * (r / ρ) ^ (N + 1) / (1 - r / ρ)) ∧
    Tendsto (fun N : ℕ => M * (r / ρ) ^ (N + 1) / (1 - r / ρ)) atTop (𝓝 0)) ∧
  outsideTaylorWitness

/-- The continuous linear functional represented by a finite coordinate gradient. -/
def scoreDifferential {q : ℕ} (g : Fin q → ℝ) : (Fin q → ℝ) →L[ℝ] ℝ :=
  ∑ j, g j • ContinuousLinearMap.proj j

def admissibleParameters {n q : ℕ} (W : Matrix (Fin n) (Fin q) ℝ)
    (I : Set ℝ) : Set (Fin q → ℝ) := {θ | ∀ i, W.mulVec θ i ∈ I}

/-- The actual vector derivative and the necessary likelihood equation at an admissible ML fit. -/
def wholeBernoulliScore : Prop :=
  ∀ (n K : ℕ) (W : Matrix (Fin n) (Fin (K + 2)) ℝ) (Y : Fin n → ℝ),
    (∀ i, Y i = 0 ∨ Y i = 1) → (∀ i, W i 0 = 1) →
    ∀ (I : Set ℝ), IsOpen I → ∀ m : ℝ → ℝ,
    DifferentiableOn ℝ m I → (∀ η ∈ I, 0 < m η ∧ m η < 1) →
    ∀ θ : Fin (K + 2) → ℝ, θ ∈ admissibleParameters W I →
    HasFDerivAt (logLikelihood W (fun _ => 1) Y m)
      (scoreDifferential (likelihoodScore W (fun _ => 1) Y m θ)) θ ∧
    ((∀ t ∈ admissibleParameters W I,
        logLikelihood W (fun _ => 1) Y m t ≤ logLikelihood W (fun _ => 1) Y m θ) →
      likelihoodScore W (fun _ => 1) Y m θ = 0)

def wholeLogisticScore : Prop :=
  (∀ η : ℝ,
    HasDerivAt inverseLogit (inverseLogit η * (1 - inverseLogit η)) η ∧
    likelihoodMultiplier inverseLogit η = 1 ∧
    deriv (likelihoodMultiplier inverseLogit) η = 0) ∧
  (∀ (n K : ℕ) (W : Matrix (Fin n) (Fin (K + 2)) ℝ)
      (Y : Fin n → ℝ) (θ : Fin (K + 2) → ℝ),
    likelihoodScore W (fun _ => 1) Y inverseLogit θ =
      residualEquation W (fun _ => 1) Y inverseLogit θ)

def canonicalGradient {n K : ℕ} (W : Matrix (Fin n) (Fin (K + 2)) ℝ)
    (κ : ℝ → ℝ) (s : ℝ) (Y : Fin n → ℝ) (θ : Fin (K + 2) → ℝ) :
    Fin (K + 2) → ℝ :=
  s⁻¹ • W.transpose.mulVec (fun i => Y i - deriv κ (W.mulVec θ i))

/-- No normalization or support assumptions are needed for this finite-sum calculus identity. -/
def wholeCanonicalScore : Prop :=
  ∀ (n K : ℕ) (W : Matrix (Fin n) (Fin (K + 2)) ℝ) (κ : ℝ → ℝ)
    (s : ℝ), 0 < s → ∀ (Y carrier : Fin n → ℝ) (θ : Fin (K + 2) → ℝ),
    (∀ i, DifferentiableAt ℝ κ (W.mulVec θ i)) →
    HasFDerivAt (canonicalSampleLikelihood W κ s Y carrier)
      (scoreDifferential (canonicalGradient W κ s Y θ)) θ ∧
    (canonicalGradient W κ s Y θ = 0 ↔
      W.transpose.mulVec (fun i => Y i - deriv κ (W.mulVec θ i)) = 0)

/-- Response law of a normalized scalar canonical family with a fixed reference measure. -/
def canonicalResponseLaw (ν : Measure ℝ) (κ : ℝ → ℝ) (s : ℝ)
    (carrier : ℝ → ℝ) (η : ℝ) : Measure ℝ :=
  ν.withDensity (fun y => ENNReal.ofReal (Real.exp (canonicalContribution κ s y (carrier y) η)))

/-- Normalized-family means and the local smoothness needed to linearize those means. -/
def wholeCanonicalMean : Prop :=
  ∀ (ν : Measure ℝ) (κ : ℝ → ℝ) (s : ℝ) (carrier : ℝ → ℝ) (I support : Set ℝ),
    ValidCanonicalFamily ν κ s carrier I support → DifferentiableOn ℝ κ I →
    ∀ η ∈ I,
      IsProbabilityMeasure (canonicalResponseLaw ν κ s carrier η) ∧
      Integrable (fun y : ℝ => y) (canonicalResponseLaw ν κ s carrier η) ∧
      (∫ y : ℝ, y ∂canonicalResponseLaw ν κ s carrier η) = deriv κ η ∧
      AnalyticAt ℝ κ η ∧ DifferentiableAt ℝ (deriv κ) η

def wholeNamedCanonicalMeans : Prop :=
  ∀ η : ℝ,
    (IsProbabilityMeasure (logisticResponseLaw η) ∧
      Integrable (fun y : ℝ => y) (logisticResponseLaw η) ∧
      (∫ y : ℝ, y ∂logisticResponseLaw η) = inverseLogit η ∧
      inverseLogit η = deriv (fun a : ℝ => Real.log (1 + Real.exp a)) η) ∧
    (IsProbabilityMeasure (poissonLogResponseLaw η) ∧
      Integrable (fun y : ℕ => (y : ℝ)) (poissonLogResponseLaw η) ∧
      (∫ y : ℕ, (y : ℝ) ∂poissonLogResponseLaw η) = Real.exp η ∧
      Real.exp η = deriv Real.exp η)

def wholeProbitScore : Prop :=
  (∀ (n K : ℕ) (W : Matrix (Fin n) (Fin (K + 2)) ℝ) (Y : Fin n → ℝ),
    (∀ i, Y i = 0 ∨ Y i = 1) → (∀ i, W i 0 = 1) →
    ∀ θ : Fin (K + 2) → ℝ,
      HasFDerivAt (logLikelihood W (fun _ => 1) Y standardNormalCDF)
        (scoreDifferential (fun j => ∑ i, W i j * probitMultiplier (W.mulVec θ i) *
          (Y i - standardNormalCDF (W.mulVec θ i)))) θ) ∧
  (∀ η : ℝ, likelihoodMultiplier standardNormalCDF η = probitMultiplier η) ∧
  (∀ η : ℝ, 0 < probitMultiplier η) ∧
  (¬ ∃ c : ℝ, ∀ η : ℝ, probitMultiplier η = c) ∧
  (standardNormalCDF 0 = 1 / 2 ∧ deriv probitMultiplier 0 = 0) ∧
  T6Statement

def interceptVector (K : ℕ) (η : ℝ) : Fin (K + 2) → ℝ :=
  fun j => if j = 0 then η else 0

def affineParameter (K : ℕ) (b c : ℝ) (θ : Fin (K + 2) → ℝ) : Fin (K + 2) → ℝ :=
  interceptVector K b + c • θ

def centeredResidual {n K : ℕ} (W : Matrix (Fin n) (Fin (K + 2)) ℝ)
    (Y : Fin n → ℝ) (p : ℝ) : Fin (K + 2) → ℝ :=
  W.transpose.mulVec (fun i => Y i - p)

def residualMoment {n K : ℕ} (W : Matrix (Fin n) (Fin (K + 2)) ℝ)
    (Y : Fin n → ℝ) (p : ℝ) : Matrix (Fin (K + 2)) (Fin (K + 2)) ℝ :=
  fun j k => ∑ i, (Y i - p) * W i j * W i k

def fullScoreTaylor {n K : ℕ} (W : Matrix (Fin n) (Fin (K + 2)) ℝ)
    (Y : Fin n → ℝ) (m : ℝ → ℝ) (η₀ : ℝ) (δ : Fin (K + 2) → ℝ) : Fin (K + 2) → ℝ :=
  fun j => ∑ i, W i j * firstTaylorPolynomial
    (fun η => likelihoodMultiplier m η * (Y i - m η)) η₀ (η₀ + W.mulVec δ i)

/-- The mean-only Taylor residual equation is an OLS normal equation, for any scalar mean. -/
def wholeResidualLinearization : Prop :=
  ∀ (n K : ℕ) (W : Matrix (Fin n) (Fin (K + 2)) ℝ) (Y : Fin n → ℝ),
    (∀ i, W i 0 = 1) → ∀ (m : ℝ → ℝ) (η₀ : ℝ), DifferentiableAt ℝ m η₀ →
    let p₀ := m η₀
    let f₀ := deriv m η₀
    let r := centeredResidual W Y p₀
    let A := W.transpose * W
    (∀ δ,
      (residualEquation W (fun _ => 1) Y (firstTaylorPolynomial m η₀)
        (interceptVector K η₀ + δ) = 0 ↔ f₀ • A.mulVec δ = r) ∧
      (W.transpose.mulVec (fun i => Y i - W.mulVec
        (affineParameter K (p₀ - f₀ * η₀) f₀ (interceptVector K η₀ + δ)) i) = 0 ↔
          f₀ • A.mulVec δ = r)) ∧
    (f₀ ≠ 0 → ∀ θ,
      affineParameter K (-(p₀ - f₀ * η₀) / f₀) f₀⁻¹
        (affineParameter K (p₀ - f₀ * η₀) f₀ θ) = θ ∧
      affineParameter K (p₀ - f₀ * η₀) f₀
        (affineParameter K (-(p₀ - f₀ * η₀) / f₀) f₀⁻¹ θ) = θ)

/-- Exact score-polynomial identity, its zero equation, and the mean-only OLS equation. -/
def wholeScoreLinearization : Prop :=
  ∀ (n K : ℕ) (W : Matrix (Fin n) (Fin (K + 2)) ℝ) (Y : Fin n → ℝ),
    (∀ i, Y i = 0 ∨ Y i = 1) → (∀ i, W i 0 = 1) →
    ∀ (I : Set ℝ), IsOpen I → ∀ m : ℝ → ℝ,
    DifferentiableOn ℝ m I → (∀ η ∈ I, 0 < m η ∧ m η < 1) →
    ∀ η₀ p₀ : ℝ, η₀ ∈ I → 0 < p₀ → p₀ < 1 → m η₀ = p₀ →
    DifferentiableAt ℝ (deriv m) η₀ →
    let f₀ := deriv m η₀
    let h₀ := likelihoodMultiplier m η₀
    let h₁ := deriv (likelihoodMultiplier m) η₀
    let r := centeredResidual W Y p₀
    let A := W.transpose * W
    let B := residualMoment W Y p₀
    (∀ δ, fullScoreTaylor W Y m η₀ δ = h₀ • r + ((-h₀ * f₀) • A + h₁ • B).mulVec δ) ∧
    (h₀ ≠ 0 → f₀ ≠ 0 ∧
      (∀ δ, fullScoreTaylor W Y m η₀ δ = 0 ↔
        (f₀ • A - (h₁ / h₀) • B).mulVec δ = r) ∧
      (∀ δ, h₁ = 0 ∨ B.mulVec δ = 0 →
        (f₀ • A - (h₁ / h₀) • B).mulVec δ = f₀ • A.mulVec δ))

/-- Finite Cox partial likelihood, retaining the risk sets as part of the model. -/
def finiteCoxLikelihood {n q e : ℕ} (Z : Matrix (Fin n) (Fin q) ℝ)
    (event : Fin e → Fin n) (risk : Fin e → Finset (Fin n)) (θ : Fin q → ℝ) : ℝ :=
  ∑ k, (Z.mulVec θ (event k) - Real.log (∑ j ∈ risk k, Real.exp (Z.mulVec θ j)))

def finiteCoxScore {n q e : ℕ} (Z : Matrix (Fin n) (Fin q) ℝ)
    (event : Fin e → Fin n) (risk : Fin e → Finset (Fin n)) (θ : Fin q → ℝ) : Fin q → ℝ :=
  fun a => ∑ k, (Z (event k) a -
    (∑ j ∈ risk k, Real.exp (Z.mulVec θ j) * Z j a) /
      (∑ j ∈ risk k, Real.exp (Z.mulVec θ j)))

def wholeCoxIllustration : Prop :=
  (∀ (n q e : ℕ) (Z : Matrix (Fin n) (Fin q) ℝ) (event : Fin e → Fin n)
      (risk : Fin e → Finset (Fin n)), (∀ k, event k ∈ risk k) →
      ∀ θ : Fin q → ℝ,
        (∀ k, 0 < ∑ j ∈ risk k, Real.exp (Z.mulVec θ j)) ∧
        HasFDerivAt (finiteCoxLikelihood Z event risk)
          (scoreDifferential (finiteCoxScore Z event risk θ)) θ) ∧
  (let Z : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 1]
    let event : Fin 1 → Fin 2 := fun _ => 0
    finiteCoxScore Z event (fun _ => {0}) 0 1 = 0 ∧
    finiteCoxScore Z event (fun _ => {0, 1}) 0 1 = -1 / 2)

/-- P015-T8; pp. 264–265 (PDF pp. 15–16); main text pp. 256–257 (PDF pp. 7–8).
The Bernoulli gradient is the residual score multiplied by m'/(m(1-m)); an admissible
ML fit satisfies its zero equation. Logistic has multiplier one. Common-dispersion
scalar canonical families have gradient s^-1 times the residual score, with mean κ'
for their normalized response laws and locally analytic cumulants, including
Bernoulli logit and Poisson log link.
Probit has the nonconstant normal-density multiplier and the explicit residual-root
counterexample. The exact first Taylor polynomial of the full score includes h' B;
division by a nonzero h gives its linearized equation, while mean-only linearization
gives the OLS normal equation after an invertible affine reparameterization. The
equations coincide when h'=0 or Bδ=0; logistic and symmetric probit give the first
case, and the square-link causal model exhibits a discrepancy in general. These
are Taylor-polynomial identities. No nonlinear-score quadratic remainder or blanket
extension to ordered, multinomial, or duration models is asserted. The Cox score
illustrates the additional risk-set terms and their dependence on the risk sets. -/
def T8WholeStatement : Prop :=
  wholeBernoulliScore ∧ wholeLogisticScore ∧ wholeCanonicalScore ∧ wholeCanonicalMean ∧
  wholeNamedCanonicalMeans ∧ wholeProbitScore ∧ wholeResidualLinearization ∧ wholeScoreLinearization ∧
  T7Statement ∧ wholeCoxIllustration

end
end SAP.P015a
