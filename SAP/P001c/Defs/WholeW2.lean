import Mathlib
import SAP.P001c.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical ContDiff
universe u
noncomputable section

/-- Definition 3.2.20. Only sample sizes at least two are used for finite-sample claims. -/
def unbiasedSampleVariance {Ω : Type u} (X : ℕ → Ω → ℝ) (n : ℕ) (z : Ω) : ℝ :=
  (n : ℝ) / ((n : ℝ) - 1) * pluginVariance X n z

/-- Theorem 3.2.33: the unbiased sample variance divided by the sample size. -/
def wholeMeanVarianceEstimate {Ω : Type u} (X : ℕ → Ω → ℝ) (n : ℕ) (z : Ω) : ℝ :=
  unbiasedSampleVariance X n z / (n : ℝ)

/-- P001-T55; Definition 3.2.32 and footnote 23, pp. 113–114 (PDF pp. 131–132);
Definition 3.2.20, p. 107 (PDF p. 125), and Theorem 3.2.33, p. 114 (PDF p. 132).
With the estimator's hats restored, variance and standard-error consistency are equivalent
to their centered forms and to each other. For iid observations of finite positive variance,
the unbiased sample variance is n/(n−1) times the plug-in variance; divided by n it is an
unbiased estimator of the sample mean's variance, for n at least two. The exact identity
n Var(sample mean)=Var(X), the root-n limit, both consistencies and both centered forms hold.
The usual measure-theoretic conditions are assumed. -/
def T55WholeStatement : Prop :=
  (∀ {Ω : Type u} [MeasurableSpace Ω], T55Statement Ω) ∧
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), isIID μ X → MemLp (X 0) 2 μ → ∀ (hv : 0 < variance (X 0) μ),
    let S := unbiasedSampleVariance X
    let V := wholeMeanVarianceEstimate X
    (∀ n, Measurable (V n)) ∧ (∀ n z, 0 ≤ V n z) ∧
    (∀ n, 2 ≤ n → ∀ z,
      S n z = (∑ i ∈ Finset.range n, (X i z - sampleAverage X n z)^2) / ((n : ℝ)-1) ∧
      V n z = pluginVariance X n z / ((n : ℝ)-1)) ∧
    (∀ n, 2 ≤ n → expectation μ (S n) = variance (X 0) μ ∧
      expectation μ (V n) = variance (sampleAverage X n) μ) ∧
    (∀ n : ℕ, 0 < n → (n : ℝ) * variance (sampleAverage X n) μ = variance (X 0) μ) ∧
    convergesInDistribution μ
      (fun n z => Real.sqrt n * (sampleAverage X n z - expectation μ (X 0)))
      (gaussianReal 0 ⟨variance (X 0) μ, le_of_lt hv⟩) ∧
    varianceConsistent μ V (variance (X 0) μ) ∧
    standardErrorConsistent μ V (variance (X 0) μ) ∧
    (∀ n : ℕ, 0 < n → ∀ z,
      (n : ℝ)*V n z - (n : ℝ)*variance (sampleAverage X n) μ =
        (n : ℝ)*V n z - variance (X 0) μ) ∧
    convergesInProbability μ
      (fun n z => (n : ℝ)*V n z - (n : ℝ)*variance (sampleAverage X n) μ) 0 ∧
    convergesInProbability μ (fun n z => (n : ℝ)*V n z - variance (X 0) μ) 0 ∧
    convergesInProbability μ
      (fun n z => Real.sqrt n * Real.sqrt (V n z) - Real.sqrt (variance (X 0) μ)) 0

/-- A smooth, nonsingular mixture used to witness the normal-marginal non-implication. -/
def normalMixtureDensity (xy : ℝ × ℝ) : ℝ :=
  (bivariatePDF 0 0 1 1 (3/5) xy + bivariatePDF 0 0 1 1 (-3/5) xy) / 2

def normalMixtureLaw : Measure (ℝ × ℝ) :=
  volume.withDensity (fun xy => ENNReal.ofReal (normalMixtureDensity xy))

/-- Bivariate-normal conclusions for arbitrary random variables with the displayed joint law. -/
def wholeBivariateTransport : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), Measurable X → Measurable Y →
    ∀ mx my sx sy ρ : ℝ, 0 < sx → 0 < sy → ρ ∈ Set.Ioo (-1 : ℝ) 1 →
    μ.map (fun z => (X z, Y z)) =
      volume.withDensity (fun xy => ENNReal.ofReal (bivariatePDF mx my sx sy ρ xy)) →
    MemLp X 2 μ ∧ MemLp Y 2 μ ∧
    μ.map X = gaussianReal mx ⟨sx^2, sq_nonneg sx⟩ ∧
    μ.map Y = gaussianReal my ⟨sy^2, sq_nonneg sy⟩ ∧
    expectation μ X = mx ∧ expectation μ Y = my ∧
    Real.sqrt (variance X μ) = sx ∧ Real.sqrt (variance Y μ) = sy ∧
    correlationCoefficient μ X Y = ρ ∧ (ρ = 0 → IndepFun X Y μ)

/-- P001-T39; Theorem 2.1.21 and following sentence, p. 56 (PDF p. 74),
Definition 2.1.19 and Theorem 2.1.20, pp. 55–56 (PDF pp. 73–74), and footnote 13,
p. 66 (PDF p. 84).
Normal variables have their specified mean and standard deviation. Every nontrivial finite
affine combination of mutually independent normal variables is normal, including the affine
and two-variable sum cases. The displayed bivariate density is a probability density with
its specified moments, marginal normal laws and correlation, and gives independence and
pointwise density factorization at zero correlation. These conclusions transfer to every
pair with that joint law. Normal marginals and zero correlation alone do not imply
independence: the equal mixture with correlations 3/5 and −3/5 is a counterexample.
The usual measure-theoretic conditions are assumed. -/
def T39WholeStatement : Prop :=
  (∀ {Ω : Type u} [MeasurableSpace Ω], T39Statement Ω) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ), Measurable X → ∀ m s : ℝ, 0 < s →
    μ.map X = gaussianReal m ⟨s^2, sq_nonneg s⟩ →
    MemLp X 2 μ ∧ expectation μ X = m ∧ Real.sqrt (variance X μ) = s) ∧
  wholeBivariateTransport.{u} ∧
  IsProbabilityMeasure normalMixtureLaw ∧ isJointDensity normalMixtureLaw normalMixtureDensity ∧
  normalMixtureLaw.map Prod.fst = gaussianReal 0 1 ∧
  normalMixtureLaw.map Prod.snd = gaussianReal 0 1 ∧
  MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 normalMixtureLaw ∧
  MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 normalMixtureLaw ∧
  correlationCoefficient normalMixtureLaw Prod.fst Prod.snd = 0 ∧
  ¬ IndepFun Prod.fst Prod.snd normalMixtureLaw

/-- All first and second partials are actual derivative certificates, including both mixed orders. -/
def wholeRiskCalculus {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ContDiff ℝ ∞ (fun p : ℝ × ℝ => affineRisk μ X Y p.1 p.2) ∧
  (∀ a b : ℝ,
    HasDerivAt (fun t => affineRisk μ X Y t b)
      (-2*expectation μ (fun z => Y z-a-b*X z)) a ∧
    HasDerivAt (fun t => affineRisk μ X Y a t)
      (-2*expectation μ (fun z => (Y z-a-b*X z)*X z)) b ∧
    HasDerivAt (fun t => deriv (fun u => affineRisk μ X Y u b) t) 2 a ∧
    HasDerivAt (fun t => deriv (fun u => affineRisk μ X Y a u) t)
      (2*expectation μ (fun z => (X z)^2)) b ∧
    HasDerivAt (fun t => deriv (fun u => affineRisk μ X Y u t) a)
      (2*expectation μ X) b ∧
    HasDerivAt (fun t => deriv (fun u => affineRisk μ X Y t u) b)
      (2*expectation μ X) a) ∧
  2*(2*expectation μ (fun z => (X z)^2))-(2*expectation μ X)^2 = 4*variance X μ

/-- The positive-variance BLP theorem, the CEF corollaries and residual identities. -/
def wholePositiveBlp {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  (∀ a b : ℝ, (expectation μ (fun z => Y z-a-b*X z)=0 ∧
    expectation μ (fun z => (Y z-a-b*X z)*X z)=0) ↔
    a=regressionIntercept μ X Y ∧ b=regressionSlope μ X Y) ∧
  (∀ a b : ℝ, affineRisk μ X Y (regressionIntercept μ X Y) (regressionSlope μ X Y) ≤
    affineRisk μ X Y a b ∧
    (affineRisk μ X Y a b=affineRisk μ X Y (regressionIntercept μ X Y) (regressionSlope μ X Y) ↔
      a=regressionIntercept μ X Y ∧ b=regressionSlope μ X Y)) ∧
  0 < 4*variance X μ ∧
  expectation μ (fun z => Y z-(regressionIntercept μ X Y+regressionSlope μ X Y*X z))=0 ∧
  expectation μ (fun z => X z*(Y z-(regressionIntercept μ X Y+regressionSlope μ X Y*X z)))=0 ∧
  covariance X (fun z => Y z-(regressionIntercept μ X Y+regressionSlope μ X Y*X z)) μ=0 ∧
  (∀ m : ℝ → ℝ, isConditionalMean μ X Y m →
    (∀ a b : ℝ, affineRisk μ X (m ∘ X) (regressionIntercept μ X Y) (regressionSlope μ X Y) ≤
      affineRisk μ X (m ∘ X) a b) ∧
    (∀ a b : ℝ, isConditionalMean μ X Y (fun x => a+b*x) →
      ∀ᵐ z ∂μ, m (X z)=regressionIntercept μ X Y+regressionSlope μ X Y*X z))

/-- Footnote 18, including arbitrary functions, all affine minimizers and their residuals. -/
def wholeZeroBlp {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  X =ᵐ[μ] (fun _ => expectation μ X) ∧
  (∀ g h : ℝ → ℝ, Measurable (g ∘ X) → Measurable (h ∘ X) →
    g (expectation μ X) = expectation μ Y →
    expectation μ (fun z => (Y z-g (X z))^2) = variance Y μ ∧
    expectation μ (fun z => (Y z-g (X z))^2) ≤
      expectation μ (fun z => (Y z-h (X z))^2)) ∧
  (∀ a b : ℝ,
    (affineRisk μ X Y a b = variance Y μ ↔ a+b*expectation μ X=expectation μ Y) ∧
    (a+b*expectation μ X=expectation μ Y →
      expectation μ (fun z => Y z-(a+b*X z))=0 ∧
      expectation μ (fun z => X z*(Y z-(a+b*X z)))=0 ∧
      covariance X (fun z => Y z-(a+b*X z)) μ=0))

/-- P001-T43; Theorem 2.2.21, proof and footnotes 18–19, pp. 76–78
(PDF pp. 94–96); corollaries, p. 78 (PDF p. 96); Theorem 2.2.22, p. 79 (PDF p. 97).
For measurable square-integrable X,Y, affine prediction risk is jointly smooth with the
corrected first partials, all second partials and Hessian determinant 4 Var(X). A Borel CEF
version exists, and every such version is square integrable. Positive regressor variance
gives exactly the BLP coefficients as the unique normal-equation solution and unique risk
minimizer; the BLP best approximates every CEF version and has all three residual
orthogonalities. If a CEF version is affine, the BLP agrees almost surely with every
CEF version. At zero regressor variance, every function
sending E[X] to E[Y] minimizes MSE, and all affine minimizers and their residuals are described.
The usual measure-theoretic conditions are assumed. -/
def T43WholeStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), Measurable X → Measurable Y → MemLp X 2 μ → MemLp Y 2 μ →
    wholeRiskCalculus μ X Y ∧
    (∃ m : ℝ → ℝ, isConditionalMean μ X Y m ∧ MemLp (m ∘ X) 2 μ) ∧
    (∀ m : ℝ → ℝ, isConditionalMean μ X Y m → MemLp (m ∘ X) 2 μ) ∧
    (0 < variance X μ → wholePositiveBlp μ X Y) ∧
    (variance X μ = 0 → wholeZeroBlp μ X Y)

/-- P001-T46; Examples 2.2.23–24, pp. 79–82 (PDF pp. 97–100);
Theorems 2.2.21 and 2.2.25, pp. 76 and 82–83 (PDF pp. 94 and 100–101).
For independent uniform X and standard normal W, Y=10X²+W has CEF 10X². The conditional
square equals X², the conditional noise mean is zero, and conditional linearity gives the
displayed calculation. The stated moments yield slope 10, intercept −5/3 and the unique
affine minimum. In general the covariance/variance BLP coefficients uniquely minimize
risk at positive regressor variance, and independent integrable outcomes have constant CEFs.
The usual measure-theoretic conditions are assumed. -/
def T46WholeStatement : Prop :=
  (∀ {Ω : Type u} [MeasurableSpace Ω], T46Statement Ω) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), Measurable X → Measurable Y → MemLp X 2 μ → MemLp Y 2 μ →
    0 < variance X μ → ∀ a b : ℝ,
      affineRisk μ X Y (regressionIntercept μ X Y) (regressionSlope μ X Y) ≤
        affineRisk μ X Y a b ∧
      (affineRisk μ X Y a b=affineRisk μ X Y (regressionIntercept μ X Y) (regressionSlope μ X Y) ↔
        a=regressionIntercept μ X Y ∧ b=regressionSlope μ X Y)) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), Measurable X → Measurable Y → Integrable Y μ → IndepFun X Y μ →
    isConditionalMean μ X Y (fun _ => expectation μ Y)) ∧
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X W : Ω → ℝ), Measurable X → Measurable W → IndepFun X W μ →
    μ.map X=intervalUniform 0 1 → μ.map W=gaussianReal 0 1 →
    let Y := fun z => 10*(X z)^2+W z
    isConditionalMean μ X (fun z => (X z)^2) (fun x => x^2) ∧
    isConditionalMean μ X W (fun _ => 0) ∧
    (μ[Y | MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ)] =ᵐ[μ] fun z => 10 * μ[(fun z => (X z)^2) | MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ)] z + μ[W | MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ)] z) ∧
    (μ[Y | MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ)] =ᵐ[μ] fun z => 10*(X z)^2) ∧
    covariance X Y μ = 10*(expectation μ (fun z => (X z)^3) -
      expectation μ X * expectation μ (fun z => (X z)^2)) ∧
    regressionSlope μ X Y =
      10*((1/4)-(1/2)*(1/3))/((1/3)-(1/2)^2) ∧
    regressionIntercept μ X Y = (10/3)-10/2

/-- Product uniform law used for the trace-space counterexample. -/
def uniformSquareLaw : Measure (ℝ × ℝ) := (intervalUniform 0 1).prod (intervalUniform 0 1)

/-- Constant-mean affine optimality under independence, including the zero-variance case
and uniqueness of the coefficients when the regressor variance is positive. -/
def wholeIndependentBlp {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  (∀ a b : ℝ, affineRisk μ X Y (expectation μ Y) 0 ≤ affineRisk μ X Y a b) ∧
  (0 < variance X μ → regressionSlope μ X Y = 0 ∧
    regressionIntercept μ X Y = expectation μ Y ∧
    ∀ a b : ℝ,
      (affineRisk μ X Y a b = affineRisk μ X Y (expectation μ Y) 0 ↔
        a = expectation μ Y ∧ b = 0))

/-- P001-T47; Theorem 2.2.25, pp. 82–83 (PDF pp. 100–101), with sub-bullet (a)
corrected to E[h(Y)|g(X)]=E[h(Y)]; Theorems 1.3.17, 2.2.8 and 2.2.21, pp. 39, 64
and 76 (PDF pp. 57, 82 and 94).
The usual measure-theoretic conditions are assumed; in particular, functions of random
variables are measurable functions. Independence is equivalent to independence of every
pair of measurable transformations. Independent variables have constant conditional mean
and conditional variance, factorized product expectation, zero covariance and correlation,
and additive variance. The constant outcome mean is a best affine predictor, uniquely so
in coefficients at positive regressor variance. The corrected transformed conditional-mean
and BLP conclusions hold with the same clause-specific existence conditions. The general
positive-variance BLP coefficient and unique-minimum theorem is included. -/
def T47WholeStatement : Prop :=
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), Measurable X → Measurable Y →
    (IndepFun X Y μ ↔ ∀ g h : ℝ → ℝ, Measurable g → Measurable h →
      IndepFun (g ∘ X) (h ∘ Y) μ)) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), Measurable X → Measurable Y → IndepFun X Y μ →
    (Integrable Y μ → isConditionalMean μ X Y (fun _ => expectation μ Y)) ∧
    (MemLp Y 2 μ → isConditionalMean μ X (fun z => (Y z-expectation μ Y)^2)
      (fun _ => variance Y μ)) ∧
    (Integrable X μ → Integrable Y μ →
      Integrable (fun z => X z * Y z) μ ∧
      expectation μ (fun z => X z * Y z) = expectation μ X * expectation μ Y ∧
      covariance X Y μ = 0) ∧
    (MemLp X 2 μ → MemLp Y 2 μ →
      variance (fun z => X z + Y z) μ = variance X μ + variance Y μ ∧
      (0 < variance X μ → 0 < variance Y μ → correlationCoefficient μ X Y = 0) ∧
      wholeIndependentBlp μ X Y) ∧
    (∀ g h : ℝ → ℝ, Measurable g → Measurable h →
      IndepFun (g ∘ X) (h ∘ Y) μ ∧
      (Integrable (h ∘ Y) μ → isConditionalMean μ (g ∘ X) (h ∘ Y)
        (fun _ => expectation μ (h ∘ Y))) ∧
      (MemLp (g ∘ X) 2 μ → MemLp (h ∘ Y) 2 μ →
        wholeIndependentBlp μ (g ∘ X) (h ∘ Y)))) ∧
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), Measurable X → Measurable Y → MemLp X 2 μ → MemLp Y 2 μ →
    0 < variance X μ → ∀ a b : ℝ,
      affineRisk μ X Y (regressionIntercept μ X Y) (regressionSlope μ X Y) ≤
        affineRisk μ X Y a b ∧
      (affineRisk μ X Y a b = affineRisk μ X Y (regressionIntercept μ X Y) (regressionSlope μ X Y) ↔
        a = regressionIntercept μ X Y ∧ b = regressionSlope μ X Y)

end
end SAP.P001c
