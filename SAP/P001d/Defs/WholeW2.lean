import Mathlib
import SAP.P001d.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The ordinary real CDF domain, including its endpoint and one-sided continuity conditions. -/
def WholeCDF (G : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ G x ∧ G x ≤ 1) ∧ Monotone G ∧
  (∀ x, Tendsto G (nhdsWithin x (Set.Ici x)) (nhds (G x))) ∧
  Tendsto G atBot (nhds 0) ∧ Tendsto G atTop (nhds 1)

/-- The triangular density on [5/4,7/4], with height 4 at 3/2. -/
def wholeTrianglePDF (x : ℝ) : ℝ := max 0 (4 - 16 * |x - 3/2|)

def wholeTriangleLaw : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (wholeTrianglePDF x))

/-- A statistical functional whose domain really is the set of CDFs. -/
def wholeSqrtFunctional (G : {G : ℝ → ℝ // WholeCDF G}) : ℝ := Real.sqrt (G.val 0)

/-- The finite empirical CDF. Every use as a CDF below is guarded by n > 0. -/
def wholeEmpiricalCDF {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter (fun i => x i ≤ t)).card : ℝ) / (n : ℝ)

/-- The lower middle order statistic, equal to the empirical half-quantile for n > 0. -/
def wholeLowerMedian {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ((List.ofFn x).mergeSort (fun a b => a ≤ b)).getD ((n-1)/2) 0

/-- The specified CDF functional itself, including its lower-quantile branch at even sizes. -/
def wholeRegularStatistic {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  regularHeavyFunctional (wholeEmpiricalCDF x)

/-- The centered empirical sign fraction; its resampling law is binomial. -/
def wholeSignStatistic {n : ℕ} (x : Fin n → ℝ) : ℝ := wholeEmpiricalCDF x 0 - 1/2

/-- Probability under the exact n-out-of-n uniform label law, for n > 0. -/
def wholeResampleProb {n : ℕ} (A : (Fin n → Fin n) → Prop) : ℝ :=
  (∑ a, if A a then (1 : ℝ) else 0) / (n : ℝ)^n

/-- Sequential Hadamard derivative h ↦ h(0) on the space of all bounded functions
with uniform convergence. No CDF, continuity, or support restriction is imposed on directions.
The total function is a local extension of its restriction to the CDF domain. -/
def WholeHadamardEvaluation (T : (ℝ → ℝ) → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ h : ℝ → ℝ, BddAbove (Set.range (fun x => |h x|)) →
    ∀ (t : ℕ → ℝ) (v : ℕ → ℝ → ℝ),
      (∀ n, 0 < t n) → Tendsto t atTop (nhds 0) →
      (∀ n, BddAbove (Set.range (fun x => |v n x|))) →
      TendstoUniformly v h atTop →
      Tendsto (fun n => (T (fun x => F x + t n * v n x) - T F) / t n)
        atTop (nhds (h 0))

def wholeUnsquared {n J : ℕ} (x y : Fin n → ℝ) (b : Fin (J+1) → ℝ) : ℝ :=
  ∑ i, (y i - ∑ k, b k * x i ^ k.val)

/-- Definition 4.3.9, pp. 168–169 (PDF pp. 186–187).
For every nonempty sample the printed unsquared polynomial criterion has its affine
expansion, tends to minus infinity as the intercept grows, and has no minimizer.
The corrected criterion is the OLS sum of squared residuals. Invertibility of the
polynomial Gram matrix requires at least J+1 distinct observed covariate values and
gives the unique inverse-formula minimizer. These assertions hold at every finite
degree, hence also at the degrees of any sieve sequence with the printed rates. -/
def T70WholeStatement : Prop :=
  T70Statement ∧
  ∀ {n : ℕ}, 0 < n → ∀ (J : ℕ) (x y : Fin n → ℝ),
    (∀ b : Fin (J+1) → ℝ, wholeUnsquared x y b =
      (∑ i, y i) - (n : ℝ)*b 0 - ∑ k : Fin J, b k.succ * ∑ i, x i ^ k.succ.val) ∧
    (∀ b : Fin (J+1) → ℝ,
      Tendsto (fun a : ℝ => wholeUnsquared x y (Function.update b 0 a)) atTop atBot) ∧
    (IsUnit ((polynomialDesign x J).transpose * polynomialDesign x J).det →
      J+1 ≤ (Finset.univ.image x).card)

def wholeFiniteVariance (Y : Fin 4 → ℝ) : ℝ :=
  finiteMean (fun i => (Y i - finiteMean Y)^2)

def wholeFiniteCondVariance (Y X : Fin 4 → ℝ) (x : ℝ) : ℝ :=
  finiteCond (fun i => (Y i - finiteCond Y X x)^2) X x

/-- Section 5.1.1, p. 181 (PDF p. 199); Theorem 2.2.19, p. 74 (PDF p. 92).
The printed claim is false: on the four equiprobable atoms (X,Y)=(0,1),(0,3),
(1,0),(1,6), the CEF is 2+X and its residuals are -1,1,-3,3, each with mass 1/4.
Their conditional and unconditional means vanish; their covariance with every g(X)
vanishes. The conditional outcome and residual variances agree and are 1 and 9;
the residual variance and the mean conditional outcome variance are both 5.
Nevertheless the displayed joint probability is 1/2 and the product is 1/4,
so CEF residuals need not be independent of X, even for a linear CEF. -/
def T73WholeStatement : Prop :=
  T73Statement ∧
  heteroResidual = ![-1, 1, -3, 3] ∧
  (∀ r : ℝ, finiteProb (fun i => heteroResidual i = r) =
    if r ∈ ({-1, 1, -3, 3} : Set ℝ) then 1/4 else 0) ∧
  (∀ i : Fin 4, finiteCond heteroY heteroX (heteroX i) = 2 + heteroX i) ∧
  (∀ x ∈ ({0, 1} : Set ℝ), finiteCond heteroResidual heteroX x = 0) ∧
  (∀ g : ℝ → ℝ, finiteCov (g ∘ heteroX) heteroResidual = 0) ∧
  (∀ x ∈ ({0, 1} : Set ℝ),
    wholeFiniteCondVariance heteroResidual heteroX x = wholeFiniteCondVariance heteroY heteroX x ∧
    wholeFiniteCondVariance heteroY heteroX x = if x = 0 then 1 else 9) ∧
  wholeFiniteVariance heteroResidual = 5 ∧
  finiteMean (fun i => wholeFiniteCondVariance heteroY heteroX (heteroX i)) = 5

/-- Definitions 3.3.7 and 3.3.9, pp. 121,123 (PDF pp. 139,141);
Definition 3.3.2, p. 118 (PDF p. 136).
The printed claim is false: the admitted even normalized signed kernel gives a
negative integrated estimate at a-1 and a strictly decreasing estimate on (a-2,a-1).
For the continuous triangular population density on [5/4,7/4], every nonempty
sample in that interval gives an integrated estimate at zero in [-3/8,-1/8].
Thus with probability one it is outside the CDF domain of the fixed functional
G ↦ sqrt(G(0)), and its value at zero has no real square root. -/
def T58WholeStatement : Prop :=
  T58Statement ∧
  (∀ a : ℝ, StrictAntiOn (kernelCDF signedKernel 1 (fun _ : Fin 1 => a))
      (Set.Ioo (a-2) (a-1)) ∧
    ¬ WholeCDF (kernelCDF signedKernel 1 (fun _ : Fin 1 => a))) ∧
  Continuous wholeTrianglePDF ∧ (∀ x, 0 ≤ wholeTrianglePDF x) ∧
  (∀ x, wholeTrianglePDF x = 0 ↔ x ∉ Set.Ioo (5/4 : ℝ) (7/4)) ∧
  Integrable wholeTrianglePDF volume ∧ (∫ x, wholeTrianglePDF x) = 1 ∧
  IsProbabilityMeasure wholeTriangleLaw ∧
  WholeCDF (cdf wholeTriangleLaw id) ∧ cdf wholeTriangleLaw id 0 = 0 ∧
  (∀ {n : ℕ}, 0 < n → ∀ x : Fin n → ℝ,
    (∀ i, x i ∈ Set.Icc (5/4 : ℝ) (7/4)) →
    kernelCDF signedKernel 1 x 0 = (∑ i, (x i-2)/2)/(n : ℝ) ∧
    kernelCDF signedKernel 1 x 0 ∈ Set.Icc (-3/8 : ℝ) (-1/8)) ∧
  (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), IID μ X → μ.map (X 0) = wholeTriangleLaw →
    ∀ᵐ ω ∂μ, ∀ n : ℕ, 0 < n →
      kernelCDF signedKernel 1 (firstSample X n ω) 0 ∈ Set.Icc (-3/8 : ℝ) (-1/8) ∧
      ¬ WholeCDF (kernelCDF signedKernel 1 (firstSample X n ω)) ∧
      ¬ ∃ r : ℝ, r^2 = kernelCDF signedKernel 1 (firstSample X n ω) 0)

/-- P001-T61, p. 131 (PDF p. 149), with footnote 31, p. 120 (PDF p. 138).
The printed claim is false: the specified half-uniform, quarter-positive and
quarter-negative heavy-tail population has the stated exact survival probabilities,
local affine CDF and unique median zero. Its odd-size median has both normal weak
limits but its scaled bootstrap variance exceeds 5 with probability at least 3/16.
The specified CDF functional T0 is locally affine, Hadamard differentiable in every
bounded sup-norm direction, and, along all positive sizes, has marginal and conditional
bootstrap limits N(0,1/4). Its scaled bootstrap variance still exceeds 5 with probability
at least 3/16 at every odd size at least 5, and cannot converge to 1/4.
The resamples repeating a high and a central observation give exactly those observations. -/
def T61WholeStatement : Prop :=
  IsProbabilityMeasure heavyBootstrapLaw ∧
  WholeCDF (cdf heavyBootstrapLaw id) ∧
  (∀ x : ℝ, 2 ≤ x → prob heavyBootstrapLaw (Set.Ici x) =
    1/(4*Real.sqrt (Real.log x / Real.log 2))) ∧
  (∀ x : ℝ, |x| ≤ 1 → cdf heavyBootstrapLaw id x = 1/2+x/4) ∧
  (cdf heavyBootstrapLaw id 0 = 1/2 ∧
    (∀ x : ℝ, x < 0 → cdf heavyBootstrapLaw id x < 1/2) ∧
    (∀ x : ℝ, 0 < x → 1/2 < cdf heavyBootstrapLaw id x)) ∧
  (∀ j : ℕ, 0 < j → prob heavyBootstrapLaw (Set.Ici ((2 : ℝ)^(j^2))) = 1/(4*j)) ∧
  regularHeavyFunctional (cdf heavyBootstrapLaw id) = 0 ∧
  (∀ G : ℝ → ℝ, (∀ x, |G x-cdf heavyBootstrapLaw id x| < 1/4) →
    regularHeavyFunctional G - regularHeavyFunctional (cdf heavyBootstrapLaw id) =
      G 0-cdf heavyBootstrapLaw id 0) ∧
  WholeHadamardEvaluation regularHeavyFunctional (cdf heavyBootstrapLaw id) ∧
  (∀ {n : ℕ}, 0 < n → ∀ x : Fin n → ℝ,
    WholeCDF (wholeEmpiricalCDF x) ∧
    ({t : ℝ | 1/2 ≤ wholeEmpiricalCDF x t}).Nonempty ∧
    BddBelow {t : ℝ | 1/2 ≤ wholeEmpiricalCDF x t} ∧
    sInf {t : ℝ | 1/2 ≤ wholeEmpiricalCDF x t} = wholeLowerMedian x ∧
    (Odd n → wholeRegularStatistic x = regularHeavyStatistic x)) ∧
  (∀ {n : ℕ}, 0 < n → ∀ c : ℝ, wholeRegularStatistic (fun _ : Fin n => c) = c) ∧
  (∀ {n : ℕ}, 0 < n → ∀ (x : Fin n → ℝ) (i : Fin n),
    wholeRegularStatistic (x ∘ (fun _ : Fin n => i)) = x i ∧
    wholeResampleProb (fun a => a = (fun _ : Fin n => i)) = (1/(n : ℝ))^n) ∧
  (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), IID μ X → μ.map (X 0) = heavyBootstrapLaw →
    T61Statement Ω ∧
    CD μ (fun k ω => Real.sqrt (k+1 : ℕ) * wholeRegularStatistic
      (firstSample X (k+1) ω)) (gaussianReal 0 (1/4)) ∧
    BootstrapWeakCP μ X (fun k => k+1) (fun {n} => @wholeRegularStatistic n)
      (gaussianReal 0 (1/4)) ∧
    (∀ n : ℕ, Odd n → 5 ≤ n → (3/16 : ℝ) ≤ prob μ {ω |
      5 < (n : ℝ)*bootVar wholeRegularStatistic (firstSample X n ω)}) ∧
    ¬ CP μ (fun k ω => (k+1 : ℕ)*bootVar wholeRegularStatistic
      (firstSample X (k+1) ω)) (1/4))

/-- Only the actually observed and resampled statistics must be random variables. -/
def WholeResampleMeasurable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (T : {n : ℕ} → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (n : ℕ) (a : Fin (n+1) → Fin (n+1)),
    Measurable (fun ω => T (firstSample X (n+1) ω ∘ a))

/-- The printed square-tail condition, with its cutoff tending through real numbers. -/
def WholeSquareTails {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (T : {n : ℕ} → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun K : ℝ => Filter.limsup (fun n => prob μ {ω | ε <
      bootstrapTestMean T (firstSample X (n+1) ω)
        (fun z => if K < |z| then z^2 else 0)}) atTop) atTop (nhds 0)

/-- P001-T62, p. 131 (PDF p. 149); Definition 3.2.32, pp. 113–114 (PDF pp. 131–132).
Assume the estimator has the stated root-n normal limit. For the exact finite
with-replacement bootstrap, conditional weak convergence to N(0,phi^2), phi>0,
makes the real-cutoff square-tail condition equivalent to convergence of n times
the bootstrap variance to phi^2. If these equivalent conditions hold, the scaled
bootstrap standard deviation converges to phi. The usual measure-theoretic
conditions are assumed; only the observed and resampled statistics must be
measurable. The finite-variance sample-mean formula and consistency, and the all-size
median case under a positive continuous local density, a unique median and a finite
positive-order absolute moment, hold as well. -/
def T62WholeStatement : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
  (∀ (X : ℕ → Ω → ℝ), IID μ X →
    ∀ T : {n : ℕ} → (Fin n → ℝ) → ℝ, WholeResampleMeasurable X T →
    ∀ (θ φ : ℝ), 0 < φ →
    CD μ (fun n ω => Real.sqrt (n+1 : ℕ)*(T (firstSample X (n+1) ω)-θ))
      (gaussianReal 0 ⟨φ^2, sq_nonneg _⟩) →
    BootstrapWeakCP μ X (fun n => n+1) T (gaussianReal 0 ⟨φ^2, sq_nonneg _⟩) →
    (WholeSquareTails μ X T ↔
      CP μ (fun n ω => (n+1 : ℕ)*bootVar T (firstSample X (n+1) ω)) (φ^2)) ∧
    (CP μ (fun n ω => (n+1 : ℕ)*bootVar T (firstSample X (n+1) ω)) (φ^2) →
      CP μ (fun n ω => Real.sqrt (n+1 : ℕ)*Real.sqrt
        (bootVar T (firstSample X (n+1) ω))) φ)) ∧
  (∀ {n : ℕ}, 0 < n → ∀ x : Fin n → ℝ,
    (n : ℝ)*bootVar finiteSampleMean x = (∑ i, (x i)^2)/(n : ℝ)-(finiteSampleMean x)^2) ∧
  (∀ X : ℕ → Ω → ℝ, IID μ X → MemLp (X 0) 2 μ → 0 < variance (X 0) μ →
    CP μ (fun n ω => (n+1 : ℕ)*bootVar finiteSampleMean (firstSample X (n+1) ω))
      (variance (X 0) μ) ∧
    CP μ (fun n ω => Real.sqrt (n+1 : ℕ)*Real.sqrt
      (bootVar finiteSampleMean (firstSample X (n+1) ω))) (Real.sqrt (variance (X 0) μ))) ∧
  (∀ X : ℕ → Ω → ℝ, IID μ X → ∀ (m : ℝ) (f : ℝ → ℝ) (δ : ℝ), 0 < δ →
    (μ.map (X 0)).restrict (Metric.ball m δ) =
      (volume.restrict (Metric.ball m δ)).withDensity (fun x => ENNReal.ofReal (f x)) →
    (∀ x ∈ Metric.ball m δ, 0 ≤ f x) → AEMeasurable f (volume.restrict (Metric.ball m δ)) →
    ContinuousAt f m → 0 < f m →
    (cdf μ (X 0) m = 1/2 ∧ (∀ x, x < m → cdf μ (X 0) x < 1/2) ∧
      (∀ x, m < x → 1/2 < cdf μ (X 0) x)) →
    ∀ η : ℝ, 0 < η → Integrable (fun ω => |X 0 ω|^η) μ →
    CP μ (fun n ω => (n+1 : ℕ)*bootVar sampleMedian (firstSample X (n+1) ω)) (1/(4*(f m)^2)) ∧
    CP μ (fun n ω => Real.sqrt (n+1 : ℕ)*Real.sqrt
      (bootVar sampleMedian (firstSample X (n+1) ω))) (1/(2*f m)))

end SAP.P001d
