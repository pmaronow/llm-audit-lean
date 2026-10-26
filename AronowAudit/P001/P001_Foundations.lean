import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Tactic
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Independence.Conditional
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.BoundedVariation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace AronowAudit.P001

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-- "P(Ω) = 1" and countable additivity (Definition 1.1.2, p. 7).
All probabilistic theorems below require an actual probability measure. -/
def prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) : ℝ := (μ A).toReal

/-- "E[X] = ∫ x f(x) dx", with absolute convergence (Definition 2.1.1,
p. 45). Integration over the original probability space is equivalent. -/
def mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : ℝ := ∫ ω, X ω ∂μ

/-- "V[X] = E[(X − E[X])²]" (Definition 2.1.12, p. 52).
Finite second moments are explicit whenever the theorem needs them. -/
def var {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : ℝ := ProbabilityTheory.variance X μ

/-- "E[(X − c)²]" (Definition 2.1.22, p. 57). -/
def mse {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (c : ℝ) : ℝ := ∫ ω, (X ω - c)^2 ∂μ

/-- "F(x) = Pr[X ≤ x]" (Definition 1.2.11, p. 21). -/
def cdf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ := prob μ {ω | X ω  ≤  x}

/-- "∀ ε > 0, lim Pr[|Tₙ − c| ≥ ε] = 0" (Definition 3.2.6, p. 99).
Distance allows the same definition for parameter vectors. -/
def CP {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (μ : Measure Ω) (Z : ℕ → Ω → E) (c : E) : Prop :=
  ∀ ε : ℝ, 0  <  ε → Tendsto (fun (n : ℕ) => prob μ {ω | ε  ≤  dist (Z n ω) c}) atTop (nhds 0)

/-- "lim Fₙ(t) = F(t)" at continuity points of F
(Definition 3.2.22, p. 108). -/
def CD {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : ℕ → Ω → ℝ) (ν : Measure ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt (fun t => prob ν (Set.Iic t)) x →
    Tendsto (fun (n : ℕ) => cdf μ (Z n) x) atTop (nhds (prob ν (Set.Iic x)))

/-- "Mutually independent" and "identically distributed"
(Definition 3.1.1, p. 92), for an infinite sequence. -/
def IID {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  (∀ i, Measurable (X i)) ∧ iIndepFun X μ ∧ ∀ i, IdentDistrib (X i) (X 0) μ μ

/-- "X̄ = (1/n) ∑ᵢ Xᵢ" (Definition 3.2.2, p. 97).
The first n observations are indexed 0,...,n−1. -/
def sampleMean {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, X i ω) / (n : ℝ)

/-- "F̂(x) = I(X ≤ x)̄" (Definition 3.3.1, p. 116), represented as
the uniform measure on the n observations, for n > 0. -/
def empirical {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Measure ℝ :=
  (n : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range n, Measure.dirac (X i ω)

/-- "There exists a non-negative function f ... F(x) = ∫₋∞ˣ f(u) du"
(Definition 1.2.14, p. 24). The law equals Lebesgue measure weighted by f;
the probability-measure premise supplies normalization. -/
def HasPDF (ν : Measure ℝ) (f : ℝ → ℝ) : Prop :=
  AEMeasurable f volume ∧ (∀ x, 0  ≤  f x) ∧ Integrable f volume ∧
    ν = volume.withDensity (fun x => ENNReal.ofReal (f x))

/-- "Gᵧ(x) = E[Y|X = x]" (Definition 2.2.15, p. 69).
The defining integral identity over every covariate-measurable event
retains the CEF's equivalence up to null sets. -/
def IsCEF {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (Y : Ω → ℝ) (m : E → ℝ) : Prop :=
  Measurable m ∧ Integrable Y μ ∧ Integrable (m ∘ X) μ ∧ ∀ A : Set E, MeasurableSet A →
    (∫ ω in X ⁻¹' A, Y ω ∂μ) = ∫ ω in X ⁻¹' A, m (X ω) ∂μ

/-- A finite PMF: "f(x) = Pr[X = x]" (Definition 1.2.5, p. 18).
Nonnegativity and total mass one exclude a zero or signed design. -/
structure FiniteLaw (n : ℕ) where
  weight : Fin n → ℝ
  nonneg : ∀ i, 0  ≤  weight i
  total : ∑ i, weight i = 1
/-- Auxiliary representation used for "f(x) = Pr[X = x]" (p. 7, Definition 1.1.2; p. 18, Definition 1.2.5): fmean. -/
def fmean {n : ℕ} (P : FiniteLaw n) (X : Fin n → ℝ) : ℝ := ∑ i, P.weight i * X i
/-- Auxiliary representation used for "f(x) = Pr[X = x]" (p. 7, Definition 1.1.2; p. 18, Definition 1.2.5): fprob. -/
def fprob {n : ℕ} (P : FiniteLaw n) (A : Fin n → Prop) [DecidablePred A] : ℝ :=
  ∑ i, if A i then P.weight i else 0
/-- Auxiliary representation used for "f(x) = Pr[X = x]" (p. 7, Definition 1.1.2; p. 18, Definition 1.2.5): fvar. -/
def fvar {n : ℕ} (P : FiniteLaw n) (X : Fin n → ℝ) : ℝ :=
  fmean P (fun i => (X i - fmean P X)^2)
/-- Auxiliary representation used for "f(x) = Pr[X = x]" (p. 7, Definition 1.1.2; p. 18, Definition 1.2.5): fcov. -/
def fcov {n : ℕ} (P : FiniteLaw n) (X Y : Fin n → ℝ) : ℝ :=
  fmean P (fun i => (X i - fmean P X)*(Y i - fmean P Y))

/-- Counterexample with "qₖ = 2^{−(k+1)}" on k = 0,1,...
(T1; refutes p. 120). -/
def geoMass (k : ℕ) : ℝ := (1/2 : ℝ)^(k+1)
/-- Auxiliary representation used for "qₖ = 2^{−(k+1)}" (T1; p. 120 and P001-C03-E001): massCDF. -/
def massCDF (q : ℕ → ℝ) (x : ℝ) : ℝ := ∑' k : ℕ, if (k : ℝ)  ≤  x then q k else 0
/-- Auxiliary representation used for "qₖ = 2^{−(k+1)}" (T1; p. 120 and P001-C03-E001): mixMass. -/
def mixMass (n k : ℕ) : ℝ :=
  (1 - (n : ℝ)⁻¹^3)*geoMass k + (n : ℝ)⁻¹^3 *
    (if n  ≤  k then geoMass (k-n) else 0)
/-- Auxiliary representation used for "qₖ = 2^{−(k+1)}" (T1; p. 120 and P001-C03-E001): massMean. -/
def massMean (q : ℕ → ℝ) : ℝ := ∑' k : ℕ, (k : ℝ)*q k
/-- Auxiliary representation used for "qₖ = 2^{−(k+1)}" (T1; p. 120 and P001-C03-E001): massSecond. -/
def massSecond (q : ℕ → ℝ) : ℝ := ∑' k : ℕ, (k : ℝ)^2*q k
/-- Auxiliary representation used for "qₖ = 2^{−(k+1)}" (T1; p. 120 and P001-C03-E001): FiniteMomentLaw. -/
def FiniteMomentLaw (q : ℕ → ℝ) : Prop :=
  (∀ k, 0  ≤  q k) ∧ Summable q ∧ (∑' k, q k) = 1 ∧
    Summable (fun k : ℕ => (k : ℝ)*q k) ∧ Summable (fun k : ℕ => (k : ℝ)^2*q k)

/-- "f_X(x) = 1/2 for x ∈ [−2,−1] ∪ [1,2]" and
"m₁(x) = x(1−x²)² for |x| < 1" (T3 counterexample). -/
def gapPDF (x : ℝ) : ℝ := if x ∈ Set.Icc (-2) (-1) ∪ Set.Icc 1 2 then 1/2 else 0
/-- Auxiliary representation used for "f_X(x) = 1/2 for x ∈ [−2,−1] ∪ [1,2]" (T3; pp. 166–168): pdaBump. -/
def pdaBump (x : ℝ) : ℝ := if |x|  <  1 then x*(1-x^2)^2 else 0
/-- Auxiliary representation used for "f_X(x) = 1/2 for x ∈ [−2,−1] ∪ [1,2]" (T3; pp. 166–168): partialAt. -/
def partialAt {K : ℕ} (m : (Fin K → ℝ) → ℝ) (x : Fin K → ℝ) (k : Fin K) : ℝ :=
  deriv (fun t : ℝ => m (Function.update x k (x k + t))) 0

/-- Auxiliary representation used for "∑ₖ₌₀ᴶ β̂ₖ xᵏ" (pp. 168–169, Definition 4.3.9, corrected): IsSieveLS. -/
def IsSieveLS {Ω : Type*} (X Y : ℕ → Ω → ℝ) (J : ℕ → ℕ)
    (fit : ℕ → Ω → Polynomial ℝ) : Prop :=
  ∀ n ω, (fit n ω).natDegree  ≤  J n ∧ ∀ p : Polynomial ℝ, p.natDegree  ≤  J n →
    (∑ i ∈ Finset.range n, (Y i ω - (fit n ω).eval (X i ω))^2)  ≤ 
      ∑ i ∈ Finset.range n, (Y i ω - p.eval (X i ω))^2
/-- Auxiliary representation used for "∑ₖ₌₀ᴶ β̂ₖ xᵏ" (pp. 168–169, Definition 4.3.9, corrected): uniformLaw. -/
def uniformLaw (a b : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (if x ∈ Set.Icc a b then (b-a)⁻¹ else 0))

/-- "KL(p(·) ∥ q(·)) = ∫ p(t) log(p(t)/q(t)) dt"
(Definition 5.2.7, p. 195); here the integral is the two-point PMF sum. -/
def bernoulliKL (p t : ℝ) : ℝ := p*Real.log (p/t)+(1-p)*Real.log ((1-p)/(1-t))
/-- Auxiliary representation used for "KL(p(·) ∥ q(·)) = ∫ p(t) log(p(t)/q(t)) dt" (p. 195, Definition 5.2.7; T7 witness): clip. -/
def clip (a b x : ℝ) : ℝ := max a (min b x)
/-- Auxiliary representation used for "KL(p(·) ∥ q(·)) = ∫ p(t) log(p(t)/q(t)) dt" (p. 195, Definition 5.2.7; T7 witness): binaryJoint. -/
def binaryJoint : FiniteLaw 4 where
  weight := ![3/8, 1/8, 1/8, 3/8]
  nonneg := by intro i; fin_cases i <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- "g = p_N g_N + p_LN g_LN + (1−p_N−p_LN) g_E"
(Example 5.2.11, pp. 199–200). The normal component is on ℝ;
the log-normal and exponential components vanish outside their supports. -/
def normalDensity (m s y : ℝ) : ℝ :=
  Real.exp (-(y-m)^2/(2*s^2))/(s*Real.sqrt (2*Real.pi))
/-- Auxiliary representation used for "g = p_N g_N + p_LN g_LN + (1−p_N−p_LN) g_E" (pp. 199–200, Example 5.2.11): lognormalDensity. -/
def lognormalDensity (m s y : ℝ) : ℝ :=
  if 0  <  y then normalDensity m s (Real.log y)/y else 0
/-- Auxiliary representation used for "g = p_N g_N + p_LN g_LN + (1−p_N−p_LN) g_E" (pp. 199–200, Example 5.2.11): exponentialDensity. -/
def exponentialDensity (r y : ℝ) : ℝ :=
  if 0  ≤  y then r*Real.exp (-r*y) else 0
/-- Auxiliary representation used for "g = p_N g_N + p_LN g_LN + (1−p_N−p_LN) g_E" (pp. 199–200, Example 5.2.11): mixtureDensity. -/
def mixtureDensity (θ : Fin 7 → ℝ) (y : ℝ) : ℝ :=
  θ 0*normalDensity (θ 2) (θ 3) y + θ 1*lognormalDensity (θ 4) (θ 5) y +
    (1-θ 0-θ 1)*exponentialDensity (θ 6) y
/-- Auxiliary representation used for "g = p_N g_N + p_LN g_LN + (1−p_N−p_LN) g_E" (pp. 199–200, Example 5.2.11): MixtureAdmissible. -/
def MixtureAdmissible (θ : Fin 7 → ℝ) : Prop :=
  0  ≤  θ 0 ∧ 0  ≤  θ 1 ∧ θ 0+θ 1  ≤  1 ∧ 0  <  θ 3 ∧ 0  <  θ 5 ∧ 0  <  θ 6
/-- Auxiliary representation used for "g = p_N g_N + p_LN g_LN + (1−p_N−p_LN) g_E" (pp. 199–200, Example 5.2.11): mixtureLikelihood. -/
def mixtureLikelihood {n : ℕ} (y : Fin n → ℝ) (θ : Fin 7 → ℝ) : ℝ := ∏ i, mixtureDensity θ (y i)
/-- Auxiliary representation used for "g = p_N g_N + p_LN g_LN + (1−p_N−p_LN) g_E" (pp. 199–200, Example 5.2.11): mixtureRestriction. -/
def mixtureRestriction (B S δ a b : ℝ) : Set (Fin 7 → ℝ) :=
  {θ | MixtureAdmissible θ ∧ |θ 2|  ≤  B ∧ |θ 4|  ≤  B ∧
    δ  ≤  θ 3 ∧ θ 3  ≤  S ∧ δ  ≤  θ 5 ∧ θ 5  ≤  S ∧ a  ≤  θ 6 ∧ θ 6  ≤  b}

/-- Two-component PMF: "(p(1−a), pa, (1−p)(1−b), (1−p)b)"
on outcomes 0,1,2,3 (T11; refutes p. 199). -/
def disjointMixture (p a b : ℝ) : Fin 4 → ℝ := ![p*(1-a),p*a,(1-p)*(1-b),(1-p)*b]

/-- "Impute ... the unit with ... nearest [propensity score]"
(Section 6.2.3, pp. 224–225; Section 7.2.4, pp. 262–264).
Ties use a fixed classical choice; the continuous designs have ties only on null sets. -/
def nearestDonor {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool) (i : Fin n) : Option (Fin n) :=
  if h : ∃ j, r j = true ∧ ∀ k, r k = true → |p j-p i|  ≤  |p k-p i|
    then some (Classical.choose h) else none
/-- Auxiliary representation used for "Impute ... the unit with ... nearest [propensity score]" (pp. 224–225 and 262–264; T13–T16): noise. -/
def noise (b : Bool) : ℝ := if b then 1 else -1
/-- Auxiliary representation used for "Impute ... the unit with ... nearest [propensity score]" (pp. 224–225 and 262–264; T13–T16): hotDeck. -/
def hotDeck {n : ℕ} (s : Fin n → ℝ × Bool × Bool) : ℝ :=
  if ∃ j, (s j).2.1 = true then
    (∑ i, if (s i).2.1 then 50+noise (s i).2.2 else
      match nearestDonor (fun j => (s j).1) (fun j => (s j).2.1) i with
      | some j => 50+noise (s j).2.2
      | none => 50) / (n : ℝ)
  else 50
/-- Auxiliary representation used for "Impute ... the unit with ... nearest [propensity score]" (pp. 224–225 and 262–264; T13–T16): causalMatch. -/
def causalMatch {n : ℕ} (s : Fin n → ℝ × Bool × Bool) : ℝ :=
  -(∑ i, if (s i).2.1 then
      match nearestDonor (fun j => (s j).1) (fun j => !(s j).2.1) i with
      | some j => noise (s j).2.2
      | none => 0
    else noise (s i).2.2) / (n : ℝ)
/-- Auxiliary representation used for "Impute ... the unit with ... nearest [propensity score]" (pp. 224–225 and 262–264; T13–T16): resample. -/
def resample {n : ℕ} {E : Type*} (s : Fin n → E) (a : Fin n → Fin n) : Fin n → E := s ∘ a
/-- Auxiliary representation used for "Impute ... the unit with ... nearest [propensity score]" (pp. 224–225 and 262–264; T13–T16): bootMean. -/
def bootMean {n : ℕ} {E : Type*} (T : (Fin n → E) → ℝ) (s : Fin n → E) : ℝ :=
  (∑ a : Fin n → Fin n, T (resample s a)) / ((n : ℝ)^n)
/-- Auxiliary representation used for "Impute ... the unit with ... nearest [propensity score]" (pp. 224–225 and 262–264; T13–T16): bootVar. -/
def bootVar {n : ℕ} {E : Type*} (T : (Fin n → E) → ℝ) (s : Fin n → E) : ℝ :=
  (∑ a : Fin n → Fin n, (T (resample s a) - bootMean T s)^2) / ((n : ℝ)^n)
/-- Auxiliary representation used for "Impute ... the unit with ... nearest [propensity score]" (pp. 224–225 and 262–264; T13–T16): matchingUnitLaw. -/
def matchingUnitLaw : Measure (ℝ × Bool × Bool) :=
  (volume.prod (Measure.count.prod Measure.count)).withDensity
    (fun u => ENNReal.ofReal (if u.1 ∈ Set.Icc (1/4 : ℝ) (3/4)
      then (if u.2.1 then u.1 else 1-u.1) else 0))
/-- Auxiliary representation used for "Impute ... the unit with ... nearest [propensity score]" (pp. 224–225 and 262–264; T13–T16): matchV. -/
def matchV : ℝ := 3*Real.log 3-1/4
/-- "s=1−e⁻¹" (T13–T16 bootstrap occupancy constants). -/
def matchS : ℝ := 1-Real.exp (-1)
/-- "A=2/s−s/(2−s)" (T13–T16 occupancy constant). -/
def matchA : ℝ := 2/matchS-matchS/(2-matchS)
/-- "B=3/(2s)−(4−s)/(2(2−s))" (T13–T16 constant). -/
def matchB : ℝ := 3/(2*matchS)-(4-matchS)/(2*(2-matchS))
/-- Auxiliary representation used for "Impute ... the unit with ... nearest [propensity score]" (pp. 224–225 and 262–264; T13–T16): matchVB. -/
def matchVB : ℝ := 1/2+matchA/2+matchB*(2*Real.log 3-3/2)
/-- Auxiliary representation used for "Impute ... the unit with ... nearest [propensity score]" (pp. 224–225 and 262–264; T13–T16): firstSample. -/
def firstSample {Ω E : Type*} (Z : ℕ → Ω → E) (n : ℕ) (ω : Ω) : Fin n → E :=
  fun i => Z i ω
/-- Auxiliary representation used for "Impute ... the unit with ... nearest [propensity score]" (pp. 224–225 and 262–264; T13–T16): MatchingFailure. -/
def MatchingFailure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : ℕ → Ω → ℝ × Bool × Bool) (causal : Bool) : Prop :=
  let T : ∀ n : ℕ, (Fin n → ℝ × Bool × Bool) → ℝ :=
    if causal then fun _ => causalMatch else fun _ => hotDeck
  let θ : ℝ := if causal then 0 else 50
  (∀ n, 0  <  n → mean μ (fun ω => T n (firstSample Z n ω)) = θ) ∧
  Tendsto (fun (n : ℕ) => (n : ℝ)*var μ (fun ω => T n (firstSample Z n ω))) atTop (nhds matchV) ∧
  Tendsto (fun (n : ℕ) => mean μ (fun ω => (n : ℝ)*bootVar (T n) (firstSample Z n ω))) atTop (nhds matchVB) ∧
  0  <  matchVB ∧ matchVB  <  matchV ∧
  ¬ CP μ (fun n ω => (n : ℝ)*bootVar (T n) (firstSample Z n ω)) matchV

/-- "P(B|A) = P(B ∩ A)/P(A)" when P(A)>0 (Definition 1.1.8,
p. 10). Conditional independence uses cross multiplication on positive cells. -/
def fcond {n : ℕ} (P : FiniteLaw n) (Y X : Fin n → ℝ) (x : ℝ) : ℝ :=
  (∑ i, if X i=x then P.weight i*Y i else 0) / fprob P (fun i => X i=x)
/-- Auxiliary representation used for "P(B|A) = P(B ∩ A)/P(A)" (p. 10, Definition 1.1.8; p. 215, footnote 6): FCondIndep. -/
def FCondIndep {n : ℕ} {E F G : Type*} (P : FiniteLaw n)
    (Y : Fin n → E) (Z : Fin n → F) (X : Fin n → G) : Prop :=
  ∀ (x : G) (y : E) (z : F), 0  <  fprob P (fun i => X i=x) →
    fprob P (fun i => X i=x ∧ Y i=y ∧ Z i=z) * fprob P (fun i => X i=x) =
    fprob P (fun i => X i=x ∧ Y i=y)*fprob P (fun i => X i=x ∧ Z i=z)
/-- Auxiliary representation used for "P(B|A) = P(B ∩ A)/P(A)" (p. 10, Definition 1.1.8; p. 215, footnote 6): placeboLaw. -/
def placeboLaw : FiniteLaw 12 where
  weight i := if i.val/4=1 then (if i.val%2=1 then 1/24 else 1/8)
    else (if i.val%2=1 then 1/8 else 1/24)
  nonneg := by intro i; split_ifs <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]
/-- Auxiliary representation used for "P(B|A) = P(B ∩ A)/P(A)" (p. 10, Definition 1.1.8; p. 215, footnote 6): placeboX. -/
def placeboX (i : Fin 12) : ℝ := if i.val/4=0 then -1 else if i.val/4=1 then 0 else 1
/-- Auxiliary representation used for "P(B|A) = P(B ∩ A)/P(A)" (p. 10, Definition 1.1.8; p. 215, footnote 6): placeboZ. -/
def placeboZ (i : Fin 12) : ℝ := if i.val%4 < 2 then -1 else 1
/-- Auxiliary representation used for "P(B|A) = P(B ∩ A)/P(A)" (p. 10, Definition 1.1.8; p. 215, footnote 6): placeboD. -/
def placeboD (i : Fin 12) : ℝ := if i.val%2=1 then 1 else 0
/-- Auxiliary representation used for "P(B|A) = P(B ∩ A)/P(A)" (p. 10, Definition 1.1.8; p. 215, footnote 6): placeboW. -/
def placeboW (i : Fin 12) : ℝ := (placeboX i)^2 + placeboZ i/2

/-- "f_(Y,Z)|X = f_Y|X f_Z|X" (footnote 6, p. 215), generalized
to conditional-expectation factorization of every pair of measurable events.
This definition works on arbitrary probability spaces without assuming a
standard Borel sample space. -/
def CI {Ω E F G : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace G] (μ : Measure Ω)
    (X : Ω → E) (hX : Measurable X) (Y : Ω → F) (Z : Ω → G) : Prop :=
  ∀ (A : Set F) (B : Set G), MeasurableSet A → MeasurableSet B →
    (μ[(fun ω => if Y ω∈A ∧ Z ω∈B then (1 : ℝ) else 0) | MeasurableSpace.comap X inferInstance]) =ᵐ[μ]
    (fun ω => (μ[(fun ω => if Y ω∈A then (1 : ℝ) else 0) | MeasurableSpace.comap X inferInstance]) ω *
      (μ[(fun ω => if Z ω∈B then (1 : ℝ) else 0) | MeasurableSpace.comap X inferInstance]) ω)

/-- "g(X)=b₀+b₁X_[1]+b₂X_[2]+...+b_K X_[K]"
(Definition 2.3.6, p. 86). The BLP minimizes MSE over these predictors;
this definition represents every such predictor, with its intercept. -/
def linearPredictor {K : ℕ} (b : Fin (K+1) → ℝ) (x : Fin K → ℝ) : ℝ :=
  b 0 + ∑ k, b k.succ * x k

/-- "Pr[X=k,D=1]=3^{−k}, Pr[X=k,D=0]=2^{−(k+1)}" for k≥1
(T19; refutes uniform-positivity converse on p. 271). -/
def overlapT (k : ℕ) : ℝ := (1/3 : ℝ)^(k+1)
/-- Auxiliary representation used for "Pr[X=k,D=1]=3^{−k}, Pr[X=k,D=0]=2^{−(k+1)}" (T19; pp. 271–272): overlapC. -/
def overlapC (k : ℕ) : ℝ := (1/2 : ℝ)^(k+2)
/-- Auxiliary representation used for "Pr[X=k,D=1]=3^{−k}, Pr[X=k,D=0]=2^{−(k+1)}" (T19; pp. 271–272): overlapPropensity. -/
def overlapPropensity (k : ℕ) : ℝ := overlapT k/(overlapT k+overlapC k)

/-- "Y(d)=20+40U+5d" with X=0 and the four masses 3/8,1/8,1/8,3/8
(T21). Each electorate has 100 voters and only displayed gender
and voters' preferences enter its rule. -/
def electorateU : Fin 4 → ℝ := ![0,0,1,1]
/-- Auxiliary representation used for "Y(d)=20+40U+5d" (T21; p. 278): electorateD. -/
def electorateD : Fin 4 → ℝ := ![0,1,0,1]
/-- Auxiliary representation used for "Y(d)=20+40U+5d" (T21; p. 278): electorateOutcome. -/
def electorateOutcome (d : ℝ) (i : Fin 4) : ℝ := 20+40*electorateU i+5*d

/-- "X(ω₀)=0" on a one-atom probability space (T25). -/
def zeroAtom : FiniteLaw 1 where
  weight _ := 1
  nonneg _ := by norm_num
  total := by norm_num [Fin.sum_univ_succ]
/-- Auxiliary representation used for "X(ω₀)=0" (T25; p. 20): intMassCDF. -/
def intMassCDF (q : ℤ → ℝ) (x : ℝ) : ℝ := ∑' k : ℤ, if (k : ℝ)  ≤  x then q k else 0

/-- "X(m,k)=(2k+1)/2^{m+1}, P{(m,k)}=2^{−(2m+1)}"
on m≥0 and k<2^m (T27). -/
def dyadicValue (i : Σ m : ℕ, Fin (2^m)) : ℝ := (2*(i.2 : ℝ)+1)/(2 : ℝ)^(i.1+1)
/-- Auxiliary representation used for "X(m,k)=(2k+1)/2^{m+1}, P{(m,k)}=2^{−(2m+1)}" (T27; p. 23): dyadicMass. -/
def dyadicMass (i : Σ m : ℕ, Fin (2^m)) : ℝ := (1/2 : ℝ)^(2*i.1+1)
/-- Auxiliary representation used for "X(m,k)=(2k+1)/2^{m+1}, P{(m,k)}=2^{−(2m+1)}" (T27; p. 23): dyadicCDF. -/
def dyadicCDF (x : ℝ) : ℝ := ∑' i, if dyadicValue i  ≤  x then dyadicMass i else 0

/-- "F(x)=0 for x<0; x for 0≤x≤1; 1 for x>1"
(Example 1.2.18, p. 28). -/
def uniformCDF (x : ℝ) : ℝ := max 0 (min 1 x)
/-- Auxiliary representation used for "F(x)=0 for x<0; x for 0≤x≤1; 1 for x>1" (pp. 24–25, 28; T29): uniformClosedPDF. -/
def uniformClosedPDF (x : ℝ) : ℝ := if x ∈ Set.Icc 0 1 then 1 else 0
/-- Auxiliary representation used for "F(x)=0 for x<0; x for 0≤x≤1; 1 for x>1" (pp. 24–25, 28; T29): uniformOpenPDF. -/
def uniformOpenPDF (x : ℝ) : ℝ := if x ∈ Set.Ioo 0 1 then 1 else 0
/-- Auxiliary representation used for "F(x)=0 for x<0; x for 0≤x≤1; 1 for x>1" (pp. 24–25, 28; T29): uniformModifiedPDF. -/
def uniformModifiedPDF (x : ℝ) : ℝ := if x=1/3 then 3/2 else uniformClosedPDF x

/-- "F(x,y)=∫₋∞ˣ∫₋∞ʸ f(u,v) dv du" (Definition 1.3.10,
p. 36), represented by a law absolutely continuous with respect to product volume. -/
def HasJointPDF (ν : Measure (ℝ × ℝ)) (f : (ℝ × ℝ) → ℝ) : Prop :=
  AEMeasurable f volume ∧ (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
    ν=volume.withDensity (fun x => ENNReal.ofReal (f x))

/-- "f(x,y)=1 on (0,1)×(−1,0) and 0 otherwise"
(T34). -/
def rectanglePDF (z : ℝ × ℝ) : ℝ := if z.1∈Set.Ioo 0 1 ∧ z.2∈Set.Ioo (-1) 0 then 1 else 0

/-- "(1/π)(eˣ/(1+eˣ))²/(1+y²e^{2x})" (T36). -/
def smoothSlicePDF (z : ℝ × ℝ) : ℝ :=
  (Real.exp z.1/(1+Real.exp z.1))^2/(Real.pi*(1+z.2^2*Real.exp (2*z.1)))

/-- "E[(X−c)²] = (1/2)(0−c)²+(1/2)(1−c)²"
(Example 2.1.25, p. 58). -/
def coinLoss (c : ℝ) : ℝ := (0-c)^2/2+(1-c)^2/2

/-- "P{u}=P{v}=1/2, P{n}=0" (T41).
The null point remains in the sample space, as pointwise equality requires. -/
def nullPointLaw : FiniteLaw 3 where
  weight := ![1/2,1/2,0]
  nonneg := by intro i; fin_cases i <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]
/-- Auxiliary representation used for "P{u}=P{v}=1/2, P{n}=0" (T41; pp. 62–63): correlation. -/
def correlation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  covariance X Y μ / (Real.sqrt (var μ X)*Real.sqrt (var μ Y))

/-- "Q(a,b)=E[(Y−a−bX)²]" (corrected proof of Theorem 2.2.21,
p. 77). The free arguments are a,b, not the optimizing α,β. -/
def linearRisk {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) (a b : ℝ) : ℝ :=
  mean μ (fun ω => (Y ω-a-b*X ω)^2)
/-- Auxiliary representation used for "Q(a,b)=E[(Y−a−bX)²]" (pp. 76–78, Theorem 2.2.21 and corrected proof): blpSlope. -/
def blpSlope {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ := covariance X Y μ/var μ X
/-- Auxiliary representation used for "Q(a,b)=E[(Y−a−bX)²]" (pp. 76–78, Theorem 2.2.21 and corrected proof): blpIntercept. -/
def blpIntercept {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ := mean μ Y-blpSlope μ X Y*mean μ X

/-- "X=Y takes values −1 and 1 with probability 1/2 each"
(T44). -/
def signLaw : FiniteLaw 2 where
  weight _ := 1/2
  nonneg _ := by norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- "Pr[X=2ᵏ]=7/8^{k+1}" (T53). -/
def heavyMomentMass (k : ℕ) : ℝ := 7*(1/8 : ℝ)^(k+1)

/-- "V̂[X]=X²̄−X̄²" (Definition 3.2.18, p. 106). -/
def sampleVariance {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sampleMean (fun i ω => (X i ω)^2) n ω-(sampleMean X n ω)^2

/-- "n V̂[θ̂] →p V[T]" and "√n √V̂[θ̂] →p √V[T]"
(Definition 3.2.32, pp. 113–114, hats restored by T55). -/
def VarianceConsistent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (vhat : ℕ → Ω → ℝ) (v : ℝ) : Prop :=
  CP μ (fun n ω => (n : ℝ)*vhat n ω) v
/-- Auxiliary representation used for "n V̂[θ̂] →p V[T]" (pp. 113–114, Definition 3.2.32, corrected): SEConsistent. -/
def SEConsistent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (vhat : ℕ → Ω → ℝ) (v : ℝ) : Prop :=
  CP μ (fun n ω => Real.sqrt n*Real.sqrt (vhat n ω)) (Real.sqrt v)

/-- "f̂_K(x)=(1/n)∑ᵢ (1/h)K((x−Xᵢ)/h)" and
"F̂_K(x)=∫₋∞ˣ f̂_K(u)du" (Definitions 3.3.7, 3.3.9, pp. 121,123). -/
def kernelDensity {n : ℕ} (K : ℝ → ℝ) (h : ℝ) (X : Fin n → ℝ) (x : ℝ) : ℝ :=
  (∑ i, K ((x-X i)/h)/h)/(n : ℝ)
/-- Auxiliary representation used for "f̂_K(x)=(1/n)∑ᵢ (1/h)K((x−Xᵢ)/h)" (pp. 121–123, Definitions 3.3.7 and 3.3.9): kernelCDF. -/
def kernelCDF {n : ℕ} (K : ℝ → ℝ) (h : ℝ) (X : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∫ u in Set.Iic x, kernelDensity K h X u
/-- Auxiliary representation used for "f̂_K(x)=(1/n)∑ᵢ (1/h)K((x−Xᵢ)/h)" (pp. 121–123, Definitions 3.3.7 and 3.3.9): signedKernel. -/
def signedKernel (t : ℝ) : ℝ := if |t| ≤ 1 then 1 else if |t| ≤ 2 then -1/2 else 0
/-- Auxiliary representation used for "f̂_K(x)=(1/n)∑ᵢ (1/h)K((x−Xᵢ)/h)" (pp. 121–123, Definitions 3.3.7 and 3.3.9): rectangleKernel. -/
def rectangleKernel (t : ℝ) : ℝ := if |t| ≤ 1 then 1/2 else 0

/-- "Hadamard differentiable ... with respect to the Kolmogorov distance"
(footnote 31, p. 120). This sequential definition states the topology,
domain and tangent space explicitly; for CDFs the ambient norm is sup norm. -/
def HadamardAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D H : Set E) (T : E → ℝ) (F : E) (L : E →L[ℝ] ℝ) : Prop :=
  ∀ h ∈ H, ∀ t : ℕ → ℝ, ∀ hn : ℕ → E,
    (∀ n, 0 < t n) → Tendsto t atTop (nhds 0) → Tendsto hn atTop (nhds h) →
    (∀ n, F+t n • hn n ∈ D) →
    Tendsto (fun (n : ℕ) => (T (F+t n • hn n)-T F)/t n) atTop (nhds (L h))
/-- Auxiliary representation used for "Hadamard differentiable ... with respect to the Kolmogorov distance" (p. 120, footnote 31; corrections T2 and T57): WeakLimit. -/
def WeakLimit {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure Ω) (Z : ℕ → Ω → E) (ν : Measure E) : Prop :=
  ∀ f : E → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Tendsto (fun (n : ℕ) => mean μ (fun ω => f (Z n ω))) atTop (nhds (mean ν f))

/-- "Wᵢ=(1/m)∑ⱼ Xᵢⱼ" (Definition 3.5.2, p. 136). -/
def clusterAverage {Ω : Type*} {m : ℕ} (X : ℕ → Ω → Fin m → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  (∑ j,X i ω j)/(m : ℝ)
/-- Auxiliary representation used for "Wᵢ=(1/m)∑ⱼ Xᵢⱼ" (p. 136, Definitions 3.5.1–3.5.2): clusterMean. -/
def clusterMean {Ω : Type*} {m : ℕ} (X : ℕ → Ω → Fin m → ℝ) (l : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range l, ∑ j,X i ω j)/((l : ℝ)*(m : ℝ))

/-- "Take a with replacement sample of l clusters ... keeping clusters intact"
(p. 141, corrected). A resample has l*m observations. -/
def blockResample {l m : ℕ} {E : Type*} (X : Fin l → Fin m → E) (draw : Fin l → Fin l) : Fin l → Fin m → E :=
  fun i j => X (draw i) j

/-- "arg min ∑ᵢ (Yᵢ−Xᵢb)²" with n×(K+1) regressor matrix
(Definition 4.1.2, pp. 146–147; Theorem 4.1.4, p. 148). -/
def olsRSS {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ) (b : Fin (K+1) → ℝ) : ℝ :=
  ∑ i,(Y i-(X.mulVec b) i)^2
/-- Auxiliary representation used for "arg min ∑ᵢ (Yᵢ−Xᵢb)²" (pp. 146–149, Definitions 4.1.2–4.1.3 and Theorem 4.1.4): olsCoef. -/
def olsCoef {n K : ℕ} (X : Matrix (Fin n) (Fin K) ℝ) (Y : Fin n → ℝ) : Fin K → ℝ :=
  (X.transpose*X)⁻¹.mulVec (X.transpose.mulVec Y)

/-- "(XᵀX)⁻¹ Xᵀ diag(eᵢ²) X (XᵀX)⁻¹"
(robust covariance estimator, p. 153). The k-th coefficient is stored at
zero-based k, corresponding to the printed (k+1)-th diagonal. -/
def robustCov {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (e : Fin n → ℝ) : Matrix (Fin (K+1)) (Fin (K+1)) ℝ :=
  (X.transpose*X)⁻¹*(X.transpose*Matrix.diagonal (fun i => (e i)^2)*X)*(X.transpose*X)⁻¹
/-- Auxiliary representation used for "(XᵀX)⁻¹ Xᵀ diag(eᵢ²) X (XᵀX)⁻¹" (pp. 153–155, Definitions 4.2.4–4.2.5; T66): classicalCov. -/
def classicalCov {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (s2 : ℝ) : Matrix (Fin (K+1)) (Fin (K+1)) ℝ :=
  s2 • (X.transpose*X)⁻¹
/-- Auxiliary representation used for "(XᵀX)⁻¹ Xᵀ diag(eᵢ²) X (XᵀX)⁻¹" (pp. 153–155, Definitions 4.2.4–4.2.5; T66): coefficientSE. -/
def coefficientSE {K : ℕ} (V : Matrix (Fin (K+1)) (Fin (K+1)) ℝ) (k : Fin (K+1)) : ℝ :=
  Real.sqrt (V k k)

/-- "m(x₁,x₂)=−x₁ if x₂≤.8 and 9x₁ if x₂>.8"
(Example 4.3.8, p. 167). -/
def apdExample (x y : ℝ) : ℝ := if y ≤ 4/5 then -x else 9*x

/-- "b∈R^{K+1}, (1/n)∑(Yᵢ−Xᵢb)²+λ∑_{k=1}^K |bₖ|"
(Definition 4.3.10, p. 170, corrected). The intercept b₀ is unpenalized. -/
def slopePenalty {K : ℕ} (b : Fin (K+1) → ℝ) : ℝ := ∑ k : Fin K, |b k.succ|
/-- Auxiliary representation used for "b∈R^{K+1}, (1/n)∑(Yᵢ−Xᵢb)²+λ∑_{k=1}^K |bₖ|" (p. 170, Definition 4.3.10, corrected T71): lassoCriterion. -/
def lassoCriterion {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ)
    (lam : ℝ) (b : Fin (K+1) → ℝ) : ℝ := olsRSS X Y b/(n : ℝ)+lam*slopePenalty b

/-- "(X,Y)=(0,1),(0,3),(1,0),(1,6), each with probability 1/4"
(T73). The linear CEF is 2+X. -/
def heteroskedasticLaw : FiniteLaw 4 where
  weight _ := 1/4
  nonneg _ := by norm_num
  total := by norm_num [Fin.sum_univ_succ]
/-- Auxiliary representation used for "(X,Y)=(0,1),(0,3),(1,0),(1,6), each with probability 1/4" (T73; p. 181): heteroX. -/
def heteroX : Fin 4 → ℝ := ![0,0,1,1]
/-- Auxiliary representation used for "(X,Y)=(0,1),(0,3),(1,0),(1,6), each with probability 1/4" (T73; p. 181): heteroY. -/
def heteroY : Fin 4 → ℝ := ![1,3,0,6]
/-- Auxiliary representation used for "(X,Y)=(0,1),(0,3),(1,0),(1,6), each with probability 1/4" (T73; p. 181): heteroResidual. -/
def heteroResidual (i : Fin 4) : ℝ := heteroY i-(2+heteroX i)

/-- "−n log s − (n/2) log(2π) − Q(b)/(2s²)"
(Example 5.2.4, pp. 190–191), with b∈R^{K+1}, s>0. -/
def normalLogLikelihood {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ)
    (b : Fin (K+1) → ℝ) (s : ℝ) : ℝ :=
  -(n : ℝ)*Real.log s-(n : ℝ)/2*Real.log (2*Real.pi)-olsRSS X Y b/(2*s^2)

/-- "F̂_ML(y,x)=(1/n)∑ᵢ I(Xᵢ≤x) F_g(y|Xᵢ;θ̂)"
(Definition 5.2.10, pp. 197–198, corrected indices).
Each νᵢ is the fitted conditional outcome law, covering PMFs and PDFs. -/
def mlFittedLaw {n K : ℕ} (X : Fin n → Fin K → ℝ) (ν : Fin n → Measure ℝ) : Measure (ℝ × (Fin K → ℝ)) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i,(ν i).prod (Measure.dirac (X i))

/-- "Y* = YR + (−99)(1−R)" (Definition 6.1.1, pp. 208–209). -/
def censored (y r : ℝ) : ℝ := y*r+(-99)*(1-r)
/-- Auxiliary representation used for "Y* = YR + (−99)(1−R)" (pp. 208–210, Definition 6.1.1; T80, T87): missingEndpoint. -/
def missingEndpoint (ystar r c : ℝ) : ℝ := ystar*r+c*(1-r)
/-- Auxiliary representation used for "Y* = YR + (−99)(1−R)" (pp. 208–210, Definition 6.1.1; T80, T87): observedOutcome. -/
def observedOutcome (y0 y1 d : ℝ) : ℝ := y1*d+y0*(1-d)
/-- Auxiliary representation used for "Y* = YR + (−99)(1−R)" (pp. 208–210, Definition 6.1.1; T80, T87): ateLower. -/
def ateLower (y d a b : ℝ) : ℝ := y*d+a*(1-d)-y*(1-d)-b*d
/-- Auxiliary representation used for "Y* = YR + (−99)(1−R)" (pp. 208–210, Definition 6.1.1; T80, T87): ateUpper. -/
def ateUpper (y d a b : ℝ) : ℝ := y*d+b*(1-d)-y*(1-d)-a*d

/-- "Six points ... probability 1/6 each" (Example 7.1.17, p. 253).
The observable (Y,X,D)=(1,1,1) occurs at two latent points. -/
def postTreatmentLaw : FiniteLaw 6 where
  weight _ := 1/6
  nonneg _ := by norm_num
  total := by norm_num [Fin.sum_univ_succ]
/-- Auxiliary representation used for "Six points ... probability 1/6 each" (pp. 253–254, Example 7.1.17; T89): postY. -/
def postY : Fin 6 → ℝ := ![0,1,1,0,1,1]
/-- Auxiliary representation used for "Six points ... probability 1/6 each" (pp. 253–254, Example 7.1.17; T89): postX. -/
def postX : Fin 6 → ℝ := ![0,0,1,0,1,1]
/-- Auxiliary representation used for "Six points ... probability 1/6 each" (pp. 253–254, Example 7.1.17; T89): postD. -/
def postD : Fin 6 → ℝ := ![0,0,0,1,1,1]
/-- Auxiliary representation used for "Six points ... probability 1/6 each" (pp. 253–254, Example 7.1.17; T89): fcond2. -/
def fcond2 {n : ℕ} (P : FiniteLaw n) (Y X D : Fin n → ℝ) (x d : ℝ) : ℝ :=
  (∑ i,if X i=x ∧ D i=d then P.weight i*Y i else 0)/fprob P (fun i => X i=x ∧ D i=d)

/-- "Y_A(d)=0, Y_B(d)=I{d=1/2}" with D uniform [0,1]
(T90). Both potential-outcome processes are deterministic. -/
def doseSpike (d : ℝ) : ℝ := if d=1/2 then 1 else 0

/-- "(13563,6178,−759,−1778)/2437" fitted to the six units with
X_[1]3=10 (T92; Example 7.2.2, p. 259). -/
def causalExampleBeta : Fin 4 → ℝ := ![13563/2437,6178/2437,-759/2437,-1778/2437]
/-- Auxiliary representation used for "(13563,6178,−759,−1778)/2437" (T92–T93; p. 259, Example 7.2.2): causalExampleY. -/
def causalExampleY : Fin 6 → ℝ := ![2,5,3,10,2,0]
/-- Auxiliary representation used for "(13563,6178,−759,−1778)/2437" (T92–T93; p. 259, Example 7.2.2): causalExampleD. -/
def causalExampleD : Fin 6 → ℝ := ![1,0,1,1,1,0]
/-- Auxiliary representation used for "(13563,6178,−759,−1778)/2437" (T92–T93; p. 259, Example 7.2.2): causalExampleX1. -/
def causalExampleX1 : Fin 6 → ℝ := ![1,8,10,3,5,7]
/-- Auxiliary representation used for "(13563,6178,−759,−1778)/2437" (T92–T93; p. 259, Example 7.2.2): causalExampleX2. -/
def causalExampleX2 : Fin 6 → ℝ := ![7,2,3,1,2,0]
/-- Auxiliary representation used for "(13563,6178,−759,−1778)/2437" (T92–T93; p. 259, Example 7.2.2): causalPrediction. -/
def causalPrediction (x1 x2 d : ℝ) : ℝ := causalExampleBeta 0+causalExampleBeta 1*d+
  causalExampleBeta 2*x1+causalExampleBeta 3*x2
/-- Auxiliary representation used for "(13563,6178,−759,−1778)/2437" (T92–T93; p. 259, Example 7.2.2): causalPartialImpute. -/
def causalPartialImpute (x1 : Fin 6 → ℝ) : ℝ :=
  (∑ i,if causalExampleD i=1 then causalExampleY i-causalPrediction (x1 i) (causalExampleX2 i) 0
    else causalPrediction (x1 i) (causalExampleX2 i) 1-causalExampleY i)/6

/-- "(1/n)∑ᵢ ∫ y g(y,(d,Xᵢ),θ̂)dy" (p. 261, corrected T94). -/
def modelConditionalMean {K τ : ℕ} (g : ℝ → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (d : ℝ) (x : Fin K → ℝ) (θ : Fin τ → ℝ) : ℝ := ∫ y,y*g y d x θ
/-- Auxiliary representation used for "(1/n)∑ᵢ ∫ y g(y,(d,Xᵢ),θ̂)dy" (p. 261, Section 7.2.3; T94): mlPotentialMean. -/
def mlPotentialMean {n K τ : ℕ} (g : ℝ → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (d : ℝ) (X : Fin n → Fin K → ℝ) (θ : Fin τ → ℝ) : ℝ :=
  (∑ i,modelConditionalMean g d (X i) θ)/(n : ℝ)

/-- "Y(0)=0,Y(1)=1,X=0,Pr[D=1]=1/4" (T99). -/
def attWitness : FiniteLaw 2 where
  weight := ![3/4,1/4]
  nonneg := by intro i; fin_cases i <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- "At step n remove from each component the open middle interval
of length 4^{−n}" (T31). Bits choose a left or right component. -/
def fatInterval : List Bool → ℝ × ℝ
  | [] => (0,1)
  | b :: w =>
    let I := fatInterval w
    let middle := (I.1+I.2)/2
    let halfGap := (1/4 : ℝ)^(w.length+1)/2
    if b then (middle+halfGap,I.2) else (I.1,middle-halfGap)
/-- Auxiliary representation used for "At step n remove from each component the open middle interval
of length 4^{−n}" (T31; p. 24 and P001-C01-E004): fatStage. -/
def fatStage (n : ℕ) : Set ℝ :=
  {x | ∃ w : List Bool,w.length=n ∧ x∈Set.Icc (fatInterval w).1 (fatInterval w).2}
/-- Auxiliary representation used for "At step n remove from each component the open middle interval
of length 4^{−n}" (T31; p. 24 and P001-C01-E004): fatCantor. -/
def fatCantor : Set ℝ := ⋂ n : ℕ,fatStage n
/-- Auxiliary representation used for "At step n remove from each component the open middle interval
of length 4^{−n}" (T31; p. 24 and P001-C01-E004): fatPDF. -/
def fatPDF (x : ℝ) : ℝ := if x∈fatCantor then 2 else 0
/-- Auxiliary representation used for "At step n remove from each component the open middle interval
of length 4^{−n}" (T31; p. 24 and P001-C01-E004): fatSampleMeasure. -/
def fatSampleMeasure : Measure fatCantor := (2 : ℝ≥0∞) • volume.comap (fun x : fatCantor => x.val)

/-- "1/2 U[-1,1], 1/4 times ±2^{1/U²}" (T61).
Endpoint U=0 is null and uses Lean's total reciprocal. -/
def heavyBootstrapLaw : Measure ℝ :=
  (1/2 : ℝ≥0∞) • uniformLaw (-1) 1 +
  (1/4 : ℝ≥0∞) • (uniformLaw 0 1).map (fun u : ℝ => (2 : ℝ)^(1/u^2)) +
  (1/4 : ℝ≥0∞) • (uniformLaw 0 1).map (fun u : ℝ => -((2 : ℝ)^(1/u^2)))
/-- Auxiliary representation used for "1/2 U[-1,1], 1/4 times ±2^{1/U²}" (T61; p. 131 and P001-C03-N016): sampleMedian. -/
def sampleMedian {n : ℕ} (X : Fin n → ℝ) : ℝ :=
  ((List.ofFn X).mergeSort (fun a b => a ≤ b)).getD (n/2) 0
/-- Auxiliary representation used for "1/2 U[-1,1], 1/4 times ±2^{1/U²}" (T61; p. 131 and P001-C03-N016): regularHeavyStatistic. -/
def regularHeavyStatistic {n : ℕ} (X : Fin n → ℝ) : ℝ :=
  let a := ((Finset.univ.filter (fun i => X i ≤ 0)).card : ℝ)/(n : ℝ)
  if a∈Set.Icc (1/4 : ℝ) (3/4) then a-1/2 else sampleMedian X
/-- Auxiliary representation used for "1/2 U[-1,1], 1/4 times ±2^{1/U²}" (T61; p. 131 and P001-C03-N016): medianCDF. -/
def medianCDF (G : ℝ → ℝ) : ℝ := sInf {x : ℝ | 1/2 ≤ G x}
/-- Auxiliary representation used for "1/2 U[-1,1], 1/4 times ±2^{1/U²}" (T61; p. 131 and P001-C03-N016): regularHeavyFunctional. -/
def regularHeavyFunctional (G : ℝ → ℝ) : ℝ :=
  if G 0∈Set.Icc (1/4 : ℝ) (3/4) then G 0-1/2 else medianCDF G

/-- "sup_x |F(x)−G(x)|" (footnote 31, p. 120).
Only bounded directions enter, so the supremum is finite. -/
def uniformNorm (h : ℝ → ℝ) : ℝ := sSup (Set.range (fun x => |h x|))
/-- Auxiliary representation used for "sup_x |F(x)−G(x)|" (p. 120, footnote 31; T118): IsRealCDF. -/
def IsRealCDF (F : ℝ → ℝ) : Prop :=
  (∀ x,0 ≤ F x ∧ F x ≤ 1) ∧ Monotone F ∧
  (∀ x,Tendsto F (nhdsWithin x (Set.Ici x)) (nhds (F x))) ∧
  Tendsto F atBot (nhds 0) ∧ Tendsto F atTop (nhds 1)
/-- Auxiliary representation used for "sup_x |F(x)−G(x)|" (p. 120, footnote 31; T118): CDFHadamard. -/
def CDFHadamard (T : (ℝ → ℝ) → ℝ) (F : ℝ → ℝ) : Prop :=
  ∃ L : (ℝ → ℝ) → ℝ,
    (∀ f g,L (fun x => f x+g x)=L f+L g) ∧ (∀ a f,L (fun x => a*f x)=a*L f) ∧
    (∃ C : ℝ,0 ≤ C ∧ ∀ h,BddAbove (Set.range (fun x => |h x|)) → |L h| ≤ C*uniformNorm h) ∧
    ∀ h : ℝ → ℝ,BddAbove (Set.range (fun x => |h x|)) →
      ∀ t : ℕ → ℝ,∀ hn : ℕ → ℝ → ℝ,(∀ n,0 < t n) →
        (∀ n,BddAbove (Set.range (fun x => |hn n x|))) → Tendsto t atTop (nhds 0) →
        Tendsto (fun (n : ℕ) => uniformNorm (fun x => hn n x-h x)) atTop (nhds 0) →
        (∀ n,IsRealCDF (fun x => F x+t n*hn n x)) →
        Tendsto (fun (n : ℕ) => (T (fun x => F x+t n*hn n x)-T F)/t n) atTop (nhds (L h))

/-- "f_{Y|X}(y|x)=g(y,x;θ)" (Definition 5.1.1, pp. 178–179).
κ is Lebesgue measure for PDFs or a countable atomic reference for PMFs. -/
def conditionalModelLaw {K τ : ℕ} (νX : Measure (Fin K → ℝ)) (κ : Measure ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (θ : Fin τ → ℝ) : Measure ((Fin K → ℝ) × ℝ) :=
  (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (g xy.2 xy.1 θ))
/-- Auxiliary representation used for "f_{Y|X}(y|x)=g(y,x;θ)" (pp. 178–179, 186, 193–196; T8,T120,T129): conditionalKL. -/
def conditionalKL {K τ : ℕ} (κ : Measure ℝ) (f : ℝ → (Fin K → ℝ) → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (x : Fin K → ℝ) (t : Fin τ → ℝ) : ℝ :=
  ∫ y,f y x*Real.log (f y x/g y x t) ∂κ
/-- Auxiliary representation used for "f_{Y|X}(y|x)=g(y,x;θ)" (pp. 178–179, 186, 193–196; T8,T120,T129): averageKL. -/
def averageKL {K τ : ℕ} (νX : Measure (Fin K → ℝ)) (κ : Measure ℝ)
    (f : ℝ → (Fin K → ℝ) → ℝ) (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ) : ℝ :=
  ∫ x,conditionalKL κ f g x t ∂νX

/-- "F-test compares regression of D on W and X with regression on X"
(Section 7.2.8, p. 270). RSS is computed from actual OLS formulas. -/
def placeboFStatistic {n K L : ℕ} (X : Fin n → Fin K → ℝ) (W : Fin n → Fin L → ℝ) (D : Fin n → ℝ) : ℝ :=
  let R : Matrix (Fin n) (Fin (K+1)) ℝ := fun i => Fin.cases 1 (X i)
  let F : Matrix (Fin n) (Fin (K+L+1)) ℝ := fun i => Fin.cases 1 (Fin.addCases (X i) (W i))
  let rr := olsRSS R D (olsCoef R D)
  let rf := olsRSS F D (olsCoef F D)
  ((rr-rf)/(L : ℝ))/(rf/((n : ℝ)-(K+L+1 : ℕ)))
/-- Auxiliary representation used for "F-test compares regression of D on W and X with regression on X" (p. 270, Section 7.2.8; T124): fReference. -/
def fReference (k v : ℕ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin (k+v) => gaussianReal 0 1)).map (fun z =>
    ((∑ i : Fin (k+v),if i.val < k then (z i)^2 else 0)/(k : ℝ))/
      ((∑ i : Fin (k+v),if k ≤ i.val then (z i)^2 else 0)/(v : ℝ)))

/-- "ρ[X,Y]=Cov[X,Y]/(σ[X]σ[Y])" (Definition 2.2.5, p. 62),
with the same finite sums as the PMF definitions of expectation and variance. -/
def fcorrelation {n : ℕ} (P : FiniteLaw n) (X Y : Fin n → ℝ) : ℝ :=
  fcov P X Y/(Real.sqrt (fvar P X)*Real.sqrt (fvar P Y))

/-- "Y_i=β_0+β_1D_i+β_2X_[1]i+β_3X_[2]i+ε_i"
(Example 7.2.2, p. 259). Row three has X_[1]=10 in the observed data. -/
def causalDesign : Matrix (Fin 6) (Fin 4) ℝ :=
  fun i => ![1,causalExampleD i,causalExampleX1 i,causalExampleX2 i]

/-- "Y ∼ U(−1,1) independent of X" with the stated gap PDF (T3).
The sample space is the actual pair of real observations. -/
def gapJointLaw : Measure (ℝ × ℝ) :=
  (volume.withDensity (fun x => ENNReal.ofReal (gapPDF x))).prod (uniformLaw (-1) 1)

/-- "1/(2πσ_Xσ_Y√(1−ρ²)) exp[−(...)/(2(1−ρ²))]"
(footnote 13, p. 66), with positive scales and |ρ|<1 in the theorem. -/
def bivariateNormalPDF (mx my sx sy ρ : ℝ) (xy : ℝ × ℝ) : ℝ :=
  Real.exp (-(((xy.1-mx)/sx)^2+((xy.2-my)/sy)^2-
    2*ρ*(xy.1-mx)*(xy.2-my)/(sx*sy))/(2*(1-ρ^2))) /
    (2*Real.pi*sx*sy*Real.sqrt (1-ρ^2))

/-- "G_n=PᵀP/n" and "‖G_n−I‖_op" (T6 correction).
For this symmetric matrix, the operator norm is the supremum of the
absolute Rayleigh quotient over Euclidean unit vectors. -/
def sampleGram {K : ℕ} {Ω : Type*} (p : Fin K → Polynomial ℝ)
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Matrix (Fin K) (Fin K) ℝ :=
  fun j k => (∑ i∈Finset.range n,(p j).eval (X i ω)*(p k).eval (X i ω))/(n : ℝ)
/-- Auxiliary representation used for "G_n=PᵀP/n" (T6; pp. 168–169 correction): gramDeviation. -/
def gramDeviation {K : ℕ} (G : Matrix (Fin K) (Fin K) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ v : Fin K → ℝ,(∑ k,(v k)^2)=1 ∧
    r=|(∑ j,∑ k,v j*G j k*v k)-1|}

/-- "E[Y|X=x]" for a discrete conditioning event of positive mass
(Definition 2.2.10, p. 67); normalization is the event probability. -/
def conditionalMeanAt {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → E) (Y : Ω → ℝ) (x : E) : ℝ :=
  (∫ ω in {ω | X ω=x},Y ω ∂μ)/prob μ {ω | X ω=x}

/-- "L(t)=E[log g(Y,X;t)]" and "L_n(t)=n⁻¹∑_i log g(Y_i,X_i;t)"
(proof of Theorem 5.2.6, pp. 193–194). -/
def expectedLogLikelihood {Ω : Type*} [MeasurableSpace Ω] {K τ : ℕ}
    (μ : Measure Ω) (X : Ω → Fin K → ℝ) (Y : Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ) : ℝ :=
  mean μ (fun ω => Real.log (g (Y ω) (X ω) t))
/-- Auxiliary representation used for "L(t)=E[log g(Y,X;t)]" (pp. 193–194, proof of Theorem 5.2.6; T129): sampleLogLikelihood. -/
def sampleLogLikelihood {Ω : Type*} {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (n : ℕ) (ω : Ω) (t : Fin τ → ℝ) : ℝ :=
  sampleMean (fun i ω => Real.log (g (Y i ω) (X i ω) t)) n ω

/-- "g(y,x;θ)=∑_m p_m g_m(y,x;θ_m)" (Section 5.2.5, p. 199).
The theorem requires nonnegative normalized weights and component laws. -/
def mixtureFamily {M K τ : ℕ} (p : (Fin τ → ℝ) → Fin M → ℝ)
    (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (y : ℝ) (x : Fin K → ℝ) (t : Fin τ → ℝ) : ℝ :=
  ∑ m,p t m*g m y x t

/-- "h(xβ)=exp(xβ)/(1+exp(xβ))" (binary-choice model, pp. 183–184).
For a cell of N units and r successes its contribution to log likelihood is
r log p+(N−r)log(1−p). These are the actual likelihoods for T84 and T96. -/
def logitProbability (a b x : ℝ) : ℝ := Real.exp (a+b*x)/(1+Real.exp (a+b*x))
/-- Auxiliary representation used for "h(xβ)=exp(xβ)/(1+exp(xβ))" (T84, T96; pp. 229–230, 265–266; finite examples): groupedLogitLikelihood. -/
def groupedLogitLikelihood (N r : Fin 3 → ℝ) (a b : ℝ) : ℝ :=
  ∑ j, (r j*Real.log (logitProbability a b ((![-1,0,1] : Fin 3 → ℝ) j))+
    (N j-r j)*Real.log (1-logitProbability a b ((![-1,0,1] : Fin 3 → ℝ) j)))
/-- Auxiliary representation used for "h(xβ)=exp(xβ)/(1+exp(xβ))" (T84, T96; pp. 229–230, 265–266; finite examples): missingCellSize. -/
def missingCellSize : Fin 3 → ℝ := fun _ => 4
/-- Auxiliary representation used for "h(xβ)=exp(xβ)/(1+exp(xβ))" (T84, T96; pp. 229–230, 265–266; finite examples): missingCellResponse. -/
def missingCellResponse : Fin 3 → ℝ :=![2,3,2]
/-- Auxiliary representation used for "h(xβ)=exp(xβ)/(1+exp(xβ))" (T84, T96; pp. 229–230, 265–266; finite examples): missingCellOutcomeSum. -/
def missingCellOutcomeSum : Fin 3 → ℝ :=![3/4,3/2,3/4]
/-- Auxiliary representation used for "h(xβ)=exp(xβ)/(1+exp(xβ))" (T84, T96; pp. 229–230, 265–266; finite examples): causalCellSize. -/
def causalCellSize : Fin 3 → ℝ := fun _ => 6
/-- Auxiliary representation used for "h(xβ)=exp(xβ)/(1+exp(xβ))" (T84, T96; pp. 229–230, 265–266; finite examples): causalCellTreatment. -/
def causalCellTreatment : Fin 3 → ℝ :=![3,1,5]
/-- Auxiliary representation used for "h(xβ)=exp(xβ)/(1+exp(xβ))" (T84, T96; pp. 229–230, 265–266; finite examples): causalCellTreatedSum. -/
def causalCellTreatedSum : Fin 3 → ℝ :=![12,3,20]
/-- Auxiliary representation used for "h(xβ)=exp(xβ)/(1+exp(xβ))" (T84, T96; pp. 229–230, 265–266; finite examples): causalCellControlSum. -/
def causalCellControlSum : Fin 3 → ℝ :=![9,10,3]

/-- "Take a with replacement sample of size n" (Section 3.4.3, p. 131).
Conditional expectation of a test function enumerates all n^n equally likely
resampling maps, and uses the statistic recomputed on the resampled observations. -/
def bootstrapTestMean {n : ℕ} (T : (Fin n → ℝ) → ℝ) (X : Fin n → ℝ)
    (f : ℝ → ℝ) : ℝ :=
  (∑ a : Fin n → Fin n,
    f (Real.sqrt n*(T (fun i => X (a i))-T X)))/((n : ℝ)^n)
/-- Auxiliary representation used for "Take a with replacement sample of size n" (p. 131; T61–T62 conditional weak-limit formulation): BootstrapWeakCP. -/
def BootstrapWeakCP {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (sizes : ℕ → ℕ)
    (T : {n : ℕ} → (Fin n → ℝ) → ℝ) (ν : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ,Continuous f → (∃ C : ℝ,∀ x,|f x| ≤ C) →
    CP μ (fun k ω => bootstrapTestMean T (firstSample X (sizes k) ω) f) (mean ν f)

/-- "X̄=(1/n)∑ X_i" (Definition 3.2.2, p. 97).
This equivalent finite-vector form permits exact bootstrap enumeration. -/
def finiteSampleMean {n : ℕ} (X : Fin n → ℝ) : ℝ := (∑ i,X i)/(n : ℝ)

/-- "The (k,k′)th entry is Cov[X_[k],X_[k′]], for all k,k′∈{1,…,K}"
(Definition 2.3.1, p. 84, corrected index quantifier). -/
def covarianceMatrix {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K : ℕ} (X : Ω → Fin K → ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  fun j k => covariance (fun ω => X ω j) (fun ω => X ω k) μ

/-- "sup_x |F(x)−G(x)|" (footnote 31, p. 120).
The infinity-sequence space over the index set ℝ consists of every bounded
function ℝ→ℝ, with its pointwise operations and supremum norm. -/
abbrev KolmogorovSpace := lp (fun _ : ℝ => ℝ) ∞
/-- Auxiliary representation used for "sup_x |F(x)−G(x)|" (p. 120, footnote 31; corrected Theorem 3.3.6, T57): kolmogorovEmbed. -/
def kolmogorovEmbed (f : ℝ → ℝ) : KolmogorovSpace :=
  if hf : Memℓp f ∞ then ⟨f,hf⟩ else 0
/-- Auxiliary representation used for "sup_x |F(x)−G(x)|" (p. 120, footnote 31; corrected Theorem 3.3.6, T57): cdfDomain. -/
def cdfDomain : Set KolmogorovSpace := {f | IsRealCDF (fun x => f x)}
/-- Auxiliary representation used for "sup_x |F(x)−G(x)|" (p. 120, footnote 31; corrected Theorem 3.3.6, T57): empiricalCDFElement. -/
def empiricalCDFElement {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : KolmogorovSpace :=
  kolmogorovEmbed (cdf (empirical X n ω) id)

/-- "requires empirical process theory" (p. 120, after Theorem 3.3.6).
For a bounded, possibly nonmeasurable function, outer expectation is the
infimum of integrals of measurable integrable pointwise majorants.
Taking also the negative lower expectation states asymptotic measurability. -/
def outerMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℝ) : ℝ :=
  sInf {r | ∃ g : Ω → ℝ,Measurable g ∧ Integrable g μ ∧
    (∀ ω,Z ω ≤ g ω) ∧ mean μ g=r}
/-- Auxiliary representation used for "requires empirical process theory" (T57; p. 120, omitted empirical-process proof and topology qualification): OuterWeakLimit. -/
def OuterWeakLimit {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure Ω) (Z : ℕ → Ω → E) (ν : Measure E) : Prop :=
  ∀ f : E → ℝ,Continuous f → (∃ C : ℝ,∀ x,|f x| ≤ C) →
    Tendsto (fun (n : ℕ) => outerMean μ (fun ω => f (Z n ω))) atTop (nhds (mean ν f)) ∧
    Tendsto (fun (n : ℕ) => -outerMean μ (fun ω => -f (Z n ω))) atTop (nhds (mean ν f))

/-- "s=∇ log g" and "I=E[ssᵀ]" (T12, corrected efficiency clause).
Coordinate directions are the independent parameter coordinates, not redundant
mixture weights constrained to sum to one. Derivative existence is a hypothesis. -/
def modelScore {K τ : ℕ}
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (y : ℝ) (x : Fin K → ℝ) (t : Fin τ → ℝ) : Fin τ → ℝ :=
  fun j => fderiv ℝ (fun u => Real.log (g y x u)) t (Pi.single j 1)
/-- Auxiliary representation used for "s=∇ log g" (T12, corrected Section 5.2.5, p. 199; information-bound clause): modelHessian. -/
def modelHessian {K τ : ℕ}
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (y : ℝ) (x : Fin K → ℝ) (t : Fin τ → ℝ) : Matrix (Fin τ) (Fin τ) ℝ :=
  fun j k => fderiv ℝ (fun u => modelScore g y x u j) t (Pi.single k 1)
/-- Auxiliary representation used for "s=∇ log g" (T12, corrected Section 5.2.5, p. 199; information-bound clause): informationMatrix. -/
def informationMatrix {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K τ : ℕ} (X : Ω → Fin K → ℝ) (Y : Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ) : Matrix (Fin τ) (Fin τ) ℝ :=
  fun j k => mean μ (fun ω => modelScore g (Y ω) (X ω) t j*modelScore g (Y ω) (X ω) t k)
/-- Auxiliary representation used for "s=∇ log g" (T12, corrected Section 5.2.5, p. 199; information-bound clause): populationHessian. -/
def populationHessian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K τ : ℕ} (X : Ω → Fin K → ℝ) (Y : Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ) : Matrix (Fin τ) (Fin τ) ℝ :=
  fun j k => mean μ (fun ω => modelHessian g (Y ω) (X ω) t j k)
/-- Auxiliary representation used for "s=∇ log g" (T12, corrected Section 5.2.5, p. 199; information-bound clause): sampleHessian. -/
def sampleHessian {Ω : Type*} {K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (n : ℕ) (ω : Ω) (t : Fin τ → ℝ) : Matrix (Fin τ) (Fin τ) ℝ :=
  fun j k => (∑ i∈Finset.range n,modelHessian g (Y i ω) (X i ω) t j k)/(n : ℝ)
/-- Auxiliary representation used for "s=∇ log g" (T12, corrected Section 5.2.5, p. 199; information-bound clause): normalVectorLaw. -/
def normalVectorLaw {τ : ℕ} (S : Matrix (Fin τ) (Fin τ) ℝ) : Measure (Fin τ → ℝ) :=
  (multivariateGaussian (0 : EuclideanSpace ℝ (Fin τ)) S).map (fun z => fun j => z j)

/-- "T_E(F)=∫ x dF(x)" (p. 118), restricted to finite second moments
in the most favorable reading of the printed claim (T118(B), T1).
A probability CDF determines its law uniquely; a chosen law is used only to
represent that integral. The default outside this domain is irrelevant. -/
def finiteSecondCDF (F : KolmogorovSpace) : Prop :=
  ∃ ν : Measure ℝ,IsProbabilityMeasure ν ∧ MemLp id 2 ν ∧ ∀ x,cdf ν id x=F x
/-- Auxiliary representation used for "T_E(F)=∫ x dF(x)" (pp. 118–120, mean functional and printed claim T118(B)): cdfMeanFunctional. -/
def cdfMeanFunctional (F : KolmogorovSpace) : ℝ :=
  if h : finiteSecondCDF F then mean h.choose id else 0

/-- "â_n=clip_[1/8,3/8](D̄−X̄), p̂_n(x)=â_n+x"
(T15). The stored first component is P=1/4+X. -/
def estimatedMatchIntercept {n : ℕ} (s : Fin n → ℝ × Bool × Bool) : ℝ :=
  clip (1/8) (3/8) ((∑ i,((if (s i).2.1 then (1 : ℝ) else 0)-((s i).1-1/4)))/(n : ℝ))
/-- Auxiliary representation used for "â_n=clip_[1/8,3/8](D̄−X̄), p̂_n(x)=â_n+x" (T15–T16; p. 264; exact estimated-score counterexample): estimatedMatchScore. -/
def estimatedMatchScore {n : ℕ} (s : Fin n → ℝ × Bool × Bool) (i : Fin n) : ℝ :=
  estimatedMatchIntercept s+((s i).1-1/4)
/-- Auxiliary representation used for "â_n=clip_[1/8,3/8](D̄−X̄), p̂_n(x)=â_n+x" (T15–T16; p. 264; exact estimated-score counterexample): causalMatchEstimated. -/
def causalMatchEstimated {n : ℕ} (s : Fin n → ℝ × Bool × Bool) : ℝ :=
  causalMatch (fun i => (estimatedMatchScore s i,(s i).2))

/-- "W_j=1+(number ... matched to respondent/control j)"
(T14, T16 formulas). Non-donors have zero weight. -/
def donorReuseWeight {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool) (j : Fin n) : ℝ :=
  if r j then 1+((Finset.univ.filter (fun i => r i=false ∧ nearestDonor p r i=some j)).card : ℝ) else 0
/-- Auxiliary representation used for "W_j=1+(number ... matched to respondent/control j)" (T14, T16; corrected finite conditional-variance formulas): signProductLaw. -/
def signProductLaw (n : ℕ) : Measure (Fin n → Bool) :=
  Measure.pi (fun _ : Fin n =>
    (1/2 : ℝ≥0∞) • Measure.dirac true+(1/2 : ℝ≥0∞) • Measure.dirac false)

/-- "p_R(x)=Pr[R=1|X=x]=E[R|X=x]" (Section 6.2.4).
E indexes the covariate support and κ x is a conditional binary probability law. -/
def kernelPropensity {E : Type*} (κ : E → Measure Bool) (x : E) : ℝ := prob (κ x) {true}


/-- "The roll of a fair die", with values 1,...,6 and PMF 1/6
(Example 1.2.6, p. 18; corrected CDF examples T28). -/
def fairDieLaw : FiniteLaw 6 where
  weight _ := 1/6
  nonneg _ := by norm_num
  total := by norm_num [Fin.sum_univ_succ]
/-- Auxiliary representation used for "The roll of a fair die" (p. 18, Example 1.2.6; T28): fairDieValue. -/
def fairDieValue (i : Fin 6) : ℝ := (i : ℝ)+1

/-- "Y_i*=1,−99,1,0,1,−99" and "R_i=1,0,1,1,1,0"
(Example 6.1.2, p. 209). Example 6.2.1 adds the binary covariate. -/
def stableExampleYstar : Fin 6 → ℝ := ![1,-99,1,0,1,-99]
/-- Auxiliary representation used for "Y_i*=1,−99,1,0,1,−99" (pp. 209, 214, 219–220, Examples 6.1.2, 6.1.7, 6.2.1; T80, T111): stableExampleR. -/
def stableExampleR : Fin 6 → ℝ := ![1,0,1,1,1,0]
/-- Auxiliary representation used for "Y_i*=1,−99,1,0,1,−99" (pp. 209, 214, 219–220, Examples 6.1.2, 6.1.7, 6.2.1; T80, T111): stableExampleX. -/
def stableExampleX : Fin 6 → Fin 2 := ![0,0,0,0,1,1]
/-- Auxiliary representation used for "Y_i*=1,−99,1,0,1,−99" (pp. 209, 214, 219–220, Examples 6.1.2, 6.1.7, 6.2.1; T80, T111): respondentMean. -/
def respondentMean {n : ℕ} (ystar r : Fin n → ℝ) : ℝ :=
  (∑ i,ystar i*r i)/(∑ i,r i)
/-- Auxiliary representation used for "Y_i*=1,−99,1,0,1,−99" (pp. 209, 214, 219–220, Examples 6.1.2, 6.1.7, 6.2.1; T80, T111): poststratifiedMissingMean. -/
def poststratifiedMissingMean {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (ystar r : Fin n → ℝ) (x : Fin n → E) : ℝ :=
  ∑ t, ((∑ i,if x i=t then ystar i*r i else 0)/(∑ i,if x i=t then r i else 0))*
    ((∑ i,if x i=t then (1 : ℝ) else 0)/(n : ℝ))

/-- "Y_i=1,1,1,0,1,0", "D_i=1,0,1,1,1,0"
(Examples 7.1.5–7.1.6, pp. 238–240). The treatment vector equals
the response vector in the earlier six-unit stable-outcome example. -/
def binaryCausalExampleY : Fin 6 → ℝ := ![1,1,1,0,1,0]

/-- "Θ=[0,1]×[0,1]×[1/4,3/4]" (T11).
The coordinatewise closed interval is exactly this three-coordinate box. -/
def disjointMixtureParameterSet : Set (Fin 3 → ℝ) :=
  Set.Icc (![0,0,1/4]) (![1,1,3/4])
/-- Auxiliary representation used for "Θ=[0,1]×[0,1]×[1/4,3/4]" (T11; p. 199; parameter box [0,1] × [0,1] × [1/4,3/4]): disjointMixtureLikelihood. -/
def disjointMixtureLikelihood {n : ℕ} (y : Fin n → Fin 4) (t : Fin 3 → ℝ) : ℝ :=
  ∏ i,disjointMixture (t 0) (t 1) (t 2) (y i)

/-- "T_1(G)=(G(0)−1/2)^2" (T56(b)). -/
def quadraticCDFFunctional (G : ℝ → ℝ) : ℝ := (G 0-1/2)^2

/-- "(Y(0),Y(1),X(1),X(0),D)" at the six equally weighted points
(Example 7.1.17, p. 253). Both outcome potentials equal postY. -/
def postPotentialX0 : Fin 6 → ℝ := ![0,0,1,0,0,1]
/-- Auxiliary representation used for "(Y(0),Y(1),X(1),X(0),D)" (p. 253, Example 7.1.17; T89): postPotentialX1. -/
def postPotentialX1 : Fin 6 → ℝ := ![0,1,1,0,1,1]

/-- "PDA = ∂E[Y|X]/∂X_[k] at X=E[X]"; the plug-in uses
"X̄" and the estimated CEF (Definition 4.3.7, p. 167). These are summaries
of a chosen predictor unless distributional version invariance is established. -/
def covariateMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K : ℕ} (X : Ω → Fin K → ℝ) : Fin K → ℝ := fun k => mean μ (fun ω => X ω k)
/-- Auxiliary representation used for "PDA = ∂E[Y|X]/∂X_[k] at X=E[X]" (pp. 166–168, Definition 4.3.7; T102): sampleCovariateMean. -/
def sampleCovariateMean {Ω : Type*} {K : ℕ} (X : ℕ → Ω → Fin K → ℝ)
    (n : ℕ) (ω : Ω) : Fin K → ℝ := fun k => sampleMean (fun i z => X i z k) n ω
/-- Auxiliary representation used for "PDA = ∂E[Y|X]/∂X_[k] at X=E[X]" (pp. 166–168, Definition 4.3.7; T102): predictorPDA. -/
def predictorPDA {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K : ℕ} (X : Ω → Fin K → ℝ) (m : (Fin K → ℝ) → ℝ) (k : Fin K) : ℝ :=
  partialAt m (covariateMean μ X) k
/-- Auxiliary representation used for "PDA = ∂E[Y|X]/∂X_[k] at X=E[X]" (pp. 166–168, Definition 4.3.7; T102): pluginPDA. -/
def pluginPDA {Ω : Type*} {K : ℕ} (X : ℕ → Ω → Fin K → ℝ)
    (mhat : ℕ → Ω → (Fin K → ℝ) → ℝ) (n : ℕ) (ω : Ω) (k : Fin K) : ℝ :=
  partialAt (mhat n ω) (sampleCovariateMean X n ω) k

/-- "Z=(X̄−E[X̄])/σ[X̄]" (Definition 3.2.23, p. 109).
The alternate root-n expression is the conclusion of the finite identity. -/
def standardizedMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (sampleMean X n ω-mean μ (sampleMean X n))/Real.sqrt (var μ (sampleMean X n))

/-- "G_n=PᵀP/n" (T6 corrected sieve finite proof). -/
def fixedDesignGram {n K : ℕ} (P : Matrix (Fin n) (Fin K) ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  (n : ℝ)⁻¹ • (P.transpose*P)

/-- "Regression of D on (1,X,W)" (p. 270, placebo test passage).
The target's full coefficients are (29/68,0,4/17). -/
def placeboRegressor (i : Fin 12) : Fin 3 → ℝ := ![1,placeboX i,placeboW i]
/-- Auxiliary representation used for "Regression of D on (1,X,W)" (p. 270 and T17 twelve-point regression calculations): placeboMoment. -/
def placeboMoment : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j k => fmean placeboLaw (fun i => placeboRegressor i j*placeboRegressor i k)
/-- Auxiliary representation used for "Regression of D on (1,X,W)" (p. 270 and T17 twelve-point regression calculations): placeboRisk. -/
def placeboRisk (a b c : ℝ) : ℝ :=
  fmean placeboLaw (fun i => (placeboD i-a-b*placeboX i-c*placeboW i)^2)

/-- "∏_{i=1}^n g(Y_i,X_i;t)" (Definition 5.2.1, p. 186).
Zero conditional-density values give zero likelihood, as in the printed product. -/
def sampleLikelihood {Ω : Type*} {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (n : ℕ) (ω : Ω) (t : Fin τ → ℝ) : ℝ :=
  ∏ i∈Finset.range n,g (Y i ω) (X i ω) t

/-- "For every n and every sample, the joint probability is the product of the four masses"
(T11). This is the actual finite iid sample probability, including null samples. -/
def finiteMixtureSampleProb {n : ℕ} (t : Fin 3 → ℝ)
    (A : (Fin n → Fin 4) → Prop) : ℝ :=
  ∑ y : Fin n → Fin 4,if A y then disjointMixtureLikelihood y t else 0

/-- "Supp[X]={x∈R:f(x)>0}" (Definition 1.2.20, p. 31).
This is the paper's positivity set of a chosen PMF/PDF version. -/
def paperSupport (f : ℝ → ℝ) : Set ℝ := {x | 0 < f x}

/-- A continuous unique maximum on a compact parameter space is separated by a positive objective gap from every point at a fixed positive distance.
Target P001-T8: Theorem 5.2.8 (The ML Estimator Is Consistent for the Minimum KL Divergence Predictor), corrected: the KL divergence averaged over the distribution of $\mathbf{X}$.
Location: p. 195 (PDF p. 213), Theorem 5.2.8; the explanatory paragraphs on p. 196 (PDF p. 214). -/
theorem compact_unique_maximum_separated {E : Type*} [MetricSpace E] (Θ : Set E) (hc : IsCompact Θ)
   (θ : E) (hθ : θ∈Θ) (M : E → ℝ) (hM : ContinuousOn M Θ)
   (hu : ∀ t∈Θ,M t ≤ M θ ∧ (M t=M θ → t=θ)) :
   ∀ ε : ℝ,0 < ε → ∃ δ : ℝ,0 < δ ∧ ∀ t∈Θ,ε ≤ dist t θ → M t ≤ M θ-δ := by
  intro ε hε
  let C := Θ∩{t | ε ≤ dist t θ}
  have hC : IsCompact C := hc.inter_right (isClosed_le continuous_const
    (continuous_id.dist continuous_const))
  by_cases hn : C.Nonempty
  · obtain ⟨x,hx,hxmax⟩ := hC.exists_isMaxOn hn (hM.mono Set.inter_subset_left)
    have hxne : x≠θ := by
      intro h
      have hdist : ε ≤ dist x θ := hx.2
      simp only [h,dist_self] at hdist
      linarith
    have hstrict : M x < M θ := lt_of_le_of_ne (hu x hx.1).1
      (fun he => hxne ((hu x hx.1).2 he))
    refine ⟨M θ-M x,sub_pos.mpr hstrict,?_⟩
    intro t ht hdist
    have he : M t ≤ M x := hxmax (show t∈C from ⟨ht,hdist⟩)
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro t ht hdist
    exact (hn ⟨t,ht,hdist⟩).elim

/-- A sequence on one probability space cannot converge in probability to two distinct points of a metric space.
Target P001-T11: Section 5.2.5, the sentence 'If any subset of the models ... jointly characterize the conditional distribution of $Y$, then this estimator is consistent and asymptotically efficient', as printed.
Location: p. 199 (PDF p. 217), second paragraph; the mixture and its parameter vector: pp. 198–199 (PDF pp. 216–217). -/
theorem probability_limit_unique {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → E) (a b : E)
   (ha : CP μ Z a) (hb : CP μ Z b) : a=b := by
  by_contra hab
  have hd : 0 < dist a b := dist_pos.mpr hab
  have hδ : 0 < dist a b/3 := by positivity
  have hlim : Tendsto (fun (n : ℕ) =>
      prob μ {ω | dist a b/3 ≤ dist (Z n ω) a}+
      prob μ {ω | dist a b/3 ≤ dist (Z n ω) b}) atTop (nhds 0) := by
    simpa only [zero_add] using (ha _ hδ).add (hb _ hδ)
  have hbound (n : ℕ) : (1 : ℝ) ≤ 
      prob μ {ω | dist a b/3 ≤ dist (Z n ω) a}+
      prob μ {ω | dist a b/3 ≤ dist (Z n ω) b} := by
    have hs : (Set.univ : Set Ω)⊆
        {ω | dist a b/3 ≤ dist (Z n ω) a}∪{ω | dist a b/3 ≤ dist (Z n ω) b} := by
      intro ω hω
      by_contra h
      simp only [Set.mem_union,Set.mem_setOf_eq,not_or,not_le] at h
      have ht : dist a b ≤ dist (Z n ω) a+dist (Z n ω) b := by
        simpa only [dist_comm a (Z n ω)] using dist_triangle a (Z n ω) b
      linarith
    have h := (measureReal_mono (μ := μ) hs).trans (measureReal_union_le _ _)
    simpa [Measure.real,AronowAudit.P001.prob] using h
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hbound)
  norm_num at hbad

/-- Every finite iid sample mean retains the population finite second moment.
Target P001-T108: Theorem 3.2.3 (The Expected Value of the Sample Mean Is the Population Mean), Theorem 3.2.4 (Sampling Variance of the Sample Mean) and Theorem 3.2.5 (Chebyshev's Inequality for the Sample Mean).
Location: Theorem 3.2.3: p. 97 (PDF p. 115). Theorems 3.2.4 and 3.2.5: p. 98 (PDF p. 116), proof of 3.2.5 continuing on p. 99 (PDF p. 117). -/
theorem sample_mean_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ) (n : ℕ) :
   MemLp (sampleMean X n) 2 μ := by
  have hi2 : ∀ i,MemLp (X i) 2 μ := fun i => (hiid.2.2 i).symm.memLp_snd h2
  have hfun : sampleMean X n=(fun ω => (n : ℝ)⁻¹*(∑ i∈Finset.range n,X i ω)) := by
    funext ω
    simp [AronowAudit.P001.sampleMean,div_eq_mul_inv,mul_comm]
  rw [hfun]
  exact (memLp_finsetSum (Finset.range n) (fun i _ => hi2 i)).const_mul ((n : ℝ)⁻¹)

/-- For each finite-variance real random variable, the event at least epsilon from its mean has probability at most variance divided by epsilon squared.
Target P001-T106: Theorem 2.1.9 (Linearity of Expectations), Theorem 2.1.13 (Alternative Formula for Variance), Theorem 2.1.14 (Properties of Variance), Theorem 2.1.16 (Properties of Standard Deviation) and Theorem 2.1.18 (Chebyshev's Inequality).
Location: Theorem 2.1.9: p. 49 (PDF p. 67). Theorems 2.1.13 and 2.1.14: p. 52 (PDF p. 70). Theorem 2.1.16: p. 53 (PDF p. 71). Theorem 2.1.18: p. 55 (PDF p. 73). -/
theorem chebyshev_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : Ω → ℝ) (hX : MemLp X 2 μ) (ε : ℝ) (hε : 0 < ε) :
   prob μ {ω | ε ≤ |X ω-mean μ X|} ≤ var μ X/ε^2 := by
  have h := meas_ge_le_variance_div_sq hX hε
  have hnon : 0 ≤ variance X μ/ε^2 := div_nonneg (variance_nonneg _ _) (sq_nonneg _)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hnon)


/-- The first K+1 geometric masses sum exactly to 1 minus the tail mass.
Target P001-T1: Section 3.3.1, the sentence 'our assumption about finite variance was sufficient to imply that the population mean is well behaved', read with footnote 31, as printed.
Location: p. 120 (PDF p. 138), paragraph after Theorem 3.3.6, and footnote 31. The mean functional $T_{\mathrm{E}}$: p. 118 (PDF p. 136). -/
theorem geometric_partial_mass (K : ℕ) : ∑ k ∈ Finset.range (K+1), geoMass k = 1 - (1/2 : ℝ)^(K+1) := by
  induction K with
  | zero => norm_num [geoMass]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [geoMass, pow_succ]
    ring


/-- Continuous functions that agree Lebesgue-almost everywhere on an open set agree throughout it; their totalized coordinate-derivative values at any point of that set are equal. This supporting lemma does not assert derivative existence.
Target P001-T4: Definition 4.3.7 (Partial Derivative at the Average), corrected with a support condition at the covariate mean.
Location: p. 167 (PDF p. 185), Definition 4.3.7; p. 168 (PDF p. 186), first paragraph. -/
theorem pda_unique_on_open_support_supporting {K : ℕ} (U : Set (Fin K → ℝ)) (hU : IsOpen U) (x : Fin K → ℝ)
   (hx : x ∈ U) (m m' : (Fin K → ℝ) → ℝ)
   (hm : ContinuousOn m U) (hm' : ContinuousOn m' U)
   (heq : m =ᵐ[volume.restrict U] m') (k : Fin K) :
   Set.EqOn m m' U ∧ partialAt m x k = partialAt m' x k := by
  
  have he : Set.EqOn m m' U := Measure.eqOn_open_of_ae_eq heq hU hm hm'
  refine ⟨he, ?_⟩
  unfold partialAt
  apply Filter.EventuallyEq.deriv_eq
  have ht : Continuous (fun t : ℝ => Function.update x k (x k+t)) := by fun_prop
  have hmem : ∀ᶠ t in nhds (0 : ℝ), Function.update x k (x k+t)∈U :=
    ht.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hx)
  filter_upwards [hmem] with t ht
  exact he ht


/-- Uniform objective error Δ and optimization error e bound the population objective loss by 2Δ+e.
Target P001-T8: Theorem 5.2.8 (The ML Estimator Is Consistent for the Minimum KL Divergence Predictor), corrected: the KL divergence averaged over the distribution of $\mathbf{X}$.
Location: p. 195 (PDF p. 213), Theorem 5.2.8; the explanatory paragraphs on p. 196 (PDF p. 214). -/
theorem argmax_finite_gap {E : Type*} (M L : E → ℝ) (t tstar : E) (Δ e : ℝ)
   (h1 : |L t-M t|  ≤  Δ) (h2 : |L tstar-M tstar|  ≤  Δ)
   (hopt : L tstar-e  ≤  L t) : M tstar-M t  ≤  2*Δ+e := by
  
  have a := (abs_le.mp h1).2
  have b := (abs_le.mp h2).1
  linarith

/-- Uniform convergence in probability of a criterion to a separated population maximum and vanishing approximate maximization error imply consistency.
Target P001-T8: Theorem 5.2.8 (The ML Estimator Is Consistent for the Minimum KL Divergence Predictor), corrected: the KL divergence averaged over the distribution of $\mathbf{X}$.
Location: p. 195 (PDF p. 213), Theorem 5.2.8; the explanatory paragraphs on p. 196 (PDF p. 214). -/
theorem separated_argmax_consistency {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (Θ : Set E) (M : E → ℝ)
   (L : ℕ → Ω → E → ℝ) (that : ℕ → Ω → E) (tstar : E) (ht : tstar ∈ Θ)
   (hthat : ∀ n ω, that n ω ∈ Θ) (Δ e : ℕ → Ω → ℝ)
   (hΔ : ∀ n ω t, t ∈ Θ → |L n ω t-M t|  ≤  Δ n ω)
   (hopt : ∀ n ω t, t ∈ Θ → L n ω t-e n ω  ≤  L n ω (that n ω))
   (hsep : ∀ ε : ℝ, 0  <  ε → ∃ δ : ℝ, 0  <  δ ∧
     ∀ t ∈ Θ, ε  ≤  dist t tstar → M t  ≤  M tstar-δ)
   (hlimΔ : CP μ Δ 0) (hlime : CP μ e 0) : CP μ that tstar := by
  
  intro ε hε
  obtain ⟨δ,hδ,hsepδ⟩ := hsep ε hε
  have hD : 0 < δ/4 := by positivity
  have he : 0 < δ/2 := by positivity
  have hlim : Tendsto (fun (n : ℕ) => prob μ {ω | δ/4 ≤ dist (Δ n ω) 0}+
      prob μ {ω | δ/2 ≤ dist (e n ω) 0}) atTop (nhds 0) := by
    simpa only [zero_add] using (hlimΔ _ hD).add (hlime _ he)
  have hbound (n : ℕ) : prob μ {ω | ε ≤ dist (that n ω) tstar} ≤ 
      prob μ {ω | δ/4 ≤ dist (Δ n ω) 0}+prob μ {ω | δ/2 ≤ dist (e n ω) 0} := by
    have hs : {ω | ε ≤ dist (that n ω) tstar}⊆
        {ω | δ/4 ≤ dist (Δ n ω) 0}∪{ω | δ/2 ≤ dist (e n ω) 0} := by
      intro ω hω
      have hg := hsepδ (that n ω) (hthat n ω) hω
      have ha := argmax_finite_gap M (L n ω) (that n ω) tstar (Δ n ω) (e n ω)
        (hΔ n ω _ (hthat n ω)) (hΔ n ω tstar ht) (hopt n ω tstar ht)
      by_contra h
      simp only [Set.mem_union,Set.mem_setOf_eq,not_or,not_le,Real.dist_eq,sub_zero] at h
      have hΔlt := (le_abs_self (Δ n ω)).trans_lt h.1
      have helt := (le_abs_self (e n ω)).trans_lt h.2
      linarith
    exact (measureReal_mono (μ := μ) hs).trans (measureReal_union_le _ _)
  exact squeeze_zero' (Eventually.of_forall (fun (n : ℕ) => ENNReal.toReal_nonneg))
    (Eventually.of_forall hbound) hlim



theorem integral_affine_iic (K : ℝ → ℝ) (a h x : ℝ) (hh : 0<h) :
    (∫ u in Set.Iic x,K ((u-a)/h))=
      h*(∫ t in Set.Iic ((x-a)/h),K t) := by
  classical
  let F := (Set.Iic ((x-a)/h)).indicator K
  have he (u : ℝ) : (Set.Iic x).indicator (fun u => K ((u-a)/h)) u=F ((u-a)/h) := by
    have hi : (u-a)/h≤(x-a)/h ↔ u≤x := by
      rw [div_le_div_iff_of_pos_right hh,sub_le_sub_iff_right]
    by_cases hu : u≤x <;> simp [F,Set.indicator,Set.mem_Iic,hu,hi]
  calc
    _ = ∫ u,F ((u-a)/h) := by
      rw [← integral_indicator measurableSet_Iic]
      exact integral_congr_ae (ae_of_all _ he)
    _ = ∫ u,F (u/h) := integral_sub_right_eq_self (fun u => F (u/h)) a
    _ = _ := by
      rw [Measure.integral_comp_div,abs_of_pos hh,smul_eq_mul]
      dsimp [F]
      rw [integral_indicator measurableSet_Iic]

theorem integrable_density_cdf_properties (f : ℝ → ℝ) (hf : Integrable f volume)
    (hpos : ∀ᵐ x ∂volume,0≤f x) (hnorm : (∫ x,f x)=1) :
    Monotone (fun x => ∫ t in Set.Iic x,f t) ∧
    Continuous (fun x => ∫ t in Set.Iic x,f t) ∧
    Tendsto (fun x => ∫ t in Set.Iic x,f t) atBot (nhds 0) ∧
    Tendsto (fun x => ∫ t in Set.Iic x,f t) atTop (nhds 1) := by
  let ν := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have hν : IsProbabilityMeasure ν := by
    constructor
    change volume.withDensity (fun x => ENNReal.ofReal (f x)) Set.univ=1
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hf hpos,hnorm]
    norm_num
  letI := hν
  have he : (fun x => ∫ t in Set.Iic x,f t)=ProbabilityTheory.cdf ν := by
    funext x
    rw [ProbabilityTheory.cdf_eq_real,measureReal_def]
    change _=(volume.withDensity (fun x => ENNReal.ofReal (f x)) (Set.Iic x)).toReal
    rw [withDensity_apply _ measurableSet_Iic]
    exact integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hpos)
      hf.integrableOn.aestronglyMeasurable
  rw [he]
  exact ⟨monotone_cdf ν,continuous_iff_continuousAt.mpr
    (fun x => AronowAudit.P053.NormalCompletion.cdf_continuousAt ν x),
    tendsto_cdf_atBot ν,tendsto_cdf_atTop ν⟩

theorem signed_kernel_indicator : signedKernel=(fun t =>
    (3/2:ℝ)*(Set.Icc (-1:ℝ) 1).indicator (fun _ => (1:ℝ)) t-
    (1/2:ℝ)*(Set.Icc (-2:ℝ) 2).indicator (fun _ => (1:ℝ)) t) := by
  funext t
  have h1 : t∈Set.Icc (-1:ℝ) 1 ↔ |t|≤1 := by simp [abs_le]
  have h2 : t∈Set.Icc (-2:ℝ) 2 ↔ |t|≤2 := by simp [abs_le]
  by_cases ht1 : |t|≤1
  · have ht2 : |t|≤2 := by linarith
    norm_num [signedKernel,Set.indicator,h1,h2,ht1,ht2]
  · by_cases ht2 : |t|≤2 <;> norm_num [signedKernel,Set.indicator,h1,h2,ht1,ht2]

theorem signed_kernel_integrals : Integrable signedKernel volume ∧
    (∫ t,signedKernel t)=1 ∧ (∫ t in Set.Iic (-1:ℝ),signedKernel t)= -1/2 := by
  have hi (a b : ℝ) : Integrable ((Set.Icc a b).indicator (fun _ : ℝ => (1:ℝ))) volume := by
    have hc : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Icc a b) volume :=
      integrableOn_const (by simp [Real.volume_Icc])
    exact hc.integrable_indicator measurableSet_Icc
  have ha := (hi (-1) 1).const_mul (3/2:ℝ)
  have hb := (hi (-2) 2).const_mul (1/2:ℝ)
  have hk : Integrable signedKernel volume := by rw [signed_kernel_indicator];exact ha.sub hb
  have hall : (∫ t,signedKernel t)=1 := by
    rw [signed_kernel_indicator,integral_sub ha hb,integral_const_mul,integral_const_mul,
      integral_indicator measurableSet_Icc,integral_indicator measurableSet_Icc]
    norm_num [integral_const,measureReal_def,Real.volume_Icc]
  have he (a b c : ℝ) : Set.Icc a b ∩ Set.Iic c=Set.Icc a (min b c) := by
    ext t
    simp only [Set.mem_inter_iff,Set.mem_Icc,Set.mem_Iic,le_min_iff]
    tauto
  have hpart : (∫ t in Set.Iic (-1:ℝ),signedKernel t)= -1/2 := by
    rw [signed_kernel_indicator,integral_sub ha.integrableOn hb.integrableOn,
      integral_const_mul,integral_const_mul,
      integral_indicator measurableSet_Icc,integral_indicator measurableSet_Icc]
    norm_num [integral_const,measureReal_def,Measure.restrict_apply measurableSet_Icc,
      he,Real.volume_Icc]
  exact ⟨hk,hall,hpart⟩

/-- A nonempty compact restriction with scales bounded below and exponential rate bounded below gives a continuous likelihood and an attained maximum.
Target P001-T10: Section 5.2.5 and Example 5.2.11, corrected: maximization of the mixture likelihood qualified by existence of a maximum; the unrestricted mixture has unbounded likelihood on positive samples; a compact restriction under which a maximum is attained.
Location: pp. 198–200 (PDF pp. 216–218); Figure 5.2.5, p. 201 (PDF p. 219). -/
theorem mixture_compact_attainment {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, 0  <  y i)
   (B S δ a b : ℝ) (hδ : 0  <  δ) (ha : 0  <  a)
   (hne : (mixtureRestriction B S δ a b).Nonempty) :
   IsCompact (mixtureRestriction B S δ a b) ∧
   ContinuousOn (mixtureLikelihood y) (mixtureRestriction B S δ a b) ∧
   ∃ θ ∈ mixtureRestriction B S δ a b, ∀ θ' ∈ mixtureRestriction B S δ a b,
     mixtureLikelihood y θ'  ≤  mixtureLikelihood y θ := by
  have he : mixtureRestriction B S δ a b=
      {θ : Fin 7 → ℝ | 0≤θ 0 ∧ 0≤θ 1 ∧ θ 0+θ 1≤1 ∧ |θ 2|≤B ∧ |θ 4|≤B ∧
        δ≤θ 3 ∧ θ 3≤S ∧ δ≤θ 5 ∧ θ 5≤S ∧ a≤θ 6 ∧ θ 6≤b} := by
    ext θ
    dsimp [mixtureRestriction,MixtureAdmissible]
    constructor
    · rintro ⟨⟨h0,h1,hw,hs,ht,hr⟩,h2,h4,h3l,h3u,h5l,h5u,h6l,h6u⟩
      exact ⟨h0,h1,hw,h2,h4,h3l,h3u,h5l,h5u,h6l,h6u⟩
    · rintro ⟨h0,h1,hw,h2,h4,h3l,h3u,h5l,h5u,h6l,h6u⟩
      exact ⟨⟨h0,h1,hw,lt_of_lt_of_le hδ h3l,lt_of_lt_of_le hδ h5l,
        lt_of_lt_of_le ha h6l⟩,h2,h4,h3l,h3u,h5l,h5u,h6l,h6u⟩
  have hclosed : IsClosed (mixtureRestriction B S δ a b) := by
    rw [he]
    have hf (j : Fin 7) : Continuous (fun θ : Fin 7 → ℝ => θ j) := continuous_apply j
    exact (isClosed_le continuous_const (hf 0)).inter
      ((isClosed_le continuous_const (hf 1)).inter
      ((isClosed_le ((hf 0).add (hf 1)) continuous_const).inter
      ((isClosed_le (hf 2).abs continuous_const).inter
      ((isClosed_le (hf 4).abs continuous_const).inter
      ((isClosed_le continuous_const (hf 3)).inter
      ((isClosed_le (hf 3) continuous_const).inter
      ((isClosed_le continuous_const (hf 5)).inter
      ((isClosed_le (hf 5) continuous_const).inter
      ((isClosed_le continuous_const (hf 6)).inter
        (isClosed_le (hf 6) continuous_const))))))))))
  have hsub : mixtureRestriction B S δ a b ⊆
      Set.Icc (![0,0,-B,δ,-B,δ,a] : Fin 7 → ℝ) ![1,1,B,S,B,S,b] := by
    intro θ hθ
    rw [he] at hθ
    rcases hθ with ⟨h0,h1,hw,h2,h4,h3l,h3u,h5l,h5u,h6l,h6u⟩
    have h2' := abs_le.mp h2
    have h4' := abs_le.mp h4
    constructor <;> intro i <;> fin_cases i <;> simp <;> linarith
  have hc : IsCompact (mixtureRestriction B S δ a b) :=
    isCompact_Icc.of_isClosed_subset hclosed hsub
  have hcont : ContinuousOn (mixtureLikelihood y) (mixtureRestriction B S δ a b) := by
    intro θ hθ
    have hs : 0<θ 3 := hθ.1.2.2.2.1
    have ht : 0<θ 5 := hθ.1.2.2.2.2.1
    apply ContinuousAt.continuousWithinAt
    unfold mixtureLikelihood
    apply tendsto_finsetProd
    intro i hi
    change ContinuousAt (fun θ' : Fin 7 → ℝ => mixtureDensity θ' (y i)) θ
    have hs0 : θ 3≠0 := hs.ne'
    have ht0 : θ 5≠0 := ht.ne'
    have hπ : Real.sqrt (2*Real.pi)≠0 := by positivity
    have hcoord (j : Fin 7) : ContinuousAt (fun θ' : Fin 7 → ℝ => θ' j) θ :=
      (continuous_apply j).continuousAt
    have hnd (j k : Fin 7) (z : ℝ) (hk : θ k≠0) :
        ContinuousAt (fun θ' : Fin 7 → ℝ => normalDensity (θ' j) (θ' k) z) θ := by
      unfold normalDensity
      apply ContinuousAt.div
      · apply Real.continuous_exp.continuousAt.comp
        exact (((continuousAt_const.sub (hcoord j)).pow 2).neg).div
          (continuousAt_const.mul ((hcoord k).pow 2)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hk))
      · exact (hcoord k).mul continuousAt_const
      · exact mul_ne_zero hk hπ
    simp only [mixtureDensity,lognormalDensity,exponentialDensity,if_pos (hy i),
      if_pos (hy i).le]
    exact (((hcoord 0).mul (hnd 2 3 (y i) hs0)).add
      ((hcoord 1).mul ((hnd 4 5 (Real.log (y i)) ht0).div_const (y i)))).add
      (((continuousAt_const.sub (hcoord 0)).sub (hcoord 1)).mul
        ((hcoord 6).mul (Real.continuous_exp.continuousAt.comp ((hcoord 6).neg.mul continuousAt_const))))
  exact ⟨hc,hcont,hc.exists_isMaxOn hne hcont⟩

/-- The compact-model parameter vectors (1,1/3,1/4) and (1,1/3,3/4) give the same normalized PMF and all sample likelihoods, while their 1/8 neighborhoods in the unused coordinate are disjoint.
Target P001-T11: Section 5.2.5, the sentence 'If any subset of the models ... jointly characterize the conditional distribution of $Y$, then this estimator is consistent and asymptotically efficient', as printed.
Location: p. 199 (PDF p. 217), second paragraph; the mixture and its parameter vector: pp. 198–199 (PDF pp. 216–217). -/
theorem unused_component_nonidentification_supporting : disjointMixture 1 (1/3) (1/4) = disjointMixture 1 (1/3) (3/4) ∧
   (∑ i : Fin 4, disjointMixture 1 (1/3) (1/4) i) = 1 ∧
   (∀ i : Fin 4, 0  ≤  disjointMixture 1 (1/3) (1/4) i) ∧
   (∀ n (y : Fin n → Fin 4), (∏ i, disjointMixture 1 (1/3) (1/4) (y i)) =
     ∏ i, disjointMixture 1 (1/3) (3/4) (y i)) ∧
   (∀ b : ℝ, ¬ (|b-1/4|  <  1/8 ∧ |b-3/4|  <  1/8)) := by
  have heq : disjointMixture 1 (1/3) (1/4) = disjointMixture 1 (1/3) (3/4) := by
    ext i; fin_cases i <;> norm_num [disjointMixture]
  refine ⟨heq, ?_, ?_, ?_, ?_⟩
  · norm_num [disjointMixture, Fin.sum_univ_succ]
  · intro i; fin_cases i <;> norm_num [disjointMixture]
  · intro n y; rw [heq]
  · intro b h
    have h1 := (abs_lt.mp h.1).2
    have h2 := (abs_lt.mp h.2).1
    linarith


/-- The twelve-atom design satisfies the placebo conditional-independence null and has Cov(W,D)=1/9 and Var(W)=17/36; the two specified population residual formulas have mean squares 35/144 and 59/272.
Target P001-T17: Section 7.2.8 (Placebo Testing): the $F$-test comparing a regression of $D_i$ on $\mathbf{W}_i$ and $\mathbf{X}_i$ with a regression of $D_i$ on $\mathbf{X}_i$ alone, as a test of $\mathbf{W}_i \perp\!\!\!\perp D_i|\mathbf{X}_i$, as printed.
Location: p. 270 (PDF p. 288), Section 7.2.8. -/
theorem placebo_linear_test_counterexample_supporting : FCondIndep placeboLaw placeboW placeboD placeboX ∧
   fmean placeboLaw placeboX = 0 ∧ fmean placeboLaw placeboD = 7/12 ∧
   fvar placeboLaw placeboW = 17/36 ∧ fcov placeboLaw placeboW placeboD = 1/9 ∧
   fmean placeboLaw (fun i => (placeboD i-7/12)^2) = 35/144 ∧
   fmean placeboLaw (fun i => (placeboD i-29/68-(4/17)*placeboW i)^2) = 59/272 ∧
   (35/144-59/272 : ℝ)/(59/272) = 64/531 ∧ (0 : ℝ)  <  4/17 := by
  
  refine ⟨?_, ?_⟩
  · intro x y z hx
    by_cases hx1 : x=(-1 : ℝ)
    · subst x
      norm_num [fprob,placeboLaw,placeboX,placeboZ,placeboW,placeboD,Fin.sum_univ_succ]
      by_cases hy1 : y=(1/2 : ℝ) <;> by_cases hy2 : y=(3/2 : ℝ) <;>
        by_cases hz1 : z=(0 : ℝ) <;> by_cases hz2 : z=(1 : ℝ) <;>
        norm_num at hy1 hy2 hz1 hz2 <;>
        norm_num [hy1,hy2,hz1,hz2,eq_comm]
    · by_cases hx0 : x=(0 : ℝ)
      · subst x
        norm_num [fprob,placeboLaw,placeboX,placeboZ,placeboW,placeboD,Fin.sum_univ_succ]
        by_cases hy1 : y=(-1/2 : ℝ) <;> by_cases hy2 : y=(1/2 : ℝ) <;>
          by_cases hz1 : z=(0 : ℝ) <;> by_cases hz2 : z=(1 : ℝ) <;>
          norm_num at hy1 hy2 hz1 hz2 <;>
          norm_num [hy1,hy2,hz1,hz2,eq_comm]
      · by_cases hx2 : x=(1 : ℝ)
        · subst x
          norm_num [fprob,placeboLaw,placeboX,placeboZ,placeboW,placeboD,Fin.sum_univ_succ]
          by_cases hy1 : y=(1/2 : ℝ) <;> by_cases hy2 : y=(3/2 : ℝ) <;>
            by_cases hz1 : z=(0 : ℝ) <;> by_cases hz2 : z=(1 : ℝ) <;>
            norm_num at hy1 hy2 hz1 hz2 <;>
            norm_num [hy1,hy2,hz1,hz2,eq_comm]
        · norm_num [fprob,placeboLaw,placeboX,Fin.sum_univ_succ,hx1,hx0,hx2,eq_comm] at hx
  · norm_num [fmean,fvar,fcov,placeboLaw,placeboX,placeboZ,placeboW,placeboD,Fin.sum_univ_succ]


/-- The normalized countable joint PMF has mass 1/2 in each arm and every covariate value in both supports, but no common positive lower propensity bound.
Target P001-T19: Section 7.3: 'a failure of the positivity assumption logically implies incomplete (or “limited”) overlap', and the converse of Theorem 7.3.2 that 'can almost be stated', as printed.
Location: p. 271 (PDF p. 289), paragraph before Definition 7.3.1 and the sentence after Theorem 7.3.2, continuing on p. 272 (PDF p. 290). -/
theorem complete_overlap_without_uniform_positivity : Summable overlapT ∧ Summable overlapC ∧ (∑' k, overlapT k) = 1/2 ∧
   (∑' k, overlapC k) = 1/2 ∧ (∀ k, 0  <  overlapT k ∧ 0  <  overlapC k ∧
     0  <  overlapPropensity k ∧ overlapPropensity k  <  1) ∧
   ¬ ∃ ε : ℝ, 0  <  ε ∧ ∀ k, ε  <  overlapPropensity k ∧ overlapPropensity k  <  1-ε := by
  have hT : overlapT=fun k : ℕ => (1/3:ℝ)^k*(1/3) := by
    funext k; simp [overlapT,pow_succ]
  have hC : overlapC=fun k : ℕ => (1/2:ℝ)^k*(1/4) := by
    funext k; simp [overlapC,pow_add]; ring
  have hsT : Summable overlapT := by
    rw [hT]
    exact (summable_geometric_of_abs_lt_one (by norm_num : |(1/3:ℝ)|<1)).mul_right _
  have hsC : Summable overlapC := by
    rw [hC]
    exact (summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)).mul_right _
  have ht : (∑' k, overlapT k)=1/2 := by
    rw [hT,tsum_mul_right,tsum_geometric_of_abs_lt_one (by norm_num : |(1/3:ℝ)|<1)]
    norm_num
  have hc : (∑' k, overlapC k)=1/2 := by
    rw [hC,tsum_mul_right,tsum_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)]
    norm_num
  have hp (k : ℕ) : 0<overlapT k ∧ 0<overlapC k := by
    constructor <;> dsimp [overlapT,overlapC] <;> positivity
  have hprop (k : ℕ) : 0<overlapPropensity k ∧ overlapPropensity k<1 := by
    dsimp [overlapPropensity]
    exact ⟨div_pos (hp k).1 (add_pos (hp k).1 (hp k).2),
      (div_lt_one (add_pos (hp k).1 (hp k).2)).mpr (by linarith [(hp k).2])⟩
  have hbound (k : ℕ) : overlapPropensity k≤(4/3:ℝ)*(2/3:ℝ)^k := by
    have he : overlapT k/overlapC k=(4/3:ℝ)*(2/3:ℝ)^k := by
      simp only [overlapT,overlapC,pow_add,pow_one,div_pow,one_pow]
      field_simp
      <;> ring
    rw [← he]
    exact div_le_div_of_nonneg_left (hp k).1.le (hp k).2 (by linarith [(hp k).1])
  have hlim : Tendsto overlapPropensity atTop (nhds 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤2/3) (by norm_num : (2/3:ℝ)<1)).const_mul (4/3:ℝ)
    simp only [mul_zero] at hh
    exact squeeze_zero (fun k => (hprop k).1.le) hbound hh
  refine ⟨hsT,hsC,ht,hc,fun k => ⟨(hp k).1,(hp k).2,(hprop k).1,(hprop k).2⟩,?_⟩
  rintro ⟨ε,hε,hεb⟩
  have hev := (tendsto_order.1 hlim).2 ε hε
  rcases (eventually_atTop.1 hev) with ⟨N,hN⟩
  exact (not_lt_of_ge (hεb N).1.le) (hN N le_rfl)

/-- For a discrete joint PMF, equality of the arm supports is equivalent to pointwise propensity strictly between zero and one on the marginal support.
Target P001-T20: Section 7.3, the relation between positivity and complete population overlap, corrected; with Theorem 7.3.2 (Positivity Implies Complete Population Overlap).
Location: p. 271 (PDF p. 289), paragraph before Definition 7.3.1, Definition 7.3.1, Theorem 7.3.2 and the sentence after it (continuing on p. 272, PDF p. 290). -/
theorem discrete_overlap_pointwise {E : Type*} (t c : E → ℝ) (ht : ∀ x, 0  ≤  t x) (hc : ∀ x, 0  ≤  c x) :
   {x | 0  <  t x} = {x | 0  <  c x} ↔
   ∀ x, 0  <  t x+c x → 0  <  t x/(t x+c x) ∧ t x/(t x+c x)  <  1 := by
  constructor
  · intro h x hx
    have htpos : 0  <  t x := by
      by_contra hn
      have hz : t x = 0 := le_antisymm (le_of_not_gt hn) (ht x)
      have hcpos : 0  <  c x := by linarith
      have he : (0 < t x ↔ 0 < c x) := by simpa using Set.ext_iff.mp h x
      have : 0 < t x := he.mpr hcpos
      simp only [Set.mem_setOf_eq, hz, lt_self_iff_false] at this
    have he : (0 < t x ↔ 0 < c x) := by simpa using Set.ext_iff.mp h x
    have hcpos : 0  <  c x := he.mp htpos
    exact ⟨div_pos htpos hx, (div_lt_one hx).mpr (by linarith)⟩
  · intro h
    ext x
    constructor
    · intro hx
      have hs : 0  <  t x+c x := by dsimp at hx; linarith [hc x]
      have hlt := (div_lt_one hs).mp (h x hs).2
      dsimp; linarith
    · intro hx
      have hs : 0  <  t x+c x := by dsimp at hx; linarith [ht x]
      have hpos := (div_pos_iff.mp (h x hs).1)
      rcases hpos with hpos | hpos
      · exact hpos.1
      · linarith

/-- On finite covariate support, pointwise positivity implies one uniform strict propensity bound.
Target P001-T20: Section 7.3, the relation between positivity and complete population overlap, corrected; with Theorem 7.3.2 (Positivity Implies Complete Population Overlap).
Location: p. 271 (PDF p. 289), paragraph before Definition 7.3.1, Definition 7.3.1, Theorem 7.3.2 and the sentence after it (continuing on p. 272, PDF p. 290). -/
theorem finite_overlap_uniform_bound {E : Type*} [Fintype E] (p : E → ℝ) (hp : ∀ x, 0  <  p x ∧ p x  <  1) :
   ∃ ε : ℝ, 0  <  ε ∧ ∀ x, ε  <  p x ∧ p x  <  1-ε := by
  
  have hfinite (s : Finset E) :
      ∃ ε : ℝ,0 < ε ∧ ∀ x∈s,ε < p x ∧ p x < 1-ε := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert a s ha ih =>
      rcases ih with ⟨ε,hε,hs⟩
      rcases hp a with ⟨hpa,hpa1⟩
      let δ := min ε (min (p a/2) ((1-p a)/2))
      have hδ : 0 < δ := by dsimp [δ]; positivity
      have hδε : δ ≤ ε := min_le_left _ _
      have hδp : δ ≤ p a/2 := le_trans (min_le_right _ _) (min_le_left _ _)
      have hδq : δ ≤ (1-p a)/2 := le_trans (min_le_right _ _) (min_le_right _ _)
      refine ⟨δ,hδ,?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with hxa|hx
      · subst x
        constructor <;> linarith
      · rcases hs x hx with ⟨hxp,hxp1⟩
        constructor <;> linarith
  rcases hfinite Finset.univ with ⟨ε,hε,hall⟩
  exact ⟨ε,hε,fun x => hall x (Finset.mem_univ x)⟩

/-- The explicit electorate design has individual effect five, treatment probability one half, observable treatment contrast twenty-five, and unequal probabilities for the electorate-type independence equation.
Target P001-T21: Section 7.5, the claim that if the coded applicant descriptions account for all the information presented to voters then 'by definition, $D_i$ must be conditionally independent of potential outcomes', as printed.
Location: p. 278 (PDF p. 296), paragraph beginning 'The fact that random assignment is unlikely to hold'; the application's setting: pp. 276–278 (PDF pp. 294–296). -/
theorem complete_coding_not_ignorability_supporting : (∀ i : Fin 4, electorateOutcome 1 i-electorateOutcome 0 i=5) ∧
   fprob binaryJoint (fun i => electorateD i=1) = 1/2 ∧
   fprob binaryJoint (fun i => electorateU i=1 ∧ electorateD i=1) = 3/8 ∧
   fprob binaryJoint (fun i => electorateU i=1)*fprob binaryJoint (fun i => electorateD i=1) = 1/4 ∧
   fcond binaryJoint (fun i => electorateOutcome (electorateD i) i) electorateD 1 = 55 ∧
   fcond binaryJoint (fun i => electorateOutcome (electorateD i) i) electorateD 0 = 30 ∧
   (55-30 : ℝ) ≠ 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; simp only [electorateOutcome]; ring
  all_goals norm_num [fprob, fcond, binaryJoint, electorateU, electorateD,
    electorateOutcome, Fin.sum_univ_succ]

/-- If both potential outcomes are fixed functions of the description X alone, their pair is conditionally independent of treatment given X.
Target P001-T22: Section 7.5, the justification of ignorability in the application, corrected: conditional independence as an explicit substantive assumption; what follows from it.
Location: p. 278 (PDF p. 296), paragraph beginning 'The fact that random assignment is unlikely to hold'. -/
theorem description_only_outcomes_conditional_independence {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (D : Ω → ℝ) (hD : Measurable D) (m : E → ℝ → ℝ)
   (hm0 : Measurable (fun x => m x 0)) (hm1 : Measurable (fun x => m x 1)) :
   CI μ X hX (fun ω => (m (X ω) 0,m (X ω) 1)) D := by
  intro A B hA hB
  let U : Ω → ℝ := fun ω => if (m (X ω) 0,m (X ω) 1) ∈ A then 1 else 0
  let V : Ω → ℝ := fun ω => if D ω ∈ B then 1 else 0
  have hXm : Measurable[MeasurableSpace.comap X inferInstance] X :=
    measurable_iff_comap_le.mpr le_rfl
  have hPair : Measurable (fun ω => (m (X ω) 0,m (X ω) 1)) :=
    (hm0.prodMk hm1).comp hX
  have hPairm : Measurable[MeasurableSpace.comap X inferInstance]
      (fun ω => (m (X ω) 0,m (X ω) 1)) := (hm0.prodMk hm1).comp hXm
  have hUm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] U := by
    exact (measurable_const.piecewise (hA.preimage hPairm) measurable_const).stronglyMeasurable
  have hUi : Integrable U μ := by
    change Integrable ({ω | (m (X ω) 0,m (X ω) 1) ∈ A}.indicator (fun _ => (1 : ℝ))) μ
    exact (integrable_const 1).indicator (hA.preimage hPair)
  have hVi : Integrable V μ := by
    change Integrable ({ω | D ω ∈ B}.indicator (fun _ => (1 : ℝ))) μ
    exact (integrable_const 1).indicator (hB.preimage hD)
  have hUV : (fun ω => if (m (X ω) 0,m (X ω) 1) ∈ A ∧ D ω ∈ B then (1 : ℝ) else 0)=U*V := by
    funext ω
    dsimp [U,V]
    split_ifs <;> simp_all
  have hUVi : Integrable (U*V) μ := by
    rw [← hUV]
    refine ((integrable_const (1 : ℝ)).indicator
      ((hA.preimage hPair).inter (hB.preimage hD))).congr ?_
    filter_upwards [] with ω
    simp [Set.indicator, Set.mem_inter_iff]
  have hCEU : μ[U | MeasurableSpace.comap X inferInstance]=U :=
    condExp_of_stronglyMeasurable hX.comap_le hUm hUi
  rw [hUV]
  change μ[U*V | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
    (fun ω => μ[U | MeasurableSpace.comap X inferInstance] ω *
      μ[V | MeasurableSpace.comap X inferInstance] ω)
  rw [hCEU]
  exact condExp_mul_of_stronglyMeasurable_left hUm hUVi hVi

/-- If event A occurs only when event B occurs, then P(A)≤P(B).
Target P001-T23: Section 1.1.2, the gloss of monotonicity in the paragraph after the proof of Theorem 1.1.4, corrected; with Theorem 1.1.4 (Basic Properties of Probability) and Theorem 1.1.7 (Addition Rule).
Location: Gloss: p. 9 (PDF p. 27), first paragraph. Theorem 1.1.4: p. 8 (PDF p. 26). Theorem 1.1.7: p. 9 (PDF p. 27), proof on p. 10 (PDF p. 28). -/
theorem probability_monotonicity {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (A B : Set Ω) (hAB : A ⊆ B) :
   (∀ ω, ω ∈ A → ω ∈ B) ∧ prob μ A  ≤  prob μ B := by
  exact ⟨hAB, measureReal_mono hAB⟩

/-- Probability satisfies subtraction, empty-set, bounds, complement and addition rules.
Target P001-T23: Section 1.1.2, the gloss of monotonicity in the paragraph after the proof of Theorem 1.1.4, corrected; with Theorem 1.1.4 (Basic Properties of Probability) and Theorem 1.1.7 (Addition Rule).
Location: Gloss: p. 9 (PDF p. 27), first paragraph. Theorem 1.1.4: p. 8 (PDF p. 26). Theorem 1.1.7: p. 9 (PDF p. 27), proof on p. 10 (PDF p. 28). -/
theorem basic_probability_rules {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) :
   (A ⊆ B → prob μ (B \ A) = prob μ B-prob μ A) ∧ prob μ ∅ = 0 ∧
   (0  ≤  prob μ A ∧ prob μ A  ≤  1) ∧ prob μ Aᶜ = 1-prob μ A ∧
   prob μ (A ∪ B) = prob μ A+prob μ B-prob μ (A ∩ B) := by
  
  refine ⟨fun h => measureReal_sdiff h hA, ?_,
    ⟨ENNReal.toReal_nonneg,measureReal_le_one⟩, ?_, ?_⟩
  · simp [AronowAudit.P001.prob]
  · simpa [AronowAudit.P001.prob,Measure.real] using (measureReal_compl (μ := μ) hA)
  · have h := measureReal_union_add_inter (μ := μ) hB
    change μ.real (A∪B)=μ.real A+μ.real B-μ.real (A∩B)
    linarith


/-- The two events A and its complement are nonempty precisely when A is neither empty nor the whole sample space.
Target P001-T24: Theorem 1.1.13 (Law of Total Probability): the positivity condition in its proof and the partition remark after the proof, corrected.
Location: Theorem 1.1.13: p. 12 (PDF p. 30). Proof and the remark after it: p. 13 (PDF p. 31). Definition 1.1.12: p. 12 (PDF p. 30). Definition 1.1.8 and Theorem 1.1.9: p. 10 (PDF p. 28). -/
theorem two_event_partition_nonempty {Ω : Type*} (A : Set Ω) :
   A.Nonempty ∧ Aᶜ.Nonempty ↔ A ≠ ∅ ∧ A ≠ Set.univ := by
  simp [Set.nonempty_iff_ne_empty]

/-- An integer-valued constant zero random variable has P(X<4)=1 but mass sum at 1,2,3 equal to zero.
Target P001-T25: Section 1.2.2, the paragraph 'For a discrete random variable $X$, the PMF tells us everything about its distribution': first bulleted list, third bullet ($\Pr[X < 4] = \sum_{x=1}^{3} f(x)$ for an integer-valued $X$), as printed.
Location: p. 20 (PDF p. 38), first bulleted list, third bullet. -/
theorem integer_cdf_missing_zero_counterexample : fprob zeroAtom (fun _ => (0 : ℝ) < 4)=1 ∧
   (∑ k ∈ Finset.Icc (1 : ℤ) 3, fprob zeroAtom (fun _ => (0 : ℤ)=k))=0 ∧
   (1 : ℝ) ≠ 0 := by
  norm_num [fprob, zeroAtom, Fin.sum_univ_succ, Finset.sum_Icc_succ_top]

/-- For an integer-supported PMF, P(X<4) includes all integers through 3; the omitted mass is exactly P(X≤0).
Target P001-T26: Section 1.2.2, the paragraph 'For a discrete random variable $X$, the PMF tells us everything about its distribution': first bulleted list, third bullet, corrected.
Location: p. 20 (PDF p. 38), first bulleted list, third bullet. -/
theorem integer_lower_tail_correction (q : ℤ → ℝ) (hq : ∀ k, 0  ≤  q k) (hs : Summable q) (ht : (∑' k,q k)=1) :
   (∑' k : ℤ, if (k : ℝ) < 4 then q k else 0) = intMassCDF q 3 ∧
   intMassCDF q 3-(∑ k ∈ Finset.Icc (1 : ℤ) 3,q k) = intMassCDF q 0 ∧
   (intMassCDF q 3=(∑ k ∈ Finset.Icc (1 : ℤ) 3,q k) ↔ intMassCDF q 0=0) := by
  classical
  have hcast (k b : ℤ) : ((k:ℝ) ≤ (b:ℝ)) ↔ k ≤ b := by exact_mod_cast Iff.rfl
  have hfirst : (∑' k : ℤ, if (k:ℝ) < 4 then q k else 0) = intMassCDF q 3 := by
    unfold intMassCDF
    apply tsum_congr
    intro k
    have hc : ((k:ℝ) < 4) ↔ k < 4 := by exact_mod_cast (Iff.rfl : k < 4 ↔ k < 4)
    have hd : ((k:ℝ) ≤ 3) ↔ k ≤ 3 := by exact_mod_cast (Iff.rfl : k ≤ 3 ↔ k ≤ 3)
    simp only [hc,hd,show (k < 4) ↔ k ≤ 3 by omega]
  have hA : Summable (fun k : ℤ => if (k:ℝ) ≤ 0 then q k else 0) := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro k; split_ifs; exact hq k; exact le_rfl
    · intro k; split_ifs <;> simp_all
  have hB : Summable (fun k : ℤ => if k ∈ Finset.Icc (1:ℤ) 3 then q k else 0) := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro k; split_ifs; exact hq k; exact le_rfl
    · intro k; split_ifs <;> simp_all
  have he : (fun k : ℤ => if (k:ℝ) ≤ 3 then q k else 0) =
      fun k : ℤ => (if (k:ℝ) ≤ 0 then q k else 0)+(if k ∈ Finset.Icc (1:ℤ) 3 then q k else 0) := by
    funext k
    have hc : ((k:ℝ) ≤ 0) ↔ k ≤ 0 := by exact_mod_cast (Iff.rfl : k ≤ 0 ↔ k ≤ 0)
    have hd : ((k:ℝ) ≤ 3) ↔ k ≤ 3 := by exact_mod_cast (Iff.rfl : k ≤ 3 ↔ k ≤ 3)
    simp only [hc,hd,Finset.mem_Icc]
    split_ifs <;> simp_all <;> omega
  have hfinite : (∑' k : ℤ, if k ∈ Finset.Icc (1:ℤ) 3 then q k else 0)=
      ∑ k ∈ Finset.Icc (1:ℤ) 3,q k := by
    rw [tsum_eq_sum (s := Finset.Icc (1:ℤ) 3) (fun k hk => by simp [hk])]
    apply Finset.sum_congr rfl
    intro k hk
    simp [hk]
  have hdecomp : intMassCDF q 3=intMassCDF q 0+(∑ k ∈ Finset.Icc (1:ℤ) 3,q k) := by
    unfold intMassCDF
    rw [he,hA.tsum_add hB,hfinite]
  refine ⟨hfirst,by linarith,?_⟩
  constructor <;> intro h <;> linarith


/-- The CDF of a countable-range random variable is the sum of its point masses through x.
Target P001-T28: Example 1.2.13, first sentence, corrected: the CDF of a discrete random variable as a sum of jumps, and its step shape when the range is finite.
Location: p. 23 (PDF p. 41), Example 1.2.13, first sentence; the analogy on p. 116 (PDF p. 134). -/
theorem discrete_cdf_jump_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : Ω → ℝ) (hX : Measurable X) [Countable (Set.range X)] :
   ∀ x : ℝ, cdf μ X x = ∑' t : Set.range X,
     if t.val  ≤  x then prob μ {ω | X ω=t.val} else 0 := by
  classical
  intro x
  let A : Set.range X → Set Ω := fun t => {ω | X ω=t.val} ∩ {ω | t.val ≤ x}
  have hA (t : Set.range X) : MeasurableSet (A t) := by
    have hXt : MeasurableSet {ω | X ω=t.val} := (measurableSet_singleton t.val).preimage hX
    have hC : MeasurableSet {ω : Ω | t.val ≤ x} := by
      by_cases ht : t.val ≤ x <;> simp [ht]
    exact hXt.inter hC
  have hd : Pairwise (fun t u => Disjoint (A t) (A u)) := by
    intro t u htu
    apply Set.disjoint_left.2
    intro ω hωt hωu
    exact htu (Subtype.ext (hωt.1.symm.trans hωu.1))
  have hu : (⋃ t : Set.range X,A t)={ω | X ω ≤ x} := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_setOf_eq]
    constructor
    · rintro ⟨t,ht⟩
      exact ht.1.symm ▸ ht.2
    · intro hx
      exact ⟨⟨X ω,Set.mem_range_self ω⟩,rfl,hx⟩
  unfold cdf prob
  rw [← hu,measure_iUnion hd hA,ENNReal.tsum_toReal_eq (fun t => measure_ne_top μ (A t))]
  apply tsum_congr
  intro t
  by_cases ht : t.val ≤ x
  · simp [A,ht,prob]
  · simp [A,ht]

/-- The CDF is constant on any interval containing no possible observation value in its half-open increment.
Target P001-T28: Example 1.2.13, first sentence, corrected: the CDF of a discrete random variable as a sum of jumps, and its step shape when the range is finite.
Location: p. 23 (PDF p. 41), Example 1.2.13, first sentence; the analogy on p. 116 (PDF p. 134). -/
theorem finite_cdf_constant_between_values {n : ℕ} (P : FiniteLaw n) (X : Fin n → ℝ) (a b : ℝ)
   (hab : a  ≤  b) (hgap : ∀ i, ¬ (a < X i ∧ X i ≤ b)) :
   fprob P (fun i => X i ≤ a) = fprob P (fun i => X i ≤ b) := by
  unfold fprob
  apply Finset.sum_congr rfl
  intro i hi
  have hiff : X i ≤ a ↔ X i ≤ b := by
    constructor
    · intro h; linarith
    · intro h
      by_contra hn
      exact hgap i ⟨lt_of_not_ge hn,h⟩
  simp only [hiff]


theorem uniform_cdf_reflection (x : ℝ) : uniformCDF (1-x) = 1-uniformCDF x := by
  unfold uniformCDF
  by_cases h0 : x ≤ 0
  · have h1 : 1 ≤ 1-x := by linarith
    rw [min_eq_left h1,max_eq_right (by norm_num : (0:ℝ) ≤ 1),
      min_eq_right (h0.trans (by norm_num)),max_eq_left h0]
    ring
  · by_cases h1 : x ≤ 1
    · have hx : 0 ≤ 1-x := by linarith
      have hx1 : 1-x ≤ 1 := by linarith
      rw [min_eq_right hx1,max_eq_right hx,min_eq_right h1,max_eq_right (le_of_not_ge h0)]
    · have hx : 1-x ≤ 0 := by linarith
      rw [min_eq_right (hx.trans (by norm_num)),max_eq_left hx,min_eq_left (le_of_not_ge h1),
        max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
      ring

theorem uniform_cdf_not_differentiable_zero : ¬ DifferentiableAt ℝ uniformCDF 0 := by
  intro h
  have he : (fun x : ℝ => 2*uniformCDF x-x) =ᶠ[𝓝 0] abs := by
    filter_upwards [eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)] with x hx
    unfold uniformCDF
    rw [min_eq_right hx.le]
    by_cases h0 : 0 ≤ x
    · rw [max_eq_right h0,abs_of_nonneg h0]
      ring
    · rw [max_eq_left (le_of_not_ge h0),abs_of_neg (lt_of_not_ge h0)]
      ring
  exact not_differentiableAt_abs_zero
    (((h.const_mul 2).sub differentiableAt_id).congr_of_eventuallyEq he.symm)

theorem uniform_cdf_not_differentiable_one : ¬ DifferentiableAt ℝ uniformCDF 1 := by
  intro h
  have hs : DifferentiableAt ℝ (fun x : ℝ => uniformCDF (1-x)) 0 := by
    have hh0 : DifferentiableAt ℝ uniformCDF ((fun x : ℝ => 1-x) 0) := by
      simpa only [sub_zero] using h
    exact hh0.comp 0 (show DifferentiableAt ℝ (fun x : ℝ => 1-x) 0 from by fun_prop)
  have hs' : DifferentiableAt ℝ (fun x : ℝ => 1-uniformCDF x) 0 := by
    simpa only [uniform_cdf_reflection] using hs
  have hh := (differentiableAt_const (1:ℝ)).sub hs'
  apply uniform_cdf_not_differentiable_zero
  convert hh using 1
  funext x
  dsimp only [Pi.sub_apply]
  ring

theorem uniform_closed_integral_cdf (x : ℝ) :
    (∫ u in Set.Iic x, uniformClosedPDF u) = uniformCDF x := by
  have hi : uniformClosedPDF = (Set.Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) := by
    funext u
    simp [uniformClosedPDF,Set.indicator]
  rw [hi,integral_indicator measurableSet_Icc,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]
  rw [Measure.restrict_apply measurableSet_Icc]
  have hs : Set.Icc (0:ℝ) 1 ∩ Set.Iic x = Set.Icc 0 (min 1 x) := by
    ext u
    simp only [Set.mem_inter_iff,Set.mem_Icc,Set.mem_Iic,le_min_iff]
    tauto
  rw [hs,Real.volume_Icc]
  simp only [sub_zero,ENNReal.toReal_ofReal',uniformCDF,max_comm]

theorem centered_gaussian_half_mass (v : ℝ≥0) (hv : 0 < v) :
    prob (gaussianReal 0 v) (Set.Iic 0) = 1/2 := by
  haveI : NullSingletonClass (gaussianReal 0 v) := nullSingletonClass_gaussianReal hv.ne'
  have hmap : (gaussianReal 0 v).map (fun x : ℝ => -x) = gaussianReal 0 v := by
    simpa using (gaussianReal_map_neg (μ := (0:ℝ)) (v := v))
  have hreflect : gaussianReal 0 v (Set.Iic 0) = gaussianReal 0 v (Set.Ici 0) := by
    conv_lhs => rw [← hmap, Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1
    ext x
    simp
  have hatom : gaussianReal 0 v (Set.Ioi 0) = gaussianReal 0 v (Set.Ici 0) :=
    measure_congr (Ioi_ae_eq_Ici' (measure_singleton 0))
  have hc := measureReal_add_measureReal_compl (μ := gaussianReal 0 v)
    (s := Set.Iic 0) measurableSet_Iic
  simp only [Set.compl_Iic, measureReal_def, measure_univ, ENNReal.toReal_one, hatom,
    ← hreflect] at hc
  unfold prob
  linarith

/-- Three distinct nonnegative densities produce the same uniform CDF, which is not differentiable at 0 or 1.
Target P001-T29: The sentence after Definition 1.2.14 ('the PDF is unique') and Definition 1.2.15 ($f(x) = dF(u)/du|_{u=x}$, $\forall x \in \mathbb{R}$), as printed; with the proof step of Theorem 1.2.16 that uses the derivative at every $x$.
Location: p. 24 (PDF p. 42), sentence after Definition 1.2.14; p. 25 (PDF p. 43), Definition 1.2.15 and the proof of Theorem 1.2.16. Example 1.2.18: p. 28 (PDF p. 46). -/
theorem uniform_pdf_versions_counterexample : (∀ x : ℝ, (∫ u in Set.Iic x, uniformClosedPDF u)=uniformCDF x ∧
   (∫ u in Set.Iic x, uniformOpenPDF u)=uniformCDF x ∧
   (∫ u in Set.Iic x, uniformModifiedPDF u)=uniformCDF x) ∧
   uniformClosedPDF ≠ uniformOpenPDF ∧ uniformClosedPDF ≠ uniformModifiedPDF ∧
   uniformOpenPDF ≠ uniformModifiedPDF ∧
   ¬ DifferentiableAt ℝ uniformCDF 0 ∧ ¬ DifferentiableAt ℝ uniformCDF 1 := by
  have h0 : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by rw [ae_iff]; simp
  have h1 : ∀ᵐ u : ℝ ∂volume, u ≠ 1 := by rw [ae_iff]; simp
  have ht : ∀ᵐ u : ℝ ∂volume, u ≠ 1/3 := by rw [ae_iff]; simp
  have hopen : uniformOpenPDF =ᵐ[volume] uniformClosedPDF := by
    filter_upwards [h0,h1] with u hu0 hu1
    unfold uniformOpenPDF uniformClosedPDF
    have he : u∈Set.Ioo (0:ℝ) 1 ↔ u∈Set.Icc (0:ℝ) 1 := by
      simp only [Set.mem_Ioo,Set.mem_Icc]
      constructor
      · rintro ⟨ha,hb⟩; exact ⟨ha.le,hb.le⟩
      · rintro ⟨ha,hb⟩; exact ⟨lt_of_le_of_ne ha hu0.symm,lt_of_le_of_ne hb hu1⟩
    simp only [he]
  have hmod : uniformModifiedPDF =ᵐ[volume] uniformClosedPDF := by
    filter_upwards [ht] with u hu
    simp only [uniformModifiedPDF,if_neg hu]
  refine ⟨?_,?_,?_,?_,uniform_cdf_not_differentiable_zero,uniform_cdf_not_differentiable_one⟩
  · intro x
    refine ⟨uniform_closed_integral_cdf x,?_,?_⟩
    · rw [setIntegral_congr_ae measurableSet_Iic (hopen.mono (fun _ h _ => h))]
      exact uniform_closed_integral_cdf x
    · rw [setIntegral_congr_ae measurableSet_Iic (hmod.mono (fun _ h _ => h))]
      exact uniform_closed_integral_cdf x
  · intro he
    have h := congrFun he 0
    norm_num [uniformClosedPDF,uniformOpenPDF] at h
  · intro he
    have h := congrFun he (1/3)
    norm_num [uniformClosedPDF,uniformModifiedPDF] at h
  · intro he
    have h := congrFun he (1/3)
    norm_num [uniformOpenPDF,uniformModifiedPDF] at h

/-- Integral PDF versions are unique almost everywhere and equal the CDF derivative almost everywhere; at differentiability points the derivative is nonnegative.
Target P001-T30: Definition 1.2.15 and the uniqueness sentence before it, corrected: the PDF is unique up to Lebesgue-almost-everywhere equality and equals $F'$ almost everywhere; the joint analogue (Definition 1.3.11).
Location: p. 24 (PDF p. 42), sentence after Definition 1.2.14; p. 25 (PDF p. 43), Definition 1.2.15 and Theorem 1.2.16; p. 36 (PDF p. 54), Definitions 1.3.10 and 1.3.11; p. 38 (PDF p. 56), Definition 1.3.16; p. 39 (PDF p. 57), Theorem 1.3.17. -/
theorem pdf_unique_and_derivative_ae (ν : Measure ℝ) [IsProbabilityMeasure ν] (f g : ℝ → ℝ)
   (hf : HasPDF ν f) (hg : HasPDF ν g) :
   f =ᵐ[volume] g ∧ (∀ᵐ x ∂volume, HasDerivAt (fun t => prob ν (Set.Iic t)) (f x) x) ∧
   (∀ x, DifferentiableAt ℝ (fun t => prob ν (Set.Iic t)) x →
     0  ≤  deriv (fun t => prob ν (Set.Iic t)) x) ∧ (∫ x, f x)=1 := by
  have heq : f =ᵐ[volume] g := by
    have h := (withDensity_eq_iff_of_sigmaFinite hf.1.ennreal_ofReal
      hg.1.ennreal_ofReal).mp (hf.2.2.2.symm.trans hg.2.2.2)
    filter_upwards [h] with x hx
    exact (ENNReal.ofReal_eq_ofReal_iff (hf.2.1 x) (hg.2.1 x)).mp hx
  have hF (x : ℝ) : prob ν (Set.Iic x) = ∫ t in Set.Iic x, f t := by
    unfold prob
    rw [hf.2.2.2, withDensity_apply _ measurableSet_Iic,
      ← ofReal_integral_eq_lintegral_ofReal hf.2.2.1.integrableOn (ae_of_all _ hf.2.1)]
    exact ENNReal.toReal_ofReal (integral_nonneg hf.2.1)
  have hfun : (fun t => prob ν (Set.Iic t)) =
      fun t => (∫ u in Set.Iic 0, f u) + ∫ u in 0..t, f u := by
    funext t
    rw [hF]
    have hi := intervalIntegral.integral_Iic_sub_Iic (a := (0:ℝ)) (b := t)
      hf.2.2.1.integrableOn hf.2.2.1.integrableOn
    linarith
  refine ⟨heq, ?_, ?_, ?_⟩
  · filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hf.2.2.1.locallyIntegrable] with x hx
    rw [hfun]
    exact (hx 0).const_add _
  · intro x _
    have hm : Monotone (fun t => prob ν (Set.Iic t)) := by
      intro a b hab
      exact ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (Set.Iic_subset_Iic.mpr hab))
    exact hm.deriv_nonneg
  · have hi : ENNReal.ofReal (∫ x, f x) = 1 := by
      rw [ofReal_integral_eq_lintegral_ofReal hf.2.2.1 (ae_of_all _ hf.2.1)]
      have hm := congrArg (fun m : Measure ℝ => m Set.univ) hf.2.2.2
      simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ] using hm.symm
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hf.2.1) (by norm_num : (0:ℝ) ≤ 1)).mp
      (by simpa using hi)

/-- Joint PDF versions of the same joint law agree almost everywhere on R².
Target P001-T30: Definition 1.2.15 and the uniqueness sentence before it, corrected: the PDF is unique up to Lebesgue-almost-everywhere equality and equals $F'$ almost everywhere; the joint analogue (Definition 1.3.11).
Location: p. 24 (PDF p. 42), sentence after Definition 1.2.14; p. 25 (PDF p. 43), Definition 1.2.15 and Theorem 1.2.16; p. 36 (PDF p. 54), Definitions 1.3.10 and 1.3.11; p. 38 (PDF p. 56), Definition 1.3.16; p. 39 (PDF p. 57), Theorem 1.3.17. -/
theorem joint_pdf_unique_ae (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (f g : (ℝ × ℝ) → ℝ)
   (hf : HasJointPDF ν f) (hg : HasJointPDF ν g) : f =ᵐ[volume] g := by
  have h := (withDensity_eq_iff_of_sigmaFinite hf.1.ennreal_ofReal
    hg.1.ennreal_ofReal).mp (hf.2.2.2.symm.trans hg.2.2.2)
  filter_upwards [h] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (hf.2.1 x) (hg.2.1 x)).mp hx

/-- A real random variable with an integral density has no atoms and an uncountable range and sample space.
Target P001-T32: Section 1.2.4, the description of the range of a continuous random variable, corrected.
Location: p. 24 (PDF p. 42), paragraph before Definition 1.2.14. -/
theorem continuous_rv_range_uncountable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : Ω → ℝ) (hX : Measurable X) (f : ℝ → ℝ) (hf : HasPDF (μ.map X) f) :
   (∀ x : ℝ, μ {ω | X ω=x}=0) ∧ ¬ (Set.range X).Countable ∧ ¬ Countable Ω := by
  have hatom (x : ℝ) : μ {ω | X ω=x}=0 := by
    have hx : (μ.map X) {x} = 0 := by
      rw [hf.2.2.2]
      exact withDensity_absolutelyContinuous _ _ (measure_singleton x)
    simpa only [Measure.map_apply hX (measurableSet_singleton x), Set.preimage,
      Set.mem_singleton_iff] using hx
  have hrange : ¬ (Set.range X).Countable := by
    intro hcount
    have hz : μ (⋃ x : Set.range X, {ω | X ω = x.val}) = 0 := by
      have : Countable (Set.range X) := hcount.to_subtype
      exact measure_iUnion_null (fun x => hatom x.val)
    have he : (⋃ x : Set.range X, {ω | X ω = x.val}) = Set.univ := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨⟨X ω, ⟨ω, rfl⟩⟩, rfl⟩
    rw [he, measure_univ] at hz
    exact one_ne_zero hz
  refine ⟨hatom, hrange, ?_⟩
  intro hcount
  have : Countable Ω := hcount
  exact hrange (Set.countable_range X)



theorem joint_pdf_event_probability (ν : Measure (ℝ×ℝ)) (f : (ℝ×ℝ) → ℝ)
    (hf : HasJointPDF ν f) (A : Set (ℝ×ℝ)) (hA : MeasurableSet A) :
    prob ν A=∫ z in A,f z := by
  unfold prob
  rw [hf.2.2.2,withDensity_apply _ hA,
    ←ofReal_integral_eq_lintegral_ofReal hf.2.2.1.integrableOn (ae_of_all _ hf.2.1)]
  exact ENNReal.toReal_ofReal (integral_nonneg hf.2.1)

theorem triangular_region_integral (f : (ℝ×ℝ) → ℝ) (hf : Integrable f volume) :
    (∫ z in {z : ℝ×ℝ | 0≤z.1 ∧ z.1≤1 ∧ 0≤z.2 ∧ z.2≤z.1},f z)=
      ∫ x in Set.Icc (0 : ℝ) 1,∫ y in Set.Icc 0 x,f (x,y) := by
  let T : Set (ℝ×ℝ) := {z | 0≤z.1 ∧ z.1≤1 ∧ 0≤z.2 ∧ z.2≤z.1}
  have hT : MeasurableSet T := by
    exact (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
        ((measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_fst)))
  change (∫ z in T,f z)=_
  rw [←integral_indicator hT]
  change (∫ z,T.indicator f z ∂((volume : Measure ℝ).prod volume))=_
  rw [integral_prod _ (hf.indicator hT)]
  rw [←integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  by_cases hx : x∈Set.Icc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hx,←integral_indicator measurableSet_Icc]
    change (∫ y,T.indicator f (x,y))=(∫ y,(Set.Icc 0 x).indicator (fun y => f (x,y)) y)
    apply integral_congr_ae
    apply ae_of_all
    intro y
    simp [T,Set.indicator,hx.1,hx.2]
  · rw [Set.indicator_of_notMem hx]
    apply integral_eq_zero_of_ae
    apply ae_of_all
    intro y
    have hn : (x,y)∉T := by
      intro h
      exact hx ⟨h.1,h.2.1⟩
    simp [Set.indicator,hn]

/-- The normalized rectangle density places probability one in the printed event Y≤X with 0≤X≤1, but its printed iterated integral over 0≤Y≤X is zero.
Target P001-T34: The 'triangular region' display after Theorem 1.3.12, $\Pr[0 \le X \le 1, Y \le X] = \int_0^1\int_0^x f(x, y)dydx$, as printed.
Location: p. 37 (PDF p. 55), sentence and display after Theorem 1.3.12. -/
theorem triangular_event_counterexample : (∫ z : ℝ × ℝ, rectanglePDF z)=1 ∧
   (∫ z in {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ z.2 ≤ z.1}, rectanglePDF z)=1 ∧
   (∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc 0 x, rectanglePDF (x,y))=0 := by
  classical
  let S : Set (ℝ×ℝ) := Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 0
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hpdf : rectanglePDF=S.indicator (fun _ => (1 : ℝ)) := by
    funext z
    simp [rectanglePDF,S,Set.indicator]
  have htotal : (∫ z : ℝ×ℝ,rectanglePDF z)=1 := by
    rw [hpdf,integral_indicator hS,integral_const]
    simp only [measureReal_def,Measure.restrict_apply_univ]
    change (((volume : Measure ℝ).prod volume) S).toReal • (1 : ℝ)=1
    simp [S,Measure.prod_prod,Real.volume_Ioo]
  let A : Set (ℝ×ℝ) := {z | 0≤z.1 ∧ z.1≤1 ∧ z.2≤z.1}
  have hA : MeasurableSet A := by
    apply MeasurableSet.inter (measurableSet_le measurable_const measurable_fst)
    exact (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hSA : S⊆A := by
    intro z hz
    exact ⟨hz.1.1.le,hz.1.2.le,le_trans hz.2.2.le hz.1.1.le⟩
  have hrestrict : A.indicator rectanglePDF=rectanglePDF := by
    rw [hpdf]
    funext z
    by_cases hz : z∈S
    · simp [Set.indicator,hz,hSA hz]
    · simp [Set.indicator,hz]
  refine ⟨htotal,?_,?_⟩
  · change (∫ z in A,rectanglePDF z)=1
    rw [←integral_indicator hA,hrestrict]
    exact htotal
  · have hinner (x : ℝ) : (∫ y in Set.Icc 0 x,rectanglePDF (x,y))=0 := by
      calc
        _ = ∫ y in Set.Icc 0 x,(0 : ℝ) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro y hy
          simp [rectanglePDF,not_lt.mpr hy.1]
        _ = 0 := by simp
    simp_rw [hinner]
    simp

/-- The triangular iterated integral gives the event with 0≤Y≤X; the printed event also includes its negative-Y portion.
Target P001-T35: The 'triangular region' display after Theorem 1.3.12, corrected.
Location: p. 37 (PDF p. 55), sentence and display after Theorem 1.3.12. -/
theorem triangular_region_correction (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (f : (ℝ × ℝ) → ℝ)
   (hf : HasJointPDF ν f) :
   prob ν {z | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ z.1} =
     (∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc 0 x, f (x,y)) ∧
   prob ν {z | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ z.2 ≤ z.1} =
     (∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc 0 x, f (x,y)) +
     prob ν {z | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ z.2 < 0} := by
  let T : Set (ℝ×ℝ) := {z | 0≤z.1 ∧ z.1≤1 ∧ 0≤z.2 ∧ z.2≤z.1}
  let N : Set (ℝ×ℝ) := {z | 0≤z.1 ∧ z.1≤1 ∧ z.2<0}
  have hT : MeasurableSet T := by
    exact (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
        ((measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_fst)))
  have hN : MeasurableSet N := by
    exact (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
        (measurableSet_lt measurable_snd measurable_const))
  have htprob : prob ν T=∫ x in Set.Icc (0 : ℝ) 1,∫ y in Set.Icc 0 x,f (x,y) :=
    (joint_pdf_event_probability ν f hf T hT).trans (triangular_region_integral f hf.2.2.1)
  have hdis : Disjoint T N := by
    apply Set.disjoint_left.mpr
    intro z hz hn
    exact (not_lt.mpr hz.2.2.1) hn.2.2
  have hsplit : {z : ℝ×ℝ | 0≤z.1 ∧ z.1≤1 ∧ z.2≤z.1}=T∪N := by
    ext z
    constructor
    · intro hz
      by_cases hy : 0≤z.2
      · exact Or.inl ⟨hz.1,hz.2.1,hy,hz.2.2⟩
      · exact Or.inr ⟨hz.1,hz.2.1,lt_of_not_ge hy⟩
    · intro hz
      rcases hz with hz|hz
      · exact ⟨hz.1,hz.2.1,hz.2.2.2⟩
      · exact ⟨hz.1,hz.2.1,le_trans hz.2.2.le hz.1⟩
  refine ⟨htprob,?_⟩
  rw [hsplit]
  change (ν (T∪N)).toReal=_
  rw [measure_union hdis hN,ENNReal.toReal_add (measure_ne_top ν T) (measure_ne_top ν N)]
  exact congrArg (fun t => t+prob ν N) htprob


/-- Multiplying a standard normal variable by zero yields an atom at zero and cannot give a positive-variance normal law; the bivariate density denominator also vanishes at rho=±1.
Target P001-T38: The sentence after Theorem 2.1.21 ('any linear combination of any number of mutually independent normal random variables must itself be normal') and the parameter range of the bivariate normal PDF in footnote 13, as printed.
Location: p. 56 (PDF p. 74), sentence after Theorem 2.1.21; p. 66 (PDF p. 84), footnote 13. Definition 2.1.19: p. 55 (PDF p. 73). -/
theorem zero_normal_combination_counterexample : (gaussianReal 0 1).map (fun _ : ℝ => (0 : ℝ))=Measure.dirac 0 ∧
   (∀ (m : ℝ) (s : ℝ≥0), 0 < s → (gaussianReal 0 1).map (fun _ : ℝ => (0 : ℝ)) ≠ gaussianReal m s) ∧
   (1-(1 : ℝ)^2=0 ∧ 1-(-1 : ℝ)^2=0) := by
  
  have hm : (gaussianReal 0 1).map (fun _ : ℝ => (0 : ℝ))=Measure.dirac 0 := by
    simp [Measure.map_const]
  refine ⟨hm,?_,by norm_num⟩
  intro m s hs
  rw [hm]
  letI : NullSingletonClass (gaussianReal m s) := nullSingletonClass_gaussianReal hs.ne'
  intro he
  have hmass := congrArg (fun ν : Measure ℝ => ν {0}) he
  simpa using hmass

/-- A nontrivial finite linear combination of independent positive-variance normal variables is normal with the stated mean and strictly positive summed variance.
Target P001-T39: The implication drawn from Theorem 2.1.21 and the bivariate normal PDF of footnote 13, corrected.
Location: p. 56 (PDF p. 74), Theorem 2.1.21 and the sentence after it; p. 66 (PDF p. 84), footnote 13. -/
theorem nontrivial_independent_normal_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {n : ℕ} (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
   (hi : iIndepFun X μ) (m a : Fin n → ℝ) (v : Fin n → ℝ≥0)
   (hv : ∀ i, 0 < v i) (hlaw : ∀ i, μ.map (X i)=gaussianReal (m i) (v i))
   (hreal : ∃ i, a i≠0) (b : ℝ) :
   μ.map (fun ω => (∑ i,a i*X i ω)+b)=
     gaussianReal ((∑ i,a i*m i)+b) (∑ i, ⟨(a i)^2, sq_nonneg _⟩*v i) ∧
   0  <  ∑ i : Fin n, (a i)^2*(v i : ℝ) := by
  let Y : Fin n → Ω → ℝ := fun i ω => a i*X i ω
  let w : Fin n → ℝ≥0 := fun i => ⟨(a i)^2,sq_nonneg _⟩*v i
  have hY : ∀ i, Measurable (Y i) := fun i => (hX i).const_mul (a i)
  have hYi : iIndepFun Y μ := hi.comp (fun i x => a i*x) (fun i => by fun_prop)
  have hYlaw (i : Fin n) : HasLaw (Y i) (gaussianReal (a i*m i) (w i)) μ :=
    gaussianReal_const_mul (show HasLaw (X i) (gaussianReal (m i) (v i)) μ from ⟨(hX i).aemeasurable, hlaw i⟩) (a i)
  have hsum (s : Finset (Fin n)) :
      HasLaw (fun ω => ∑ i ∈ s, Y i ω)
        (gaussianReal (∑ i ∈ s,a i*m i) (∑ i ∈ s,w i)) μ := by
    induction s using Finset.induction with
    | empty =>
      refine ⟨by fun_prop, ?_⟩
      simp [gaussianReal_zero_var, Measure.map_const]
    | @insert i s hiS ih =>
      have hind : IndepFun (Y i) (fun ω => ∑ j ∈ s, Y j ω) μ := by
        have hfun : (∑ j ∈ s, Y j)=(fun ω => ∑ j ∈ s, Y j ω) := by
          funext ω
          simp
        have hh := (hYi.indepFun_finsetSum_of_notMem hY hiS).symm
        rw [hfun] at hh
        exact hh
      have hadd := gaussianReal_add_gaussianReal_of_indepFun hind (hYlaw i) ih
      refine ⟨by fun_prop, ?_⟩
      have hfun : (fun ω => ∑ j ∈ insert i s, Y j ω)=
          Y i+(fun ω => ∑ j ∈ s, Y j ω) := by
        funext ω
        simp only [Finset.sum_insert hiS, Pi.add_apply]
      rw [hfun]
      simpa only [Finset.sum_insert hiS] using hadd
  refine ⟨(gaussianReal_add_const (hsum Finset.univ) b).map_eq, ?_⟩
  obtain ⟨i, hai⟩ := hreal
  exact Finset.sum_pos' (fun j _ => mul_nonneg (sq_nonneg _) (v j).coe_nonneg)
    ⟨i, Finset.mem_univ _, mul_pos (sq_pos_of_ne_zero hai) (hv i)⟩

/-- The fair-coin MSE is c²−c+1/2, has unique minimum 1/4 at c=1/2, and the plotted endpoint values are twice the MSE.
Target P001-T40: Figure 2.1.1 (Minimum MSE Solution for a Fair Coin Flip): the vertical scale, corrected; with Theorem 2.1.23 (Alternative Formula for MSE), Theorem 2.1.24 (The Expected Value Minimizes MSE) and Example 2.1.25.
Location: Figure 2.1.1: p. 59 (PDF p. 77). Theorem 2.1.23: p. 57 (PDF p. 75). Theorem 2.1.24 and Example 2.1.25: p. 58 (PDF p. 76). -/
theorem coin_mse_scale_correction : (∀ c : ℝ, coinLoss c=c^2-c+1/2 ∧ 1/4 ≤ coinLoss c ∧
   (coinLoss c=1/4 ↔ c=1/2) ∧ 2*coinLoss c=(0-c)^2+(1-c)^2) ∧
   coinLoss (-2)=13/2 ∧ coinLoss 2=5/2 ∧ coinLoss (1/2)=1/4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    have hs := sq_nonneg (c-1/2)
    refine ⟨by unfold coinLoss; ring, ?_, ?_, by unfold coinLoss; ring⟩
    · unfold coinLoss; nlinarith
    · constructor
      · intro h
        have hz : (c-1/2)^2=0 := by unfold coinLoss at h; nlinarith
        have : c-1/2=0 := (sq_eq_zero_iff).mp hz
        linarith
      · intro h; rw [h]; norm_num [coinLoss]
  all_goals norm_num [coinLoss]

/-- The explicit three-point law has positive variances and correlations ±1, but no affine equality holds at every sample point.
Target P001-T41: Theorem 2.2.6 (Correlation and Linear Dependence), second and third bullets, as printed.
Location: p. 63 (PDF p. 81), Theorem 2.2.6. Definition 2.2.5: p. 62 (PDF p. 80). Definition 1.3.1: p. 31 (PDF p. 49). -/
theorem correlation_not_pointwise_dependence : fvar nullPointLaw ![0,1,0]=1/4 ∧ fvar nullPointLaw ![0,1,1]=1/4 ∧
   fvar nullPointLaw ![1,0,0]=1/4 ∧ fcov nullPointLaw ![0,1,0] ![0,1,1]=1/4 ∧
   fcov nullPointLaw ![0,1,0] ![1,0,0]= -1/4 ∧
   (¬ ∃ a b : ℝ, ∀ i : Fin 3, (![0,1,1] : Fin 3 → ℝ) i=a+b*(![0,1,0] : Fin 3 → ℝ) i) ∧
   (¬ ∃ a b : ℝ, ∀ i : Fin 3, (![1,0,0] : Fin 3 → ℝ) i=a-b*(![0,1,0] : Fin 3 → ℝ) i) := by
  
  refine ⟨by norm_num [fvar,fmean,nullPointLaw,Fin.sum_univ_succ],
    by norm_num [fvar,fmean,nullPointLaw,Fin.sum_univ_succ],
    by norm_num [fvar,fmean,nullPointLaw,Fin.sum_univ_succ],
    by norm_num [fcov,fmean,nullPointLaw,Fin.sum_univ_succ],
    by norm_num [fcov,fmean,nullPointLaw,Fin.sum_univ_succ], ?_, ?_⟩
  · rintro ⟨a0,b0,h⟩
    have h0 := h 0
    have h2 := h 2
    norm_num at h0 h2
    linarith
  · rintro ⟨a0,b0,h⟩
    have h0 := h 0
    have h2 := h 2
    norm_num at h0 h2
    linarith


theorem correlation_affine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω→ℝ) (hX : MemLp X 2 μ) (hvX : 0<var μ X) (a b : ℝ) (hb : b≠0)
    (hAE : Y =ᵐ[μ] (fun ω=>a+b*X ω)) : correlation μ X Y=b/|b|:=by
  have hsx : 0<Real.sqrt (var μ X):=Real.sqrt_pos.mpr hvX
  have hsq : (Real.sqrt (var μ X))^2=var μ X:=Real.sq_sqrt hvX.le
  have hvar : var μ Y=b^2*var μ X:=by
    rw [var,variance_congr hAE,variance_const_add (hX.const_mul b).aestronglyMeasurable a,variance_const_mul]
    rfl
  have hcov : covariance X Y μ=b*var μ X:=by
    have he : covariance X Y μ=covariance X (fun ω=>a+b*X ω) μ:=by
      unfold covariance
      rw [integral_congr_ae hAE]
      apply integral_congr_ae
      filter_upwards [hAE] with ω hω
      rw [hω]
    rw [he,covariance_const_add_right ((hX.const_mul b).integrable one_le_two) a,
      covariance_const_mul_right,covariance_self hX.aemeasurable]
    rfl
  have hsy : Real.sqrt (var μ Y)=|b| *Real.sqrt (var μ X):=by
    rw [hvar,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs]
  unfold correlation
  rw [hcov,hsy]
  nth_rw 1 [←hsq]
  field_simp [hsx.ne',abs_ne_zero.mpr hb]
  <;> ring

/-- With finite positive variances, correlation lies in [−1,1] and extreme correlations are equivalent to affine dependence almost surely with the corresponding sign.
Target P001-T42: Theorem 2.2.6 (Correlation and Linear Dependence), corrected: linear dependence almost surely.
Location: p. 63 (PDF p. 81), Theorem 2.2.6; the same qualification applies to the description of linear dependence on p. 62 (PDF p. 80) and to the last sentence of footnote 21, p. 78 (PDF p. 96). -/
theorem correlation_linear_dependence_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
   (hvX : 0 < var μ X) (hvY : 0 < var μ Y) :
   correlation μ X Y ∈ Set.Icc (-1) 1 ∧
   (correlation μ X Y=1 ↔ ∃ a b : ℝ, 0 < b ∧ Y =ᵐ[μ] (fun ω => a+b*X ω)) ∧
   (correlation μ X Y= -1 ↔ ∃ a b : ℝ, 0 < b ∧ Y =ᵐ[μ] (fun ω => a-b*X ω)) := by
  let sx:=Real.sqrt (var μ X)
  let sy:=Real.sqrt (var μ Y)
  let c:=sy/sx
  have hsx : 0<sx:=Real.sqrt_pos.mpr hvX
  have hsy : 0<sy:=Real.sqrt_pos.mpr hvY
  have hsx2 : sx^2=var μ X:=Real.sq_sqrt hvX.le
  have hsy2 : sy^2=var μ Y:=Real.sq_sqrt hvY.le
  have hc : 0<c:=div_pos hsy hsx
  have hmem : MemLp (fun ω=>c*X ω) 2 μ:=hX.const_mul c
  have hvc : variance (fun ω=>c*X ω) μ=var μ Y:=by
    rw [variance_const_mul]
    change c^2*var μ X=var μ Y
    rw [←hsx2,←hsy2]
    dsimp [c]
    field_simp
  have hcov : covariance Y (fun ω=>c*X ω) μ=var μ Y*correlation μ X Y:=by
    rw [covariance_const_mul_right,covariance_comm Y X]
    unfold correlation
    change c*covariance X Y μ=var μ Y*(covariance X Y μ/(sx*sy))
    rw [←hsy2]
    dsimp [c]
    field_simp
    <;> ring
  have hminus : variance (fun ω=>Y ω-c*X ω) μ=2*var μ Y*(1-correlation μ X Y):=by
    rw [variance_fun_sub hY hmem,hvc,hcov]
    change var μ Y-2*(var μ Y*correlation μ X Y)+var μ Y=_
    ring
  have hplus : variance (fun ω=>Y ω+c*X ω) μ=2*var μ Y*(1+correlation μ X Y):=by
    rw [variance_fun_add hY hmem,hvc,hcov]
    change var μ Y+2*(var μ Y*correlation μ X Y)+var μ Y=_
    ring
  have hbound : correlation μ X Y∈Set.Icc (-1) 1:=by
    have hm:=variance_nonneg (fun ω=>Y ω-c*X ω) μ
    have hp:=variance_nonneg (fun ω=>Y ω+c*X ω) μ
    rw [hminus] at hm
    rw [hplus] at hp
    constructor <;> nlinarith
  refine ⟨hbound,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro hρ
    have hz : variance (fun ω=>Y ω-c*X ω) μ=0:=by rw [hminus,hρ];ring
    have hae:=ae_eq_integral_of_variance_eq_zero (hY.sub hmem) hz
    refine ⟨∫ω,Y ω-c*X ω ∂μ,c,hc,?_⟩
    filter_upwards [hae] with ω hω
    change Y ω-c*X ω=(∫ω,Y ω-c*X ω ∂μ) at hω
    linarith
  · rintro ⟨a,b,hb,hAE⟩
    rw [correlation_affine μ X Y hX hvX a b hb.ne' hAE,abs_of_pos hb,div_self hb.ne']
  · intro hρ
    have hz : variance (fun ω=>Y ω+c*X ω) μ=0:=by rw [hplus,hρ];ring
    have hae:=ae_eq_integral_of_variance_eq_zero (hY.add hmem) hz
    refine ⟨∫ω,Y ω+c*X ω ∂μ,c,hc,?_⟩
    filter_upwards [hae] with ω hω
    change Y ω+c*X ω=(∫ω,Y ω+c*X ω ∂μ) at hω
    linarith
  · rintro ⟨a,b,hb,hAE⟩
    have hAE' : Y =ᵐ[μ] (fun ω=>a+(-b)*X ω):=by
      filter_upwards [hAE] with ω hω
      rw [hω]
      ring
    rw [correlation_affine μ X Y hX hvX a (-b) (neg_ne_zero.mpr hb.ne') hAE',abs_neg,abs_of_pos hb,
      neg_div,div_self hb.ne']

/-- For a random variable with finite second moment, its MSE about any constant equals variance plus squared mean error and is uniquely minimized at its mean.
Target P001-T40: Figure 2.1.1 (Minimum MSE Solution for a Fair Coin Flip): the vertical scale, corrected; with Theorem 2.1.23 (Alternative Formula for MSE), Theorem 2.1.24 (The Expected Value Minimizes MSE) and Example 2.1.25.
Location: Figure 2.1.1: p. 59 (PDF p. 77). Theorem 2.1.23: p. 57 (PDF p. 75). Theorem 2.1.24 and Example 2.1.25: p. 58 (PDF p. 76). -/
theorem mse_general_identity_and_unique_minimum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : Ω → ℝ) (h2 : MemLp X 2 μ) :
   (∀ c : ℝ,mse μ X c=var μ X+(mean μ X-c)^2) ∧
   (∀ c : ℝ,mse μ X (mean μ X) ≤ mse μ X c ∧
     (mse μ X c=mse μ X (mean μ X) ↔ c=mean μ X)) := by
  
  have hx : Integrable X μ := h2.integrable one_le_two
  have he (c : ℝ) : mse μ X c=var μ X+(mean μ X-c)^2 := by
    have hc : MemLp (fun ω => X ω-c) 2 μ := h2.sub (memLp_const c)
    have h := variance_eq_sub hc
    have hm : (∫ ω,X ω-c ∂μ)=mean μ X-c := by
      rw [integral_sub hx (integrable_const c)]
      simp [AronowAudit.P001.mean]
    have hv : variance (fun ω => X ω-c) μ=var μ X := by
      simpa [var,sub_eq_add_neg] using variance_add_const h2.aestronglyMeasurable (-c)
    rw [hm,hv] at h
    change var μ X=(∫ ω,(X ω-c)^2 ∂μ)-(mean μ X-c)^2 at h
    unfold mse
    linarith
  refine ⟨he, ?_⟩
  intro c
  rw [he,he]
  constructor
  · nlinarith [sq_nonneg (mean μ X-c)]
  · constructor
    · intro h
      nlinarith [sq_nonneg (mean μ X-c)]
    · intro h
      simp [h]


/-- The affine prediction risk equals its variance-covariance quadratic plus squared mean error. -/
theorem linearRisk_mean_covariance_form {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (a b : ℝ) :
    linearRisk μ X Y a b=var μ Y-2*b*covariance X Y μ+b^2*var μ X+
      (mean μ Y-a-b*mean μ X)^2 := by
  let R : Ω → ℝ := fun ω => Y ω-b*X ω
  have hBX : MemLp (fun ω => b*X ω) 2 μ := hX.const_mul b
  have hR : MemLp R 2 μ := hY.sub hBX
  have hYi : Integrable Y μ := hY.integrable one_le_two
  have hBXi : Integrable (fun ω => b*X ω) μ := hBX.integrable one_le_two
  have hmean : mean μ R=mean μ Y-b*mean μ X := by
    unfold mean R
    rw [integral_sub hYi hBXi, integral_const_mul]
  have hvar : var μ R=var μ Y-2*b*covariance X Y μ+b^2*var μ X := by
    unfold var R
    rw [variance_fun_sub hY hBX, variance_const_mul, covariance_const_mul_right,
      covariance_comm Y X]
    ring
  have he : linearRisk μ X Y a b=mse μ R a := by
    unfold linearRisk mse R
    congr 1
    funext ω
    ring
  rw [he, (mse_general_identity_and_unique_minimum μ R hR).1 a, hmean, hvar]
  ring

/-- The BLP risk has derivatives in the free arguments a,b; its normal equations uniquely give the covariance/variance slope and the mean-adjusted intercept, which uniquely minimize risk.
Target P001-T43: Theorem 2.2.21 (Best Linear Predictor) and the first-order conditions in its proof, with the derivatives taken in the free arguments $(a, b)$ and evaluated at $(\alpha, \beta)$; the two corollaries and Theorem 2.2.22.
Location: Theorem 2.2.21: p. 76 (PDF p. 94). Proof and footnote 19: pp. 77–78 (PDF pp. 95–96). Corollaries: p. 78 (PDF p. 96). Theorem 2.2.22: p. 79 (PDF p. 97). -/
theorem blp_corrected_derivatives_and_minimum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hv : 0 < var μ X) :
   (∀ a b : ℝ, HasDerivAt (fun t => linearRisk μ X Y t b)
     (-2*mean μ (fun ω => Y ω-a-b*X ω)) a ∧
     HasDerivAt (fun t => linearRisk μ X Y a t)
     (-2*mean μ (fun ω => (Y ω-a-b*X ω)*X ω)) b) ∧
   (∀ a b : ℝ, (mean μ (fun ω => Y ω-a-b*X ω)=0 ∧
     mean μ (fun ω => (Y ω-a-b*X ω)*X ω)=0) ↔
     a=blpIntercept μ X Y ∧ b=blpSlope μ X Y) ∧
   (∀ a b : ℝ, linearRisk μ X Y (blpIntercept μ X Y) (blpSlope μ X Y)  ≤  linearRisk μ X Y a b ∧
     (linearRisk μ X Y a b=linearRisk μ X Y (blpIntercept μ X Y) (blpSlope μ X Y) ↔
       a=blpIntercept μ X Y ∧ b=blpSlope μ X Y)) := by
  have hXi : Integrable X μ := hX.integrable one_le_two
  have hYi : Integrable Y μ := hY.integrable one_le_two
  have hMean (a b : ℝ) : mean μ (fun ω => Y ω-a-b*X ω)=mean μ Y-a-b*mean μ X := by
    have hYa : Integrable (fun ω => Y ω-a) μ := hYi.sub (integrable_const a)
    have hBX : Integrable (fun ω => b*X ω) μ := hXi.const_mul b
    unfold mean
    rw [integral_sub hYa hBX, integral_sub hYi (integrable_const a), integral_const_mul]
    simp
  have hCross (a b : ℝ) : mean μ (fun ω => (Y ω-a-b*X ω)*X ω)=
      covariance X Y μ-b*var μ X+mean μ X*(mean μ Y-a-b*mean μ X) := by
    have hYX : Integrable (fun ω => Y ω*X ω) μ := hY.integrable_mul hX
    have hAX : Integrable (fun ω => a*X ω) μ := hXi.const_mul a
    have hBXsq : Integrable (fun ω => b*(X ω)^2) μ := hX.integrable_sq.const_mul b
    have hfun : (fun ω => (Y ω-a-b*X ω)*X ω)=
        (fun ω => (Y ω*X ω-a*X ω)-b*(X ω)^2) := by funext ω; ring
    rw [hfun]
    unfold mean
    change (∫ ω, ((fun ω => Y ω*X ω)-(fun ω => a*X ω)) ω-(fun ω => b*(X ω)^2) ω ∂μ)=_
    rw [integral_sub (hYX.sub hAX) hBXsq]
    change (∫ ω, Y ω*X ω-a*X ω ∂μ)-(∫ ω,b*(X ω)^2 ∂μ)=_
    rw [integral_sub hYX hAX, integral_const_mul, integral_const_mul]
    change mean μ (fun ω => Y ω*X ω)-a*mean μ X-b*mean μ (fun ω => (X ω)^2)=_
    have hYXeq : mean μ (fun ω => Y ω*X ω)=covariance X Y μ+mean μ Y*mean μ X := by
      have hc := covariance_eq_sub hY hX
      rw [covariance_comm Y X] at hc
      change covariance X Y μ=mean μ (fun ω => Y ω*X ω)-mean μ Y*mean μ X at hc
      linarith
    have hXsq : mean μ (fun ω => (X ω)^2)=var μ X+(mean μ X)^2 := by
      have hc := variance_eq_sub hX
      change var μ X=mean μ (fun ω => (X ω)^2)-(mean μ X)^2 at hc
      linarith
    rw [hYXeq, hXsq]
    simp only [mean]
    ring
  have hGap (a b : ℝ) : linearRisk μ X Y a b=
      linearRisk μ X Y (blpIntercept μ X Y) (blpSlope μ X Y)+
        var μ X*(b-blpSlope μ X Y)^2+(mean μ Y-a-b*mean μ X)^2 := by
    rw [linearRisk_mean_covariance_form μ X Y hX hY,
      linearRisk_mean_covariance_form μ X Y hX hY]
    unfold blpIntercept blpSlope
    field_simp [hv.ne']
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    constructor
    · have hd := ((((hasDerivAt_const a (mean μ Y)).sub (hasDerivAt_id a)).sub_const
        (b*mean μ X)).pow 2).const_add (var μ Y-2*b*covariance X Y μ+b^2*var μ X)
      dsimp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq] at hd
      convert hd using 1
      · funext t
        rw [linearRisk_mean_covariance_form μ X Y hX hY]
      · rw [hMean]
        ring
    · have hl := ((hasDerivAt_id b).const_mul (-2*covariance X Y μ)).const_add (var μ Y)
      have hq := ((hasDerivAt_id b).pow 2).mul_const (var μ X)
      have hb := ((hasDerivAt_const b (mean μ Y-a)).sub
        ((hasDerivAt_id b).mul_const (mean μ X))).pow 2
      have hd := (hl.add hq).add hb
      dsimp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq] at hd
      convert hd using 1
      · funext t
        rw [linearRisk_mean_covariance_form μ X Y hX hY]
        dsimp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
        ring
      · rw [hCross]
        ring
  · intro a b
    constructor
    · rintro ⟨hM, hC⟩
      rw [hMean] at hM
      rw [hCross, hM, mul_zero, add_zero] at hC
      have hb : b=blpSlope μ X Y := by
        unfold blpSlope
        apply (eq_div_iff hv.ne').mpr
        linarith
      refine ⟨?_, hb⟩
      unfold blpIntercept
      rw [← hb]
      linarith
    · rintro ⟨rfl,rfl⟩
      rw [hMean, hCross]
      unfold blpIntercept blpSlope
      constructor <;> field_simp [hv.ne'] <;> ring
  · intro a b
    have hgap := hGap a b
    have hnb := mul_nonneg hv.le (sq_nonneg (b-blpSlope μ X Y))
    have hna := sq_nonneg (mean μ Y-a-b*mean μ X)
    refine ⟨by linarith, ?_⟩
    constructor
    · intro he
      have hbsq : (b-blpSlope μ X Y)^2=0 := by nlinarith
      have hb : b=blpSlope μ X Y := sub_eq_zero.mp (sq_eq_zero_iff.mp hbsq)
      have hasq : (mean μ Y-a-b*mean μ X)^2=0 := by nlinarith
      have ha := sq_eq_zero_iff.mp hasq
      refine ⟨?_, hb⟩
      unfold blpIntercept
      rw [← hb]
      linarith
    · rintro ⟨rfl,rfl⟩
      rfl

/-- In the symmetric sign law with Y=X and Var(X)=1, the distinct linear predictors X and X+1 both have Cov(X,g(X))=Cov(X,Y), and the latter has MSE one.
Target P001-T44: Footnote 21, first sentence ('the BLP is the only linear function that satisfies $\mathrm{Cov}[X, g(X)] = \mathrm{Cov}[X, Y]$'), as printed.
Location: p. 78 (PDF p. 96), footnote 21. Theorem 2.2.21: p. 76 (PDF p. 94). Example 2.2.23: pp. 79–81 (PDF pp. 97–99). -/
theorem covariance_does_not_fix_intercept : fvar signLaw ![-1,1]=1 ∧ fcov signLaw ![-1,1] ![-1,1]=1 ∧
   fcov signLaw ![-1,1] ![0,2]=1 ∧
   fmean signLaw (fun i => (( ![-1,1] : Fin 2 → ℝ) i-(![0,2] : Fin 2 → ℝ) i)^2)=1 ∧
   (![0,2] : Fin 2 → ℝ) ≠ ![-1,1] := by
  
  refine ⟨by norm_num [fvar,fmean,signLaw,Fin.sum_univ_succ],
    by norm_num [fcov,fmean,signLaw,Fin.sum_univ_succ],
    by norm_num [fcov,fmean,signLaw,Fin.sum_univ_succ],
    by norm_num [fmean,signLaw,Fin.sum_univ_succ], ?_⟩
  intro h
  have h0 := congrFun h 0
  norm_num at h0

/-- The covariance equation fixes only slope; adding the mean equation fixes the BLP intercept uniquely.
Target P001-T45: Footnote 21, first sentence, corrected: the BLP is characterized by the covariance equation together with the mean equation.
Location: p. 78 (PDF p. 96), footnote 21. -/
theorem blp_two_equation_characterization {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hv : 0 < var μ X)
   (a b : ℝ) :
   (covariance X (fun ω => a+b*X ω) μ=covariance X Y μ ↔ b=blpSlope μ X Y) ∧
   ((covariance X (fun ω => a+b*X ω) μ=covariance X Y μ ∧
     mean μ (fun ω => a+b*X ω)=mean μ Y) ↔ b=blpSlope μ X Y ∧ a=blpIntercept μ X Y) := by
  have hXi := hX.integrable one_le_two
  have hBX : Integrable (fun ω => b*X ω) μ := hXi.const_mul b
  have hcov : covariance X (fun ω => a+b*X ω) μ=b*var μ X := by
    rw [covariance_const_add_right hBX a, covariance_const_mul_right,
      covariance_self hX.aemeasurable]
    rfl
  have hmean : mean μ (fun ω => a+b*X ω)=a+b*mean μ X := by
    unfold mean
    rw [integral_add (integrable_const a) hBX, integral_const_mul]
    simp
  have hs : covariance X (fun ω => a+b*X ω) μ=covariance X Y μ ↔ b=blpSlope μ X Y := by
    rw [hcov]
    exact (eq_div_iff hv.ne').symm
  refine ⟨hs, ?_⟩
  constructor
  · rintro ⟨hc, hm⟩
    have hb := hs.mp hc
    refine ⟨hb, ?_⟩
    rw [hmean] at hm
    unfold blpIntercept
    rw [← hb]
    linarith
  · rintro ⟨hb, ha⟩
    refine ⟨hs.mpr hb, ?_⟩
    rw [hmean, ha, hb]
    unfold blpIntercept
    ring


/-- Independent integrable outcomes have a constant CEF, verified on every covariate event. -/
theorem independent_constant_cef {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hYi : Integrable Y μ)
    (hi : IndepFun X Y μ) : IsCEF μ X Y (fun _ => mean μ Y) := by
  refine ⟨measurable_const, hYi, integrable_const _, ?_⟩
  intro A hA
  have hpre : MeasurableSet[MeasurableSpace.comap X ‹MeasurableSpace E›] (X ⁻¹' A) :=
    ⟨A, hA, rfl⟩
  have hset := ((IndepFun_iff_Indep X Y μ).mp hi).setIntegral_eq_mul
    hX.comap_le hY.aemeasurable hpre aestronglyMeasurable_id
  simpa [mean, integral_const, smul_eq_mul] using hset


/-- For independent mean-zero noise, the CEF of g(X) plus the noise is g(X); evaluating it at a fixed covariate value uses that value.
Target P001-T68: Example 4.3.5 (Overfitting with a Nonlinear CEF), the CEF identity, corrected ($g(x)$ for $g(X)$).
Location: p. 163 (PDF p. 181), Example 4.3.5, first two sentences. -/
theorem additive_independent_noise_cef {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X W : Ω → ℝ) (hX : Measurable X) (hW : Measurable W)
   (hi : IndepFun X W μ) (hWi : Integrable W μ) (hW0 : mean μ W=0)
   (g : ℝ → ℝ) (hg : Measurable g) (hgi : Integrable (g ∘ X) μ) :
   IsCEF μ X (fun ω => g (X ω)+W ω) g := by
  have hc := independent_constant_cef μ X W hX hW hWi hi
  refine ⟨hg, hgi.add hWi, hgi, ?_⟩
  intro A hA
  have hiA : IntegrableOn (fun ω => g (X ω)) (X ⁻¹' A) μ := hgi.integrableOn
  rw [integral_add hiA hWi.integrableOn]
  have hz : (∫ ω in X ⁻¹' A, W ω ∂μ)=0 := by
    simpa [hW0] using hc.2.2.2 A hA
  rw [hz, add_zero]


/-- Every covariance-matrix entry uses its own two component indices; the matrix is symmetric, has variances on the diagonal, and the variance of the component sum is the sum of all entries.
Target P001-T48: Definition 2.3.1 (Covariance Matrix), the index quantifier, corrected; with Theorem 2.3.2 (Multivariate Variance Rule).
Location: p. 84 (PDF p. 102). -/
theorem multivariate_variance_rule {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K : ℕ} (X : Fin K → Ω → ℝ) (hX : ∀ k, MemLp (X k) 2 μ) :
   (∀ j k, covariance (X j) (X k) μ=covariance (X k) (X j) μ) ∧
   (∀ k, covariance (X k) (X k) μ=var μ (X k)) ∧
   var μ (fun ω => ∑ k,X k ω)=∑ j : Fin K, ∑ k : Fin K,covariance (X j) (X k) μ := by
  refine ⟨fun j k => covariance_comm (X j) (X k), fun k => covariance_self (hX k).aemeasurable, ?_⟩
  exact variance_fun_sum hX

/-- Replacing a single covariate coordinate by t changes the affine predictor by its slope times t minus the old coordinate.
Target P001-T49: Section 2.3, the two expansions of the multivariate BLP used to interpret $\beta_1$, corrected; with Definition 2.3.6 and Theorem 2.3.7 (Coefficients of the BLP Are Partial Derivatives).
Location: p. 87 (PDF p. 105), first paragraph and Theorem 2.3.7. Definition 2.3.6: p. 86 (PDF p. 104). -/
theorem linear_predictor_update_identity {K : ℕ} (b : Fin (K+1) → ℝ) (x : Fin K → ℝ) (k : Fin K) (t : ℝ) :
   linearPredictor b (Function.update x k t)=linearPredictor b x+b k.succ*(t-x k) := by
  have hs : (∑ j : Fin K,b j.succ*Function.update x k t j)=
      (∑ j : Fin K,b j.succ*x j)+b k.succ*(t-x k) := by
    calc
      _=∑ j : Fin K,(b j.succ*x j+if j=k then b k.succ*(t-x k) else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases he : j=k
        · subst j
          simp only [Function.update_self,ite_true]
          ring
        · simp [Function.update_of_ne he,he]
      _=_ := by rw [Finset.sum_add_distrib]; simp
  unfold linearPredictor
  rw [hs]
  ring

/-- Changing one coordinate by one changes an affine predictor by its corresponding slope; the intercept is its value at zero.
Target P001-T49: Section 2.3, the two expansions of the multivariate BLP used to interpret $\beta_1$, corrected; with Definition 2.3.6 and Theorem 2.3.7 (Coefficients of the BLP Are Partial Derivatives).
Location: p. 87 (PDF p. 105), first paragraph and Theorem 2.3.7. Definition 2.3.6: p. 86 (PDF p. 104). -/
theorem linear_predictor_coordinate_increment {K : ℕ} (b : Fin (K+1) → ℝ) (x : Fin K → ℝ) (k : Fin K) :
   linearPredictor b (Function.update x k (x k+1))-linearPredictor b x=b k.succ ∧
   linearPredictor b (fun _ => 0)=b 0 := by
  
  constructor
  · rw [linear_predictor_update_identity]
    ring
  · simp [linearPredictor]

/-- The variance functional subtracts squared mean from second moment.
Target P001-T50: Three misprinted displays, corrected: the variance in Example 3.1.3 (p. 94); the variance functional $T_{\mathrm{V}}(F)$ (p. 118, repeated in Example 3.3.5, p. 119); the last line of Example 3.3.4 (p. 119).
Location: (a) p. 94 (PDF p. 112), Example 3.1.3 (continued), second bullet. (b) p. 118 (PDF p. 136), display for $\mathrm{V}[X] = T_{\mathrm{V}}(F)$, last line; p. 119 (PDF p. 137), first display of Example 3.3.5. (c) p. 119 (PDF p. 137), Example 3.3.4, last line of the display. Definition 3.1.2 and Example 3.1.3: p. 93 (PDF p. 111). -/
theorem variance_functional_minus_sign {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : Ω → ℝ) (hX : MemLp X 2 μ) :
   var μ X=mean μ (fun ω => (X ω)^2)-(mean μ X)^2 := by
  exact variance_eq_sub hX


/-- Convergence in probability is equivalent to eventual within-epsilon probability at least p for every p in [0,1).
Target P001-T51: The verbal gloss of convergence in probability after Definition 3.2.6, corrected ($p \in [0, 1)$).
Location: p. 99 (PDF p. 117), paragraph after Definition 3.2.6, sentence beginning 'More specifically'. -/
theorem probability_convergence_eventual_levels {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ) (hZ : ∀ n, Measurable (Z n)) (c : ℝ) :
   CP μ Z c ↔ ∀ p : ℝ, 0 ≤ p → p < 1 → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
     ∀ n, N ≤ n → p ≤ prob μ {ω | |Z n ω-c| < ε} := by
  have hcomp (n : ℕ) (ε : ℝ) : prob μ {ω | ε ≤ |Z n ω-c|}=
      1-prob μ {ω | |Z n ω-c| < ε} := by
    have hs : MeasurableSet {ω | |Z n ω-c| < ε} :=
      by simpa only [Real.norm_eq_abs] using
        (measurableSet_lt (((hZ n).sub_const c).norm)
          (measurable_const : Measurable (fun _ : Ω => ε)))
    have he : {ω | ε ≤ |Z n ω-c|}={ω | |Z n ω-c| < ε}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq,Set.mem_compl_iff,not_lt]
    rw [he]
    exact probReal_compl_eq_one_sub hs
  simp only [CP,Real.dist_eq]
  constructor
  · intro h p hp hp1 ε hε
    have hevent := (tendsto_order.1 (h ε hε)).2 (1-p) (by linarith)
    rcases eventually_atTop.1 hevent with ⟨N,hN⟩
    refine ⟨N,?_⟩
    intro n hn
    have ht := hN n hn
    rw [hcomp] at ht
    linarith
  · intro h ε hε
    apply tendsto_order.2
    refine ⟨?_,?_⟩
    · intro a ha
      exact Eventually.of_forall (fun n => ha.trans_le ENNReal.toReal_nonneg)
    · intro b hb
      let p : ℝ := max 0 (1-b/2)
      have hp : 0 ≤ p := le_max_left _ _
      have hp1 : p < 1 := max_lt (by norm_num) (by linarith)
      rcases h p hp hp1 ε hε with ⟨N,hN⟩
      apply eventually_atTop.2
      refine ⟨N,?_⟩
      intro n hn
      rw [hcomp]
      have ht := hN n hn
      have hpbound : 1-b/2 ≤ p := le_max_right _ _
      linarith

/-- The expectation of the indicator of any measurable real set is its event probability.
Target P001-T52: Footnote 12 (the expectation of an indicator), with the domain of $D$ corrected; with Theorem 3.2.9 (Estimating the CDF), to whose statement it is attached.
Location: p. 102 (PDF p. 120), Theorem 3.2.9 and footnote 12. -/
theorem indicator_expectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : Ω → ℝ) (hX : Measurable X) (D : Set ℝ) (hD : MeasurableSet D) :
   mean μ (fun ω => if X ω∈D then (1 : ℝ) else 0)=prob μ (X ⁻¹' D) := by
  
  have hs : MeasurableSet (X ⁻¹' D) := hD.preimage hX
  have h := integral_indicator_const (μ := μ) (1 : ℝ) hs
  simpa [AronowAudit.P001.mean,AronowAudit.P001.prob,Set.indicator,Measure.real] using h

/-- The explicit geometric-tail PMF at powers of two has finite positive variance 7/18 but an infinite fourth moment.
Target P001-T53: Proof of Theorem 3.2.19, the step 'by the WLLN, $\overline{X^2} \xrightarrow{p} \mathrm{E}[X^2]$', as printed: an instance of the theorem's hypotheses to which the cited WLLN (Theorem 3.2.8) does not apply.
Location: Proof step: p. 107 (PDF p. 125). Theorem 3.2.19: p. 106 (PDF p. 124). Theorem 3.2.8: p. 100 (PDF p. 118). -/
theorem squares_missing_wlln_hypothesis : Summable heavyMomentMass ∧ (∑' k,heavyMomentMass k)=1 ∧
   Summable (fun k => (2 : ℝ)^k*heavyMomentMass k) ∧
   Summable (fun k => (2 : ℝ)^(2*k)*heavyMomentMass k) ∧
   (∑' k,(2 : ℝ)^k*heavyMomentMass k)=7/6 ∧
   (∑' k,(2 : ℝ)^(2*k)*heavyMomentMass k)=7/4 ∧
   (∑' k : ℕ, ENNReal.ofReal ((2 : ℝ)^(4*k)*heavyMomentMass k))=∞ ∧
   (7/4-(7/6)^2 : ℝ)=7/18 := by
  have h0 (k : ℕ) : heavyMomentMass k=(7/8 : ℝ)*(1/8 : ℝ)^k := by
    simp only [heavyMomentMass,pow_succ]
    ring
  have h1 (k : ℕ) : (2 : ℝ)^k*heavyMomentMass k=(7/8 : ℝ)*(1/4 : ℝ)^k := by
    rw [h0]
    calc
      _=(7/8 : ℝ)*((2 : ℝ)*(1/8))^k := by rw [mul_pow]; ring
      _=_ := by norm_num
  have h2 (k : ℕ) : (2 : ℝ)^(2*k)*heavyMomentMass k=(7/8 : ℝ)*(1/2 : ℝ)^k := by
    rw [h0,pow_mul]
    calc
      _=(7/8 : ℝ)*((2 : ℝ)^2*(1/8))^k := by rw [mul_pow]; ring
      _=_ := by norm_num
  have h4 (k : ℕ) : (2 : ℝ)^(4*k)*heavyMomentMass k=(7/8 : ℝ)*(2 : ℝ)^k := by
    rw [h0,pow_mul]
    calc
      _=(7/8 : ℝ)*((2 : ℝ)^4*(1/8))^k := by rw [mul_pow]; ring
      _=_ := by norm_num
  have hs0 : Summable heavyMomentMass := by
    change Summable (fun k => heavyMomentMass k)
    simp_rw [h0]
    exact (summable_geometric_of_abs_lt_one (by norm_num : |(1/8 : ℝ)|<1)).mul_left _
  have hs1 : Summable (fun k => (2 : ℝ)^k*heavyMomentMass k) := by
    simp_rw [h1]
    exact (summable_geometric_of_abs_lt_one (by norm_num : |(1/4 : ℝ)|<1)).mul_left _
  have hs2 : Summable (fun k => (2 : ℝ)^(2*k)*heavyMomentMass k) := by
    simp_rw [h2]
    exact (summable_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)|<1)).mul_left _
  refine ⟨hs0,?_,hs1,hs2,?_,?_,?_,by norm_num⟩
  · simp_rw [h0]
    rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (by norm_num : |(1/8 : ℝ)|<1)]
    norm_num
  · simp_rw [h1]
    rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (by norm_num : |(1/4 : ℝ)|<1)]
    norm_num
  · simp_rw [h2]
    rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)|<1)]
    norm_num
  · have hc : (∑' _ : ℕ, ENNReal.ofReal (7/8 : ℝ))=∞ :=
      ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)
    apply top_unique
    rw [← hc]
    apply ENNReal.tsum_le_tsum
    intro k
    rw [h4]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [(show (1 : ℝ)≤(2 : ℝ)^k from one_le_pow₀ (by norm_num))]

/-- Convergence in probability to a constant is preserved by a function continuous at that constant.
Target P001-T55: Definition 3.2.32 (Consistency of Sampling Variance and Standard Error Estimators) and footnote 23, with the estimator's hat restored in four places.
Location: pp. 113–114 (PDF pp. 131–132), Definition 3.2.32; footnote 23, p. 114 (PDF p. 132). -/
theorem probability_convergence_continuous_at {Ω E F : Type*} [MeasurableSpace Ω]
  [PseudoMetricSpace E] [PseudoMetricSpace F]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → E) (z : E)
  (f : E → F) (hZ : CP μ Z z) (hf : ContinuousAt f z) :
  CP μ (fun n ω => f (Z n ω)) (f z) := by
  intro ε hε
  rcases Metric.continuousAt_iff.mp hf ε hε with ⟨δ,hδ,hd⟩
  have hb (n : ℕ) : prob μ {ω | ε ≤ dist (f (Z n ω)) (f z)} ≤
      prob μ {ω | δ ≤ dist (Z n ω) z} := by
    refine measureReal_mono ?_ (measure_ne_top μ _)
    intro ω hω
    change ε ≤ dist (f (Z n ω)) (f z) at hω
    change δ ≤ dist (Z n ω) z
    by_contra h
    have hg := hd (lt_of_not_ge h)
    linarith
  exact squeeze_zero (fun n => ENNReal.toReal_nonneg) hb (hZ δ hδ)

/-- A nonnegative sampling-variance estimator is consistent exactly when its square-root standard-error estimator is consistent.
Target P001-T55: Definition 3.2.32 (Consistency of Sampling Variance and Standard Error Estimators) and footnote 23, with the estimator's hat restored in four places.
Location: pp. 113–114 (PDF pp. 131–132), Definition 3.2.32; footnote 23, p. 114 (PDF p. 132). -/
theorem variance_se_consistency_equivalence {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (vhat : ℕ → Ω → ℝ) (hvhat : ∀ n ω, 0 ≤ vhat n ω) (v : ℝ) (hv : 0 ≤ v) :
   VarianceConsistent μ vhat v ↔ SEConsistent μ vhat v := by
  constructor
  · intro h
    have hs := probability_convergence_continuous_at μ
      (fun n ω => (n : ℝ)*vhat n ω) v Real.sqrt h Real.continuous_sqrt.continuousAt
    simpa only [SEConsistent,Real.sqrt_mul (Nat.cast_nonneg _)] using hs
  · intro h
    have hs := probability_convergence_continuous_at μ
      (fun n ω => Real.sqrt n*Real.sqrt (vhat n ω)) (Real.sqrt v)
      (fun t : ℝ => t^2) h (by fun_prop)
    have he (n : ℕ) (ω : Ω) :
        (Real.sqrt n*Real.sqrt (vhat n ω))^2=(n : ℝ)*vhat n ω := by
      rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n),Real.sq_sqrt (hvhat n ω)]
    simpa only [VarianceConsistent,he,Real.sq_sqrt hv] using hs

/-- The constant functional T(G)=7 has exactly zero centered root-n statistics, which cannot converge in distribution to any positive-variance normal law.
Target P001-T56: Theorem 3.3.6 (Asymptotic Normality of Plug-In Estimators), as printed, read with footnote 31 and Definition 3.2.28.
Location: p. 120 (PDF p. 138), Theorem 3.3.6 and footnote 31. Definition 3.2.28: p. 112 (PDF p. 130). -/
theorem constant_plugin_degenerate {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
   (∀ n : ℕ, ∀ ω : Ω, Real.sqrt n*((7 : ℝ)-7)=0) ∧
   ∀ v : ℝ≥0, 0 < v → ¬ CD μ (fun _ _ => (0 : ℝ)) (gaussianReal 0 v) := by
  refine ⟨by simp,?_⟩
  intro v hv hCD
  haveI : NullSingletonClass (gaussianReal 0 v) := nullSingletonClass_gaussianReal hv.ne'
  have hcont : ContinuousAt (fun t => prob (gaussianReal 0 v) (Set.Iic t)) 0 := by
    simpa only [prob, ← measureReal_def, ← cdf_eq_real] using
      P053.NormalCompletion.cdf_continuousAt (gaussianReal 0 v) 0
  have hlim := hCD 0 hcont
  have he : cdf μ (fun _ : Ω => (0:ℝ)) 0 = 1 := by
    simp [cdf,prob]
  simp only [he,centered_gaussian_half_mass v hv] at hlim
  have hbad : (1:ℝ) = 1/2 := tendsto_nhds_unique tendsto_const_nhds hlim
  norm_num at hbad

/-- The admitted even signed kernel integrates to one, but with one observation its integrated density at a−1 equals −1/2.
Target P001-T58: Definition 3.3.9 (Kernel Plug-In Estimator) with the kernels admitted by Definition 3.3.7, as printed: a signed kernel for which $\hat F_K$ is not a CDF.
Location: Definition 3.3.7: p. 121 (PDF p. 139). Definition 3.3.9: p. 123 (PDF p. 141). Definition 3.3.2: p. 118 (PDF p. 136). -/
theorem signed_kernel_not_cdf : (∀ t : ℝ, signedKernel t=signedKernel (-t)) ∧ Integrable signedKernel volume ∧
   (∫ t, signedKernel t)=1 ∧ ∀ a : ℝ,
     kernelCDF signedKernel 1 (fun _ : Fin 1 => a) (a-1)= -1/2 := by
  refine ⟨fun t => by simp [signedKernel,abs_neg],signed_kernel_integrals.1,
    signed_kernel_integrals.2.1,?_⟩
  intro a
  have hh := integral_affine_iic signedKernel a 1 (a-1) (by norm_num)
  have he : (a-1-a)/(1:ℝ)= -1 := by ring
  rw [he] at hh
  simpa [kernelCDF,kernelDensity] using hh.trans (by simpa using signed_kernel_integrals.2.2)

/-- An integrable even kernel with nonnegative a.e. values and integral one yields a nonnegative normalized density and a continuous monotone CDF with limits zero and one.
Target P001-T59: Definition 3.3.9 (Kernel Plug-In Estimator), corrected: a non-negative kernel.
Location: p. 123 (PDF p. 141), Definition 3.3.9; Definition 3.3.7, p. 121 (PDF p. 139). -/
theorem nonnegative_kernel_cdf {n : ℕ} (hn : 0 < n) (X : Fin n → ℝ) (K : ℝ → ℝ) (hK : Integrable K volume)
   (hpos : ∀ᵐ t ∂volume, 0 ≤ K t) (hnorm : (∫ t,K t)=1)
   (heven : ∀ t,K t=K (-t)) (h : ℝ) (hh : 0 < h) :
   (∀ᵐ x ∂volume, 0 ≤ kernelDensity K h X x) ∧
   (∫ x,kernelDensity K h X x)=1 ∧ Monotone (kernelCDF K h X) ∧
   Continuous (kernelCDF K h X) ∧ Tendsto (kernelCDF K h X) atBot (nhds 0) ∧
   Tendsto (kernelCDF K h X) atTop (nhds 1) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hi (i : Fin n) : Integrable (fun u => K ((u-X i)/h)/h) volume :=
    ((hK.comp_div hh.ne').comp_sub_right (X i)).div_const h
  have hki : Integrable (kernelDensity K h X) volume :=
    (integrable_finsetSum _ (fun i _ => hi i)).div_const (n:ℝ)
  have hkn : ∀ᵐ x ∂volume,0≤kernelDensity K h X x := by
    have hs (i : Fin n) : ∀ᵐ x ∂volume,0≤K ((x-X i)/h) := by
      have hq : Measure.QuasiMeasurePreserving (fun x : ℝ => (x-X i)/h) volume volume := by
        have hqs := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ)
          (inv_ne_zero hh.ne')
        have hqt := (measurePreserving_sub_right (volume : Measure ℝ) (X i)).quasiMeasurePreserving
        simpa only [Function.comp_def,smul_eq_mul,div_eq_inv_mul] using hqs.comp hqt
      exact hq.ae hpos
    filter_upwards [ae_all_iff.2 hs] with x hx
    exact div_nonneg (Finset.sum_nonneg (fun i _ => div_nonneg (hx i) hh.le)) hnR.le
  have hknorm : (∫ x,kernelDensity K h X x)=1 := by
    unfold kernelDensity
    rw [integral_div,integral_finsetSum _ (fun i _ => hi i)]
    have hv (i : Fin n) : (∫ x,K ((x-X i)/h)/h)=(1:ℝ) := by
      rw [integral_div,integral_sub_right_eq_self (fun u => K (u/h)) (X i),
        Measure.integral_comp_div,abs_of_pos hh,smul_eq_mul,hnorm]
      field_simp [hh.ne']
    simp only [hv,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    exact div_self hnR.ne'
  exact ⟨hkn,hknorm,integrable_density_cdf_properties _ hki hkn hknorm⟩

/-- Integrating the actual kernel density estimator gives the average of shifted kernel CDFs.
Target P001-T60: Definition 3.3.9 (Kernel Plug-In Estimator), last line: the integrand, corrected to the kernel density estimator $\hat f_K$.
Location: p. 123 (PDF p. 141), Definition 3.3.9, last line. -/
theorem kernel_cdf_correct_integrand {n : ℕ} (hn : 0 < n) (X : Fin n → ℝ) (K : ℝ → ℝ) (hK : Integrable K volume)
   (h : ℝ) (hh : 0 < h) (x : ℝ) :
   kernelCDF K h X x=(∑ i,∫ t in Set.Iic ((x-X i)/h),K t)/(n : ℝ) := by
  have hi (i : Fin n) : Integrable (fun u => K ((u-X i)/h)/h) volume :=
    ((hK.comp_div hh.ne').comp_sub_right (X i)).div_const h
  unfold kernelCDF kernelDensity
  rw [integral_div,integral_finsetSum _ (fun i _ => (hi i).integrableOn)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hmem
  rw [integral_div,integral_affine_iic K (X i) h x hh]
  field_simp [hh.ne']


/-- For every positive sample size, the iid sample mean is unbiased and its variance is population variance divided by n.
Target P001-T108: Theorem 3.2.3 (The Expected Value of the Sample Mean Is the Population Mean), Theorem 3.2.4 (Sampling Variance of the Sample Mean) and Theorem 3.2.5 (Chebyshev's Inequality for the Sample Mean).
Location: Theorem 3.2.3: p. 97 (PDF p. 115). Theorems 3.2.4 and 3.2.5: p. 98 (PDF p. 116), proof of 3.2.5 continuing on p. 99 (PDF p. 117). -/
theorem iid_sample_mean_finite_moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ) (n : ℕ) (hn : 0 < n) :
   mean μ (sampleMean X n)=mean μ (X 0) ∧ var μ (sampleMean X n)=var μ (X 0)/(n : ℝ) := by
  
  have hi2 : ∀ i, MemLp (X i) 2 μ := fun i => (hiid.2.2 i).symm.memLp_snd h2
  have hiint : ∀ i, Integrable (X i) μ := fun i => (hi2 i).integrable one_le_two
  have hEi : ∀ i, (∫ ω,X i ω ∂μ)=(∫ ω,X 0 ω ∂μ) := fun i => (hiid.2.2 i).integral_eq
  have hVi : ∀ i, variance (X i) μ=variance (X 0) μ := fun i => (hiid.2.2 i).variance_eq
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  have hsm : sampleMean X n=(fun ω => (n : ℝ)⁻¹*(∑ i∈Finset.range n,X i ω)) := by
    funext ω
    simp [sampleMean, div_eq_mul_inv, mul_comm]
  constructor
  · rw [hsm]
    unfold mean
    rw [integral_const_mul, integral_finsetSum (Finset.range n) (fun i _ => hiint i)]
    simp only [hEi, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [hn0]
  · unfold var
    rw [hsm, variance_const_mul]
    have hs : (fun ω => ∑ i∈Finset.range n,X i ω)=(∑ i∈Finset.range n,X i) := by
      funext ω
      simp
    rw [hs, IndepFun.variance_sum (fun i _ => hi2 i) (fun i hi j hj hij => hiid.2.1.indepFun hij)]
    simp only [hVi, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [hn0]

/-- The cluster sample mean is the mean of iid cluster averages, is unbiased for E[W], has variance Var(W)/l, and converges in probability to E[W].
Target P001-T63: Section 3.5.1, the sentence before Theorem 3.5.6 (mean of the cluster averages), corrected; with Theorems 3.5.3, 3.5.4, 3.5.5 and 3.5.6 for the cluster sample mean.
Location: Sentence: p. 138 (PDF p. 156). Definitions 3.5.1, 3.5.2: p. 136 (PDF p. 154). Theorems 3.5.3–3.5.5: p. 137 (PDF p. 155). Theorem 3.5.6: p. 138 (PDF p. 156). -/
theorem cluster_mean_properties {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {m : ℕ} (hm : 0 < m) (X : ℕ → Ω → Fin m → ℝ) (hiid : IID μ X)
   (h2 : ∀ j, MemLp (fun ω => X 0 ω j) 2 μ) :
   (∀ l, 0 < l → clusterMean X l=sampleMean (clusterAverage X) l ∧
     mean μ (clusterMean X l)=mean μ (clusterAverage X 0) ∧
     var μ (clusterMean X l)=var μ (clusterAverage X 0)/(l : ℝ)) ∧
   mean μ (clusterAverage X 0)=(∑ j,mean μ (fun ω => X 0 ω j))/(m : ℝ) ∧
   CP μ (clusterMean X) (mean μ (clusterAverage X 0)) := by
  let g : (Fin m → ℝ) → ℝ := fun x => (∑ j, x j)/(m : ℝ)
  have hg : Measurable g := by unfold g; fun_prop
  have hW : IID μ (clusterAverage X) := by
    refine ⟨fun i => hg.comp (hiid.1 i), ?_, fun i => (hiid.2.2 i).comp hg⟩
    exact hiid.2.1.comp (fun _ => g) (fun _ => hg)
  have hW2 : MemLp (clusterAverage X 0) 2 μ := by
    change MemLp (fun ω => (∑ j, X 0 ω j)/(m : ℝ)) 2 μ
    have hs : MemLp (fun ω => ∑ j, X 0 ω j) 2 μ :=
      memLp_finsetSum Finset.univ (fun j _ => h2 j)
    simpa only [div_eq_mul_inv, mul_comm] using hs.const_mul ((m : ℝ)⁻¹)
  have heq (l : ℕ) : clusterMean X l=sampleMean (clusterAverage X) l := by
    funext ω
    simp [clusterMean, sampleMean, clusterAverage, ← Finset.sum_div, div_div, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · intro l hl
    rw [heq]
    exact ⟨rfl, iid_sample_mean_finite_moments μ (clusterAverage X) hW hW2 l hl⟩
  · unfold mean clusterAverage
    rw [integral_div, integral_finsetSum Finset.univ (fun j _ => (h2 j).integrable one_le_two)]
  · have hlim := strong_law_ae_real (clusterAverage X) (hW2.integrable one_le_two)
      (fun i j hij => hW.2.1.indepFun hij) hW.2.2
    have hWm : ∀ i, Measurable (clusterAverage X i) := hW.1
    have hmW : ∀ l, Measurable (sampleMean (clusterAverage X) l) := by
      intro l
      unfold sampleMean
      fun_prop
    have hmeasure := tendstoInMeasure_of_tendsto_ae
      (fun l => (hmW l).aestronglyMeasurable) hlim
    intro ε hε
    simpa only [heq, mean, sampleMean, prob, Measure.real] using
      (tendstoInMeasure_iff_measureReal_dist.mp hmeasure) ε hε

/-- With diagonal variance σ² and off-diagonal covariance rho*σ², the double covariance sum gives the usual design-effect variance, including rho=0 and rho=1.
Target P001-T64: Example 3.5.8 (Consequences of Clustering for the Sample Mean), the common-correlation condition, corrected to pairs $j \ne j'$; and step 1 of the block bootstrap, corrected to $l$ clusters.
Location: Example 3.5.8: pp. 140–141 (PDF pp. 158–159). Block bootstrap steps: p. 141 (PDF p. 159). Theorem 3.5.5: p. 137 (PDF p. 155). -/
theorem intracluster_variance_correct_diagonal (l m : ℕ) (hl : 0 < l) (hm : 0 < m) (s ρ : ℝ)
   (C : Fin m → Fin m → ℝ) (hdiag : ∀ j,C j j=s)
   (hoff : ∀ j k,j≠k → C j k=ρ*s) :
   (∑ j,∑ k,C j k)/((l : ℝ)*(m : ℝ)^2)=
     s/((l : ℝ)*m)*(1+ρ*((m : ℝ)-1)) := by
  
  have he (j k : Fin m) : C j k=ρ*s+(if k=j then s-ρ*s else 0) := by
    by_cases hk : k=j
    · subst k; rw [hdiag]; simp
    · rw [hoff j k (Ne.symm hk)]
      simp [hk]
  have hl0 : (l : ℝ)≠0 := by exact_mod_cast hl.ne'
  have hm0 : (m : ℝ)≠0 := by exact_mod_cast hm.ne'
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hl0,hm0]
  <;> ring

/-- With invertible XᵀX, the OLS formula uniquely minimizes the correctly indexed squared residuals and makes Xᵀe zero, including the intercept residual sum.
Target P001-T65: Theorem 4.1.4 (OLS Solution in Matrix Algebra), with the last row of the stacked residual system in its proof corrected ($Y_n$ for $Y_3$); and Theorem 4.1.5 (Properties of Residuals from the OLS Regression Estimator).
Location: Theorem 4.1.4 and the stacked system: p. 148 (PDF p. 166); rest of the proof and Theorem 4.1.5: p. 149 (PDF p. 167); proof of 4.1.5: p. 150 (PDF p. 168). Definition 4.1.2: pp. 146–147 (PDF pp. 164–165). Definition 4.1.3: p. 148. -/
theorem ols_correct_rows_solution_residuals {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ)
   (hX : IsUnit (X.transpose*X).det) (hinter : ∀ i,X i 0=1) :
   (∀ b, olsRSS X Y (olsCoef X Y)  ≤  olsRSS X Y b ∧
     (olsRSS X Y b=olsRSS X Y (olsCoef X Y) ↔ b=olsCoef X Y)) ∧
   X.transpose.mulVec (Y-X.mulVec (olsCoef X Y))=0 ∧
   ∑ i,(Y-X.mulVec (olsCoef X Y)) i=0 := by
  let β := olsCoef X Y
  let e := Y-X.mulVec β
  have hnormal : X.transpose.mulVec e=0 := by
    change X.transpose.mulVec (Y-X.mulVec ((X.transpose*X)⁻¹.mulVec (X.transpose.mulVec Y)))=0
    rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hX,Matrix.one_mulVec,sub_self]
  have hinj : Function.Injective X.mulVec := by
    intro a b hab
    have h := congrArg X.transpose.mulVec hab
    simp only [Matrix.mulVec_mulVec] at h
    exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hX) h
  have hcross (d : Fin (K+1) → ℝ) : (∑ i,e i*(X.mulVec d) i)=0 := by
    change dotProduct e (X.mulVec d)=0
    rw [Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,hnormal,zero_dotProduct]
  have hgap (b : Fin (K+1) → ℝ) :
      olsRSS X Y b=olsRSS X Y β+∑ i,((X.mulVec (b-β)) i)^2 := by
    have hres (i : Fin n) : Y i-(X.mulVec b) i=e i-(X.mulVec (b-β)) i := by
      rw [Matrix.mulVec_sub]
      dsimp [e]
      ring
    calc
      olsRSS X Y b=∑ i,((e i)^2-2*(e i*(X.mulVec (b-β)) i)+((X.mulVec (b-β)) i)^2) := by
        unfold olsRSS
        apply Finset.sum_congr rfl
        intro i hi
        rw [hres]
        ring
      _=olsRSS X Y β-2*(∑ i,e i*(X.mulVec (b-β)) i)+∑ i,((X.mulVec (b-β)) i)^2 := by
        simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
        rfl
      _=olsRSS X Y β+∑ i,((X.mulVec (b-β)) i)^2 := by rw [hcross]; ring
  refine ⟨?_,hnormal,?_⟩
  · intro b
    have hn : 0 ≤ ∑ i,((X.mulVec (b-β)) i)^2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
    have hmin : olsRSS X Y β ≤ olsRSS X Y b := by
      rw [hgap b]
      exact le_add_of_nonneg_right hn
    refine ⟨hmin,?_⟩
    constructor
    · intro heq
      have hzsum : (∑ i,((X.mulVec (b-β)) i)^2)=0 := by linarith [hgap b]
      have hz : X.mulVec (b-β)=0 := by
        funext i
        apply sq_eq_zero_iff.mp
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => sq_nonneg _)).mp hzsum i (Finset.mem_univ i)
      apply hinj
      exact sub_eq_zero.mp (by rw [← Matrix.mulVec_sub,hz])
    · rintro rfl
      rfl
  · have hc := congrFun hnormal 0
    change (∑ i,X i 0*e i)=0 at hc
    simpa only [hinter,one_mul] using hc

/-- For every coefficient including the intercept, its robust and classical standard errors are the square roots of its own covariance diagonal entry.
Target P001-T66: The standard error estimator for an OLS coefficient as the square root of a diagonal element of the estimated covariance matrix: the ordinal, corrected (robust, p. 153; classical, p. 155).
Location: p. 153 (PDF p. 171), paragraph after Definition 4.2.1; p. 155 (PDF p. 173), sentence after Definition 4.2.3. -/
theorem standard_error_diagonal_index {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (e : Fin n → ℝ) (s2 : ℝ) (k : Fin (K+1)) :
   coefficientSE (robustCov X e) k=Real.sqrt (robustCov X e k k) ∧
   coefficientSE (classicalCov X s2) k=Real.sqrt (classicalCov X s2 k k) := by
  exact ⟨rfl,rfl⟩

/-- The homoskedastic middle moment σ²A gives the corrected symmetric sandwich σ²A⁻¹.
Target P001-T67: Section 4.2.3, the display reducing the asymptotic covariance of the OLS estimator under a linear CEF and homoskedasticity, with the stray observation subscript removed.
Location: p. 155 (PDF p. 173), display beginning $n\mathrm{V}[\hat{\boldsymbol\beta}] \approx$; the sandwich form: p. 152 (PDF p. 170). -/
theorem homoskedastic_sandwich_identity {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) (hA : IsUnit A.det) (s2 : ℝ) :
   A⁻¹*(s2 • A)*A⁻¹=s2 • A⁻¹ := by
  
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.nonsing_inv_mul A hA, Matrix.one_mul]

/-- The derivative in the first coordinate is −1 or 9; its uniform-covariate average is 1 while the derivative at the mean (1/2,1/2) is −1.
Target P001-T69: Example 4.3.8 (Differences between the Average Partial Derivative and the Partial Derivative at the Average), with the subscripts of the two displays corrected; and the label in the sentence after Definition 4.3.6.
Location: Example 4.3.8: p. 167 (PDF p. 185). Sentence after Definition 4.3.6: p. 166 (PDF p. 184). Definitions 4.3.6 and 4.3.7: pp. 166–167. -/
theorem apd_pda_different_correct_coordinate_supporting : (∀ x y : ℝ, deriv (fun t => apdExample t y) x=if y ≤ 4/5 then -1 else 9) ∧
   (-1*(4/5)+9*(1/5) : ℝ)=1 ∧ deriv (fun t => apdExample t (1/2)) (1/2)= -1 := by
  refine ⟨?_, by norm_num, ?_⟩
  · intro x y
    by_cases hy : y ≤ 4/5
    · simp [apdExample,hy]
    · simp [apdExample,hy]
  · norm_num [apdExample]

/-- With a nonempty sample, the printed unsquared residual criterion has no minimizer because increasing the intercept decreases it without bound.
Target P001-T70: Definition 4.3.9 (Polynomial Least Squares Sieve Estimator), the least squares criterion, corrected (the missing square).
Location: p. 169 (PDF p. 187), the display defining $\hat{\boldsymbol\beta}$ (the definition begins on p. 168, PDF p. 186). -/
theorem unsquared_sieve_no_minimum {n : ℕ} (hn : 0 < n) (Y : Fin n → ℝ) :
   ∀ B : ℝ, ∃ b0 : ℝ, (∑ i,(Y i-b0)) < B := by
  
  intro B
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨((∑ i,Y i)-B+1)/(n : ℝ), ?_⟩
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmul : (n : ℝ)*((∑ i,Y i)-B+1)/(n : ℝ)=(∑ i,Y i)-B+1 :=
    mul_div_cancel_left₀ _ (ne_of_gt hnR)
  rw [← mul_div_assoc, hmul]
  linarith

/-- At λ=0 the corrected lasso objective is exactly the OLS mean squared residual objective, and its slope penalty vanishes at an intercept-only vector.
Target P001-T71: Definition 4.3.10 (Lasso Estimator), corrected: the coefficient vector in $\mathbb{R}^{K+1}$ and the penalty on the slope coefficients.
Location: pp. 169–170 (PDF pp. 187–188). -/
theorem lasso_zero_penalty_ols {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ) (b : Fin (K+1) → ℝ) :
   lassoCriterion X Y 0 b=olsRSS X Y b/(n : ℝ) ∧
   slopePenalty (fun k : Fin (K+1) => if k=0 then (1 : ℝ) else 0)=0 := by
  constructor
  · simp [lassoCriterion]
  · simp [slopePenalty]

/-- For λ≥0 and nonempty data, the corrected lasso criterion is convex in the full coefficient vector.
Target P001-T71: Definition 4.3.10 (Lasso Estimator), corrected: the coefficient vector in $\mathbb{R}^{K+1}$ and the penalty on the slope coefficients.
Location: pp. 169–170 (PDF pp. 187–188). -/
theorem lasso_convex {n K : ℕ} (hn : 0 < n) (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ)
   (lam : ℝ) (hlam : 0 ≤ lam) : ConvexOn ℝ Set.univ (lassoCriterion X Y lam) := by
  
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  have hb' : b=1-a := by linarith
  have hquad (u v : ℝ) : (a*u+b*v)^2 ≤ a*u^2+b*v^2 := by
    have he : a*u^2+b*v^2-(a*u+b*v)^2=a*b*(u-v)^2 := by
      rw [hb']
      ring
    have hp := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (u-v))
    linarith
  have hlin (i : Fin n) : (X.mulVec (a • x+b • y)) i=
      a*(X.mulVec x) i+b*(X.mulVec y) i := by
    simp [Matrix.mulVec_add,Matrix.mulVec_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have hres (i : Fin n) : Y i-(X.mulVec (a • x+b • y)) i=
      a*(Y i-(X.mulVec x) i)+b*(Y i-(X.mulVec y) i) := by
    rw [hlin,hb']
    ring
  have hRSS : olsRSS X Y (a • x+b • y) ≤ a*olsRSS X Y x+b*olsRSS X Y y := by
    unfold olsRSS
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i hi => by rw [hres]; exact hquad _ _)
  have hpen : slopePenalty (a • x+b • y) ≤ a*slopePenalty x+b*slopePenalty y := by
    unfold slopePenalty
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    change |a*x i.succ+b*y i.succ| ≤ a*|x i.succ|+b*|y i.succ|
    calc
      _ ≤ |a*x i.succ|+|b*y i.succ| := abs_add_le _ _
      _=_ := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
  have hdiv := div_le_div_of_nonneg_right hRSS (show (0 : ℝ) ≤ n by positivity)
  have hmul := mul_le_mul_of_nonneg_left hpen hlam
  change olsRSS X Y (a • x+b • y)/(n : ℝ)+lam*slopePenalty (a • x+b • y) ≤ 
    a*(olsRSS X Y x/(n : ℝ)+lam*slopePenalty x)+
    b*(olsRSS X Y y/(n : ℝ)+lam*slopePenalty y)
  rw [add_div,mul_div_assoc,mul_div_assoc] at hdiv
  nlinarith

/-- The positive-scale normal density agrees pointwise with Mathlib’s Gaussian density. -/
theorem normalDensity_eq_gaussianPDFReal (m s : ℝ) (hs : 0 < s) :
    normalDensity m s=gaussianPDFReal m ⟨s^2,sq_nonneg _⟩ := by
  funext y
  have hsqrt : Real.sqrt (2*Real.pi*s^2)=s*Real.sqrt (2*Real.pi) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hs]
    ring
  change Real.exp (-(y-m)^2/(2*s^2))/(s*Real.sqrt (2*Real.pi))=
    (Real.sqrt (2*Real.pi*s^2))⁻¹*Real.exp (-(y-m)^2/(2*s^2))
  rw [hsqrt]
  ring

/-- The positive-scale normal conditional density has integral one and conditional mean x·beta, as in the corrected classical linear model.
Target P001-T72: Definition 5.1.4 (Classical Linear Model), the parameter space, corrected ($\sigma > 0$); with Theorem 5.1.5 (CEF of the Classical Linear Model).
Location: Definition 5.1.4: pp. 180–181 (PDF pp. 198–199). Theorem 5.1.5: p. 181 (PDF p. 199). -/
theorem classical_linear_positive_scale_cef {K : ℕ} (x b : Fin (K+1) → ℝ) (s : ℝ) (hs : 0 < s) :
   (∫ y,normalDensity (∑ k,x k*b k) s y)=1 ∧
   (∫ y,y*normalDensity (∑ k,x k*b k) s y)=∑ k,x k*b k := by
  let v : ℝ≥0 := ⟨s^2,sq_nonneg _⟩
  have hv : v≠0 := by
    intro he
    have he' : s^2=0 := congrArg (fun x : ℝ≥0 => (x : ℝ)) he
    exact hs.ne' (sq_eq_zero_iff.mp he')
  have hPDF : normalDensity (∑ k,x k*b k) s=gaussianPDFReal (∑ k,x k*b k) v :=
    normalDensity_eq_gaussianPDFReal _ s hs
  constructor
  · rw [hPDF]
    exact integral_gaussianPDFReal_eq_one _ hv
  · calc
      (∫ y,y*normalDensity (∑ k,x k*b k) s y)=
          ∫ y,gaussianPDFReal (∑ k,x k*b k) v y • y := by
        rw [hPDF]
        apply integral_congr_ae
        exact ae_of_all _ (fun y => by simp only [smul_eq_mul]; ring)
      _ = ∫ y,y ∂gaussianReal (∑ k,x k*b k) v :=
        (integral_gaussianReal_eq_integral_smul hv).symm
      _ = ∑ k,x k*b k := integral_id_gaussianReal

/-- The explicit four-atom law has linear CEF 2+X and zero-mean, uncorrelated residuals, but the residual absolute-value event and X fail the independence product equation.
Target P001-T73: Section 5.1.1, the sentence attributing independence from $\mathbf{X}$ to the deviations from the CEF (with the reference to Theorem 2.2.19), as printed.
Location: p. 181 (PDF p. 199), paragraph after the display $Y = \mathbf{X}\boldsymbol\beta + \varepsilon$. Theorem 2.2.19: p. 74 (PDF p. 92). -/
theorem cef_residual_not_independent : fcond heteroskedasticLaw heteroY heteroX 0=2 ∧
   fcond heteroskedasticLaw heteroY heteroX 1=3 ∧
   fmean heteroskedasticLaw heteroResidual=0 ∧ fcov heteroskedasticLaw heteroX heteroResidual=0 ∧
   fprob heteroskedasticLaw (fun i => heteroX i=0 ∧ |heteroResidual i|=1)=1/2 ∧
   fprob heteroskedasticLaw (fun i => heteroX i=0)*
     fprob heteroskedasticLaw (fun i => |heteroResidual i|=1)=1/4 ∧ (1/2 : ℝ)≠1/4 := by
  norm_num [fcond, fprob, fmean, fcov, heteroskedasticLaw, heteroX, heteroY, heteroResidual, Fin.sum_univ_succ]

/-- The integral-identity CEF is a version of the standard conditional expectation. -/
theorem isCEF_condExp {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y : Ω → ℝ) (m : E → ℝ) (hm : IsCEF μ X Y m) :
    (m ∘ X) =ᵐ[μ] μ[Y | MeasurableSpace.comap X inferInstance] := by
  have hXm : Measurable[MeasurableSpace.comap X inferInstance] X :=
    measurable_iff_comap_le.mpr le_rfl
  refine ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hm.2.1
    (fun s hs hfin => hm.2.2.1.integrableOn) ?_
    (hm.1.comp hXm).stronglyMeasurable.aestronglyMeasurable
  intro s hs hfin
  rcases hs with ⟨A, hA, rfl⟩
  exact (hm.2.2.2 A hA).symm

/-- CEF deviations have conditional mean zero, mean zero and zero covariance with every square-integrable function of the covariates.
Target P001-T74: Section 5.1.1, the comparison of the classical linear model's errors with deviations from the CEF, corrected ('uncorrelated with' for 'independent of'); with Theorem 2.2.19 (Properties of Deviations from the CEF).
Location: p. 181 (PDF p. 199), paragraph after the display $Y = \mathbf{X}\boldsymbol\beta + \varepsilon$. Theorem 2.2.19: p. 74 (PDF p. 92), proof on pp. 74–75. -/
theorem cef_residual_orthogonality_correction {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y : Ω → ℝ) (hY : MemLp Y 2 μ) (m : E → ℝ) (hm : IsCEF μ X Y m)
   (hm2 : MemLp (m ∘ X) 2 μ) :
   IsCEF μ X (fun ω => Y ω-m (X ω)) (fun _ => 0) ∧
   mean μ (fun ω => Y ω-m (X ω))=0 ∧
   ∀ g : E → ℝ, Measurable g → MemLp (g ∘ X) 2 μ →
     covariance (g ∘ X) (fun ω => Y ω-m (X ω)) μ=0 := by
  let R : Ω → ℝ := fun ω => Y ω-m (X ω)
  have hR2 : MemLp R 2 μ := hY.sub hm2
  have hRint : Integrable R μ := hR2.integrable one_le_two
  have hMi : Integrable (fun ω => m (X ω)) μ := hm.2.2.1
  have hc : IsCEF μ X R (fun _ => 0) := by
    refine ⟨measurable_const, hRint, integrable_const _, ?_⟩
    intro A hA
    change (∫ ω in X ⁻¹' A, Y ω-m (X ω) ∂μ)=_
    rw [integral_sub hm.2.1.integrableOn hMi.integrableOn, hm.2.2.2 A hA]
    simp
  have hmean : mean μ R=0 := by
    simpa [mean] using hc.2.2.2 Set.univ MeasurableSet.univ
  refine ⟨hc, hmean, ?_⟩
  intro g hg hg2
  have hXm : Measurable[MeasurableSpace.comap X inferInstance] X :=
    measurable_iff_comap_le.mpr le_rfl
  have hGm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] (g ∘ X) :=
    (hg.comp hXm).stronglyMeasurable
  have hz : μ[R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] (fun _ => 0) :=
    (isCEF_condExp μ X hX R (fun _ => 0) hc).symm
  have hmul := condExp_mul_of_stronglyMeasurable_left hGm (hg2.integrable_mul hR2) hRint
  have hprod : (∫ ω, (g ∘ X) ω*R ω ∂μ)=0 := by
    change (∫ ω, ((g ∘ X)*R) ω ∂μ)=0
    rw [← integral_condExp hX.comap_le (f := (g ∘ X)*R)]
    apply integral_eq_zero_of_ae
    filter_upwards [hmul, hz] with ω hω hzero
    simp only [hω, Pi.mul_apply, hzero, mul_zero, Pi.zero_apply]
  rw [covariance_eq_sub hg2 hR2]
  change (∫ ω, (g ∘ X) ω*R ω ∂μ)-mean μ (g ∘ X)*mean μ R=0
  rw [hprod, hmean]
  ring

/-- At each fixed covariate x, the binary-choice PMF has conditional mean h(x·beta), in [0,1].
Target P001-T75: Theorem 5.1.8 (CEF of a Binary Choice Model) and the kernel of Definition 5.1.7, with the fixed argument $\mathbf{x}$ in place of the random vector $\mathbf{X}$.
Location: Definition 5.1.7: pp. 182–183 (PDF pp. 200–201). Theorem 5.1.8: p. 183 (PDF p. 201). -/
theorem binary_choice_fixed_argument_mean {K : ℕ} (x b : Fin (K+1) → ℝ) (h : ℝ → ℝ) (hh : ∀ t,0 ≤ h t ∧ h t ≤ 1) :
   0*(1-h (∑ k,x k*b k))+1*h (∑ k,x k*b k)=h (∑ k,x k*b k) ∧
   h (∑ k,x k*b k) ∈ Set.Icc 0 1 := by
  exact ⟨by ring,hh _⟩

/-- For every fixed positive scale, the coefficient maximizers of the normal log likelihood are precisely the OLS residual-sum-of-squares minimizers in R^(K+1).
Target P001-T76: Example 5.2.4 (Maximum Likelihood Estimation of the Classical Linear Model), the maximization display, corrected: the coefficient vector in $\mathbb{R}^{K+1}$ and the likelihood written with $(\mathbf{b}, s)$; the ML estimator of $\boldsymbol\beta$ is the OLS estimator.
Location: pp. 190–191 (PDF pp. 208–209). -/
theorem normal_fixed_scale_ml_is_ols {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ)
   (bstar : Fin (K+1) → ℝ) (s : ℝ) (hs : 0 < s) :
   (∀ b,normalLogLikelihood X Y b s ≤ normalLogLikelihood X Y bstar s) ↔
   (∀ b,olsRSS X Y bstar ≤ olsRSS X Y b) := by
  have hd : 0 < 2*s^2 := by positivity
  constructor
  · intro h b
    have hb := h b
    unfold normalLogLikelihood at hb
    have hq : olsRSS X Y bstar/(2*s^2)  ≤  olsRSS X Y b/(2*s^2) := by linarith
    exact (div_le_div_iff_of_pos_right hd).mp hq
  · intro h b
    have hq := (div_le_div_iff_of_pos_right hd).mpr (h b)
    unfold normalLogLikelihood
    linarith

/-- A finite nonnegative conditional PMF or PDF evaluated at the random data defines a random function on the parameter space with values in [0,infinity).
Target P001-T77: Footnote 5 (the likelihood function as a random function), with the domain and codomain corrected.
Location: p. 186 (PDF p. 204), footnote 5, attached to the sentence after Definition 5.2.1. -/
theorem likelihood_correct_function_space {Ω : Type*} {τ : ℕ} (Θ : Set (Fin τ → ℝ)) (Y : Ω → ℝ)
   {K : ℕ} (X : Ω → Fin K → ℝ) (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (hg : ∀ y x t,t∈Θ → 0 ≤ g y x t) :
   ∃ L : Ω → Θ → ℝ≥0, ∀ ω t,(L ω t : ℝ)=g (Y ω) (X ω) t.val := by
  refine ⟨fun ω t => ⟨g (Y ω) (X ω) t.val,hg _ _ _ t.property⟩, ?_⟩
  intro ω t
  rfl

/-- If the minimized residual sum Q is positive, the joint normal log likelihood is maximized at the OLS coefficient and scale sqrt(Q/n); its variance parameter is Q/n.
Target P001-T78: Footnote 10 (Example 5.2.4), corrected: $\frac{1}{n}\sum_i(Y_i - \mathbf{X}_i\hat{\boldsymbol\beta})^2$ is the ML estimator of $\sigma^2$, not of $\sigma$.
Location: p. 191 (PDF p. 209), footnote 10. -/
theorem normal_joint_ml_scale_square {n K : ℕ} (hn : 0 < n) (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ)
   (bstar : Fin (K+1) → ℝ) (hmin : ∀ b,olsRSS X Y bstar ≤ olsRSS X Y b)
   (hQ : 0 < olsRSS X Y bstar) :
   0 < Real.sqrt (olsRSS X Y bstar/(n : ℝ)) ∧
   (Real.sqrt (olsRSS X Y bstar/(n : ℝ)))^2=olsRSS X Y bstar/(n : ℝ) ∧
   ∀ b s,0 < s → normalLogLikelihood X Y b s  ≤ 
     normalLogLikelihood X Y bstar (Real.sqrt (olsRSS X Y bstar/(n : ℝ))) := by
  let q : ℝ := olsRSS X Y bstar/(n : ℝ)
  let σ : ℝ := Real.sqrt q
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hq : 0<q := div_pos hQ hnR
  have hσ : 0<σ := Real.sqrt_pos.mpr hq
  have hσsq : σ^2=q := Real.sq_sqrt hq.le
  refine ⟨hσ, hσsq, ?_⟩
  intro b s hs
  have hfirst := ((normal_fixed_scale_ml_is_ols X Y bstar s hs).mpr hmin) b
  apply hfirst.trans
  have hratio : 0<q/s^2 := div_pos hq (sq_pos_of_pos hs)
  have hlog : Real.log (q/s^2)=2*Real.log σ-2*Real.log s := by
    rw [Real.log_div hq.ne' (sq_pos_of_pos hs).ne', ← hσsq, Real.log_pow, Real.log_pow]
    ring
  have hl := Real.log_le_sub_one_of_pos hratio
  rw [hlog] at hl
  have hb := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ (n : ℝ)/2 by positivity)
  have hQs : olsRSS X Y bstar/(2*s^2)=(n : ℝ)/2*(q/s^2) := by
    dsimp [q]
    field_simp
  have hQσ : olsRSS X Y bstar/(2*σ^2)=(n : ℝ)/2 := by
    rw [hσsq]
    dsimp [q]
    field_simp
  change normalLogLikelihood X Y bstar s ≤ normalLogLikelihood X Y bstar σ
  unfold normalLogLikelihood
  rw [hQs, hQσ]
  linarith


theorem ols_fitted_sum_squares_le {n K : ℕ} (P : Matrix (Fin n) (Fin K) ℝ) (r : Fin n → ℝ) :
    (∑ i, (P.mulVec (olsCoef P r) i)^2) ≤ ∑ i, (r i)^2 := by
  by_cases hP : IsUnit (P.transpose*P).det
  · let β := olsCoef P r
    let e := r-P.mulVec β
    have hnormal : P.transpose.mulVec e=0 := by
      change P.transpose.mulVec (r-P.mulVec ((P.transpose*P)⁻¹.mulVec (P.transpose.mulVec r)))=0
      rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ hP,Matrix.one_mulVec,sub_self]
    have hcross : (∑ i, e i*(P.mulVec β) i)=0 := by
      change dotProduct e (P.mulVec β)=0
      rw [Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,hnormal,zero_dotProduct]
    have hsplit : (∑ i, (r i)^2) = (∑ i, (e i)^2)+(∑ i, (P.mulVec β i)^2) := by
      calc
        (∑ i, (r i)^2) = ∑ i, ((e i)^2+2*(e i*(P.mulVec β) i)+((P.mulVec β) i)^2) := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp [e]
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib,← Finset.mul_sum,hcross,mul_zero,add_zero]
    have hnon : 0 ≤ ∑ i, (e i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    change (∑ i, (P.mulVec β i)^2) ≤ _
    linarith
  · rw [show olsCoef P r=0 by simp [olsCoef,Matrix.nonsing_inv_apply_not_isUnit _ hP]]
    simp only [Matrix.mulVec_zero,Pi.zero_apply,zero_pow (by decide : 2≠0),Finset.sum_const_zero]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- The corrected average of conditional fitted laws and observed covariates is a probability law whose joint CDF uses Xi[k]≤x[k] in every coordinate.
Target P001-T79: Definition 5.2.10 (Maximum Likelihood Plug-In Estimator), the indicator in both displays of $\hat F_{ML}$, with its subscripts corrected.
Location: pp. 197–198 (PDF pp. 215–216). -/
theorem ml_plugin_correct_covariate_indices {n K : ℕ} (hn : 0 < n) (X : Fin n → Fin K → ℝ) (ν : Fin n → Measure ℝ)
   (hν : ∀ i,IsProbabilityMeasure (ν i)) :
   IsProbabilityMeasure (mlFittedLaw X ν) ∧ ∀ y : ℝ, ∀ x : Fin K → ℝ,
     prob (mlFittedLaw X ν) {z | z.1 ≤ y ∧ ∀ k,z.2 k ≤ x k} =
       (∑ i,if (∀ k,X i k ≤ x k) then prob (ν i) (Set.Iic y) else 0)/(n : ℝ) := by
  haveI : ∀ i, IsProbabilityMeasure (ν i) := hν
  have hn0 : (n:ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  constructor
  · constructor
    simp only [mlFittedLaw,Measure.smul_apply,Measure.finsetSum_apply,measure_univ,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,smul_eq_mul,mul_one]
    exact ENNReal.inv_mul_cancel hn0 (by simp)
  · intro y x
    have he : {z : ℝ × (Fin K → ℝ) | z.1 ≤ y ∧ ∀ k, z.2 k ≤ x k} =
        Set.Iic y ×ˢ {u : Fin K → ℝ | ∀ k, u k ≤ x k} := by
      ext z
      simp only [Set.mem_setOf_eq,Set.mem_prod,Set.mem_Iic]
    have hcomp (i : Fin n) :
        prob ((ν i).prod (Measure.dirac (X i))) {z | z.1 ≤ y ∧ ∀ k, z.2 k ≤ x k} =
          if (∀ k,X i k ≤ x k) then prob (ν i) (Set.Iic y) else 0 := by
      unfold prob
      rw [he,Measure.prod_prod,Measure.dirac_apply]
      by_cases hx : ∀ k, X i k ≤ x k <;> simp [Set.indicator,hx,prob]
    unfold prob mlFittedLaw
    rw [Measure.smul_apply,Measure.finsetSum_apply]
    simp only [smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast]
    rw [ENNReal.toReal_sum (fun i _ => measure_ne_top ((ν i).prod (Measure.dirac (X i))) _)]
    change (n:ℝ)⁻¹*(∑ i, prob ((ν i).prod (Measure.dirac (X i))) _) = _
    simp_rw [hcomp]
    simp only [prob]
    ring

/-- For the six printed censored observations, imputing zero gives lower mean 1/2 and imputing one gives upper mean 5/6.
Target P001-T80: Example 6.1.2 (Bounding the Expected Value), the upper-bound instruction, corrected ('highest' for 'lowest'); with Theorem 6.1.3 (Sharp Bounds for the Expected Value).
Location: Example 6.1.2: pp. 209–210 (PDF pp. 227–228). Theorem 6.1.3: p. 210 (PDF p. 228), proof on p. 211 (PDF p. 229). Section 6.1.1, first paragraphs: p. 209. -/
theorem missing_data_bounds_example : (∑ i : Fin 6,missingEndpoint (stableExampleYstar i)
       (stableExampleR i) 0)/6=1/2 ∧
   (∑ i : Fin 6,missingEndpoint (stableExampleYstar i)
       (stableExampleR i) 1)/6=5/6 := by
  norm_num [missingEndpoint,stableExampleYstar,stableExampleR,Fin.sum_univ_succ]

/-- Bounded outcomes lie between the lowest- and highest-value imputations in expectation, and every point of that interval is attained by a completion with the same observable data.
Target P001-T80: Example 6.1.2 (Bounding the Expected Value), the upper-bound instruction, corrected ('highest' for 'lowest'); with Theorem 6.1.3 (Sharp Bounds for the Expected Value).
Location: Example 6.1.2: pp. 209–210 (PDF pp. 227–228). Theorem 6.1.3: p. 210 (PDF p. 228), proof on p. 211 (PDF p. 229). Section 6.1.1, first paragraphs: p. 209. -/
theorem missing_data_bounds_and_sharpness {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R) (a b : ℝ)
   (hbound : ∀ ω,Y ω∈Set.Icc a b) (hbinary : ∀ ω,R ω=0 ∨ R ω=1) :
   let L := mean μ (fun ω => missingEndpoint (censored (Y ω) (R ω)) (R ω) a)
   let U := mean μ (fun ω => missingEndpoint (censored (Y ω) (R ω)) (R ω) b)
   L ≤ mean μ Y ∧ mean μ Y ≤ U ∧ ∀ c : ℝ,c∈Set.Icc L U →
     ∃ Y' : Ω → ℝ, Measurable Y' ∧ (∀ ω,Y' ω∈Set.Icc a b) ∧ mean μ Y'=c ∧
       (fun ω => censored (Y' ω) (R ω))=(fun ω => censored (Y ω) (R ω)) := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hab : a≤b := (hbound ω₀).1.trans (hbound ω₀).2
  let l : Ω → ℝ := fun ω => missingEndpoint (censored (Y ω) (R ω)) (R ω) a
  let u : Ω → ℝ := fun ω => missingEndpoint (censored (Y ω) (R ω)) (R ω) b
  have hlm : Measurable l := by dsimp [l,missingEndpoint,censored]; fun_prop
  have hum : Measurable u := by dsimp [u,missingEndpoint,censored]; fun_prop
  have hlb : ∀ ω, l ω ∈ Set.Icc a b := by
    intro ω
    rcases hbinary ω with hr|hr
    · simpa [l,missingEndpoint,censored,hr] using hab
    · simpa [l,missingEndpoint,censored,hr] using hbound ω
  have hub : ∀ ω, u ω ∈ Set.Icc a b := by
    intro ω
    rcases hbinary ω with hr|hr
    · simpa [u,missingEndpoint,censored,hr] using hab
    · simpa [u,missingEndpoint,censored,hr] using hbound ω
  have hint (g : Ω → ℝ) (hgm : Measurable g) (hgb : ∀ ω, g ω ∈ Set.Icc a b) :
      Integrable g μ := by
    apply Integrable.of_bound hgm.aestronglyMeasurable (max |a| |b|)
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs (hgb ω).1 (hgb ω).2
  have hli := hint l hlm hlb
  have hui := hint u hum hub
  have hyi := hint Y hY hbound
  have hly : ∀ ω, l ω≤Y ω := by
    intro ω
    rcases hbinary ω with hr|hr
    · simpa [l,missingEndpoint,censored,hr] using (hbound ω).1
    · simp [l,missingEndpoint,censored,hr]
  have hyu : ∀ ω, Y ω≤u ω := by
    intro ω
    rcases hbinary ω with hr|hr
    · simpa [u,missingEndpoint,censored,hr] using (hbound ω).2
    · simp [u,missingEndpoint,censored,hr]
  change (∫ ω,l ω ∂μ)≤(∫ ω,Y ω ∂μ) ∧
    (∫ ω,Y ω ∂μ)≤(∫ ω,u ω ∂μ) ∧ _
  refine ⟨integral_mono hli hyi hly,integral_mono hyi hui hyu,?_⟩
  intro c hc
  change c ∈ Set.Icc (∫ ω,l ω ∂μ) (∫ ω,u ω ∂μ) at hc
  have hLU : (∫ ω,l ω ∂μ)≤(∫ ω,u ω ∂μ) :=
    integral_mono hli hui (fun ω => (hly ω).trans (hyu ω))
  by_cases heq : (∫ ω,l ω ∂μ)=(∫ ω,u ω ∂μ)
  · refine ⟨l,hlm,hlb,?_,?_⟩
    · change (∫ ω,l ω ∂μ)=c
      change c ∈ Set.Icc (∫ ω,l ω ∂μ) (∫ ω,u ω ∂μ) at hc
      exact le_antisymm hc.1 (by linarith [hc.2])
    · funext ω
      rcases hbinary ω with hr|hr <;> simp [censored,l,missingEndpoint,hr]
  · have hd : 0<(∫ ω,u ω ∂μ)-(∫ ω,l ω ∂μ) := by
      exact sub_pos.mpr (lt_of_le_of_ne hLU heq)
    let t : ℝ := (c-(∫ ω,l ω ∂μ))/((∫ ω,u ω ∂μ)-(∫ ω,l ω ∂μ))
    have ht0 : 0≤t := div_nonneg (sub_nonneg.mpr hc.1) hd.le
    have ht1 : t≤1 := (div_le_one hd).mpr (by linarith [hc.2])
    let z : Ω → ℝ := fun ω => (1-t)*l ω+t*u ω
    have hzm : Measurable z := (hlm.const_mul _).add (hum.const_mul _)
    have hzb : ∀ ω,z ω ∈ Set.Icc a b := by
      intro ω
      dsimp [z]
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (hlb ω).1),
          mul_nonneg ht0 (sub_nonneg.mpr (hub ω).1)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (hlb ω).2),
          mul_nonneg ht0 (sub_nonneg.mpr (hub ω).2)]
    refine ⟨z,hzm,hzb,?_,?_⟩
    · change (∫ ω,z ω ∂μ)=c
      dsimp [z]
      rw [integral_add (hli.const_mul _) (hui.const_mul _),integral_const_mul,integral_const_mul]
      dsimp [t]
      field_simp [hd.ne']
      <;> ring
    · funext ω
      rcases hbinary ω with hr|hr <;> simp [censored,z,l,u,missingEndpoint,hr]
      ring

/-- The donor distances are measured from unit 2 at score .14, giving .19 for unit 1 and .21 for unit 4; unit 6 at .70 is closest to unit 3 at .73. The completed-data estimate equals the printed value.
Target P001-T81: The paragraph after Example 6.2.5 (Imputation with the Propensity Score): the comparison of donors for unit 2, corrected ($p_R(\mathbf{X}_2)$ for $p_R(\mathbf{X}_1)$); with the hot deck estimate of the example.
Location: Example 6.2.5: pp. 224–225 (PDF pp. 242–243). Paragraph after it: p. 225 (PDF p. 243). -/
theorem hot_deck_correct_donor_comparison : |(33/100 : ℝ)-14/100|=19/100 ∧ |(35/100 : ℝ)-14/100|=21/100 ∧
   |(73/100 : ℝ)-14/100|=59/100 ∧ |(78/100 : ℝ)-14/100|=64/100 ∧
   |(33/100 : ℝ)-70/100|=37/100 ∧ |(73/100 : ℝ)-70/100|=3/100 ∧
   |(35/100 : ℝ)-70/100|=35/100 ∧ |(78/100 : ℝ)-70/100|=8/100 ∧ (∑ i : Fin 6,(![2,2,3,10,12,3] : Fin 6 → ℝ) i)/6=16/3 := by
  norm_num [Fin.sum_univ_succ]

/-- The donor distances are measured from unit 2 at score .14, giving .19 for unit 1 and .21 for unit 4; unit 6 at .70 is closest to unit 3 at .73. The completed-data estimate equals the printed value.
Target P001-T95: The paragraph after Example 7.2.4 (Propensity Score Matching): the comparison of donors for unit 2, corrected ($P_2$ for $P_1$); with the matching estimate of the example.
Location: Example 7.2.4: pp. 262–263 (PDF pp. 280–281). Paragraph after it: pp. 263–264 (PDF pp. 281–282). -/
theorem matching_correct_donor_comparison : |(33/100 : ℝ)-14/100|=19/100 ∧ |(35/100 : ℝ)-14/100|=21/100 ∧
   |(73/100 : ℝ)-14/100|=59/100 ∧ |(78/100 : ℝ)-14/100|=64/100 ∧
   |(33/100 : ℝ)-70/100|=37/100 ∧ |(73/100 : ℝ)-70/100|=3/100 ∧
   |(35/100 : ℝ)-70/100|=35/100 ∧ |(78/100 : ℝ)-70/100|=8/100 ∧ (∑ i : Fin 6,((![2,2,3,10,2,3] : Fin 6 → ℝ) i-(![5,5,0,5,0,0] : Fin 6 → ℝ) i))/6=7/6 := by
  norm_num [Fin.sum_univ_succ]


/-- In each positive-response cell, division by the observed response fraction equals multiplication by cell size over respondent count; summing proves IPW/post-stratification equality.
Target P001-T85: Section 6.2.5, equivalence of the IPW estimator and the post-stratification plug-in estimator, corrected: it holds when the estimated response probability in each cell is the observed respondent fraction.
Location: p. 228 (PDF p. 246), first paragraph. -/
theorem missing_ipw_saturated_cells {E : Type*} [Fintype E] (N r S : E → ℝ) (hN : ∀ x,0 < N x) (hr : ∀ x,0 < r x) :
   (∑ x,S x/(r x/N x))=∑ x,N x*S x/r x := by
  apply Finset.sum_congr rfl
  intro x hx
  field_simp [ne_of_gt (hN x), ne_of_gt (hr x)]
  <;> ring

/-- For fixed positive cell sizes, respondent counts and fitted probabilities, equality of the two estimators for every cell outcome sum is equivalent to saturation.
Target P001-T85: Section 6.2.5, equivalence of the IPW estimator and the post-stratification plug-in estimator, corrected: it holds when the estimated response probability in each cell is the observed respondent fraction.
Location: p. 228 (PDF p. 246), first paragraph. -/
theorem missing_ipw_saturation_necessary {E : Type*} [Fintype E] [DecidableEq E] (N r q : E → ℝ)
   (hN : ∀ x,0 < N x) (hr : ∀ x,0 < r x) (hq : ∀ x,0 < q x) :
   (∀ S : E → ℝ,(∑ x,S x/q x)=∑ x,N x*S x/r x) ↔ ∀ x,q x=r x/N x := by
  
  constructor
  · intro h x
    have hs := h (fun y => if y=x then 1 else 0)
    have he : 1/q x=N x/r x := by simpa [ite_div] using hs
    have hq0 := ne_of_gt (hq x)
    have hr0 := ne_of_gt (hr x)
    have hN0 := ne_of_gt (hN x)
    apply (eq_div_iff hN0).2
    field_simp [hq0,hr0] at he
    nlinarith
  · intro h S
    simp_rw [h]
    exact missing_ipw_saturated_cells N r S hN hr


theorem positive_cef_inverse_weights {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y : Ω → ℝ) (hY : Measurable Y) (hbound : ∀ ω, |Y ω|≤1)
    (p : E → ℝ) (hp : IsCEF μ X Y p) (ε : ℝ) (hε : 0<ε)
    (hpos : ∀ ω, ε<p (X ω)) :
    IsCEF μ X (fun ω => Y ω/p (X ω)) (fun _ => 1) ∧
    mean μ (fun ω => Y ω/p (X ω))=1 := by
  let W : Ω → ℝ := fun ω => Y ω/p (X ω)
  have hWi : Integrable W μ := by
    apply Integrable.of_bound ((hY.div (hp.1.comp hX)).aestronglyMeasurable) (1/ε)
    apply ae_of_all
    intro ω
    change ‖Y ω/p (X ω)‖≤1/ε
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (hε.trans (hpos ω))]
    exact div_le_div₀ (by norm_num) (hbound ω) hε (hpos ω).le
  have hXm : Measurable[MeasurableSpace.comap X inferInstance] X :=
    measurable_iff_comap_le.mpr le_rfl
  have hgm : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
      (fun ω => (p (X ω))⁻¹) := ((hp.1.comp hXm).inv).stronglyMeasurable
  have hprod : Integrable ((fun ω => (p (X ω))⁻¹)*Y) μ := by
    change Integrable (fun ω => (p (X ω))⁻¹*Y ω) μ
    exact hWi.congr (ae_of_all _ (fun ω => by simp [W,div_eq_mul_inv,mul_comm]))
  have hmul := condExp_mul_of_stronglyMeasurable_left hgm hprod hp.2.1
  have hcef := isCEF_condExp μ X hX Y p hp
  have he : μ[W | MeasurableSpace.comap X inferInstance] =ᵐ[μ] (fun _ => 1) := by
    have hw : W=(fun ω => (p (X ω))⁻¹)*Y := by
      funext ω
      simp only [W,Pi.mul_apply,div_eq_mul_inv,mul_comm]
    rw [hw]
    filter_upwards [hmul,hcef] with ω hω hωp
    rw [hω,Pi.mul_apply,←hωp]
    exact inv_mul_cancel₀ (hε.trans (hpos ω)).ne'
  have hwcef : IsCEF μ X W (fun _ => 1) := by
    refine ⟨measurable_const,hWi,integrable_const 1,?_⟩
    intro A hA
    rw [←setIntegral_condExp hX.comap_le hWi (show MeasurableSet[MeasurableSpace.comap X inferInstance] (X ⁻¹' A) from ⟨A,hA,rfl⟩)]
    apply setIntegral_congr_ae (hA.preimage hX)
    filter_upwards [he] with ω hω
    intro _
    exact hω
  refine ⟨hwcef,?_⟩
  simpa [mean] using hwcef.2.2.2 Set.univ MeasurableSet.univ

/-- True-propensity respondent weights have conditional and unconditional mean one; all-unit reciprocal weights have mean at least one with equality only for certain response.
Target P001-T86: The paragraph after Definition 6.2.8 (Stabilized IPW Estimator for Missing Data): the sum whose between-sample variation the stabilized estimator accounts for, corrected ($R_i$ in the numerator).
Location: p. 228 (PDF p. 246), Definition 6.2.8 and the paragraph after it. -/
theorem response_weights_denominator_correction {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (R : Ω → ℝ) (hR : Measurable R) (hbinary : ∀ ω,R ω=0 ∨ R ω=1)
   (p : E → ℝ) (hp : IsCEF μ X R p)
   (hpos : ∃ ε : ℝ,0 < ε ∧ ∀ ω,ε < p (X ω) ∧ p (X ω) ≤ 1) :
   IsCEF μ X (fun ω => R ω/p (X ω)) (fun _ => 1) ∧
   mean μ (fun ω => R ω/p (X ω))=1 ∧
   1 ≤ mean μ (fun ω => 1/p (X ω)) ∧
   (mean μ (fun ω => 1/p (X ω))=1 ↔ ∀ᵐ ω ∂μ,p (X ω)=1) := by
  obtain ⟨ε,hε,hpos⟩ := hpos
  have hw := positive_cef_inverse_weights μ X hX R hR
    (fun ω => by rcases hbinary ω with h|h <;> rw [h] <;> norm_num) p hp ε hε (fun ω => (hpos ω).1)
  have hpi : Integrable (fun ω => 1/p (X ω)) μ := by
    apply Integrable.of_bound (measurable_const.div (hp.1.comp hX)).aestronglyMeasurable (1/ε)
    apply ae_of_all
    intro ω
    change ‖1/p (X ω)‖≤1/ε
    rw [Real.norm_eq_abs,abs_div,abs_one,abs_of_pos (hε.trans (hpos ω).1)]
    exact div_le_div₀ (by norm_num) le_rfl hε (hpos ω).1.le
  have hpoint (ω : Ω) : 1≤1/p (X ω) := by
    rw [one_le_div (hε.trans (hpos ω).1)]
    exact (hpos ω).2
  have hmean : 1≤mean μ (fun ω => 1/p (X ω)) := by
    have hh := integral_mono (integrable_const (1 : ℝ)) hpi hpoint
    simpa [mean] using hh
  refine ⟨hw.1,hw.2,hmean,?_⟩
  constructor
  · intro heq
    have hzero : (∫ ω, (1/p (X ω)-1) ∂μ)=0 := by
      rw [integral_sub hpi (integrable_const 1)]
      simpa [mean] using sub_eq_zero.mpr heq
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun ω => sub_nonneg.mpr (hpoint ω)) (hpi.sub (integrable_const 1))).mp hzero
    filter_upwards [hae] with ω hω
    change 1/p (X ω)-1=0 at hω
    exact ((div_eq_one_iff_eq (hε.trans (hpos ω).1).ne').mp (sub_eq_zero.mp hω)).symm
  · intro heq
    have hh : (fun ω => 1/p (X ω))=ᵐ[μ] (fun _ => (1 : ℝ)) := by
      filter_upwards [heq] with ω hω
      simp [hω]
    change (∫ ω, 1/p (X ω) ∂μ)=1
    rw [integral_congr_ae hh]
    simp


/-- The duplicated observable cell has probability one third, and the corrected four conditional means give the adjusted contrast minus one quarter.
Target P001-T89: Example 7.1.17 (Conditioning on Post-Treatment Variables), the distribution of observables, corrected (the cell $(Y_i, X_i, D_i) = (1, 1, 1)$ once, with probability $\frac{1}{3}$); the adjusted contrast $-\frac{1}{4}$.
Location: pp. 253–254 (PDF pp. 271–272). -/
theorem post_treatment_observable_mass_and_contrast : fprob postTreatmentLaw (fun i => postY i=1 ∧ postX i=1 ∧ postD i=1)=1/3 ∧
   fprob postTreatmentLaw (fun i => postX i=0)=1/2 ∧
   fcond2 postTreatmentLaw postY postX postD 0 1=0 ∧
   fcond2 postTreatmentLaw postY postX postD 1 1=1 ∧
   fcond2 postTreatmentLaw postY postX postD 0 0=1/2 ∧
   fcond2 postTreatmentLaw postY postX postD 1 0=1 ∧
   ((0*(1/2)+1*(1/2))-((1/2)*(1/2)+1*(1/2)) : ℝ)= -1/4 := by
  norm_num [fprob, fcond2, postTreatmentLaw, postY, postX, postD, Fin.sum_univ_succ]

/-- The two deterministic potential-response curves produce identical observable laws under uniform treatment but have different mean causal effects from dose zero to dose 1/2.
Target P001-T90: Section 7.1.8, the claim that under ignorability $\mathrm{E}[\tau_i(d, d')]$ is point identified for any $d, d' \in \mathrm{Supp}[D_i]$, for a continuous treatment, as printed.
Location: p. 255 (PDF p. 273), first paragraph; Definition 7.1.18 and the generalized conditional independence assumption: p. 254 (PDF p. 272). Definition 6.0.1: p. 207 (PDF p. 225). -/
theorem continuous_dose_nonidentification : (volume.restrict (Set.Icc (0 : ℝ) 1)).map (fun d => ((0 : ℝ),d,(0 : ℝ)))=
     (volume.restrict (Set.Icc (0 : ℝ) 1)).map (fun d => (doseSpike d,d,(0 : ℝ))) ∧
   doseSpike (1/2)-doseSpike 0=1 ∧ (0 : ℝ)≠1 := by
  have hae : (fun d : ℝ => ((0 : ℝ),d,(0 : ℝ)))=ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun d => (doseSpike d,d,(0 : ℝ))) := by
    have hne : ∀ᵐ d ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), d≠(1/2 : ℝ) := by
      exact ae_restrict_of_ae (ae_iff.mpr (by simp))
    filter_upwards [hne] with d hd
    simp only [doseSpike,if_neg hd]
  refine ⟨Measure.map_congr hae,?_,?_⟩ <;> norm_num [doseSpike]


/-- Using the fitted coefficient vector but predicting unit 3 at the misprinted covariate 9 gives partial imputation 12103/4874, different from the full-imputation treatment coefficient 6178/2437.
Target P001-T92: Example 7.2.2 (Causal Inference with OLS Regression), the two imputation tables as printed (unit 3 with $X_{[1]i} = 9$) against the claim that both imputations give the same estimate.
Location: p. 259 (PDF p. 277), the data table and the two imputation tables. -/
theorem misprinted_imputation_table_disagreement : causalPartialImpute ![1,8,9,3,5,7]=12103/4874 ∧
   causalExampleBeta 1=6178/2437 ∧ (12103/4874-6178/2437 : ℝ)= -253/4874 ∧
   causalPartialImpute ![1,8,9,3,5,7]≠causalExampleBeta 1 := by
  norm_num [causalPartialImpute, causalPrediction, causalExampleBeta, causalExampleY,
     causalExampleD, causalExampleX2, Fin.sum_univ_succ]

/-- With unit 3 at the correct covariate 10, both imputation estimates equal the fitted treatment coefficient 6178/2437.
Target P001-T93: Example 7.2.2 (Causal Inference with OLS Regression), unit 3 of the two imputation tables, corrected ($X_{[1]3} = 10$); the two imputations give the same estimate, the OLS coefficient on $D_i$.
Location: p. 259 (PDF p. 277); the pooled-regression identity $\mathrm{E}[\tau_i|\mathbf{X}_i] = \beta_1$: p. 258 (PDF p. 276). -/
theorem corrected_imputation_table_agreement : causalPartialImpute causalExampleX1=causalExampleBeta 1 ∧
   (∑ i : Fin 6,(causalPrediction (causalExampleX1 i) (causalExampleX2 i) 1-
       causalPrediction (causalExampleX1 i) (causalExampleX2 i) 0))/6=causalExampleBeta 1 := by
  norm_num [causalPartialImpute, causalPrediction, causalExampleBeta, causalExampleY,
     causalExampleD, causalExampleX1, causalExampleX2, Fin.sum_univ_succ]

/-- For binary treatment, residual orthogonality to intercept and treatment makes both pooled-OLS imputation estimates equal the treatment coefficient.
Target P001-T93: Example 7.2.2 (Causal Inference with OLS Regression), unit 3 of the two imputation tables, corrected ($X_{[1]3} = 10$); the two imputations give the same estimate, the OLS coefficient on $D_i$.
Location: p. 259 (PDF p. 277); the pooled-regression identity $\mathrm{E}[\tau_i|\mathbf{X}_i] = \beta_1$: p. 258 (PDF p. 276). -/
theorem pooled_ols_imputation_identity {n : ℕ} (hn : 0 < n) (Y D g : Fin n → ℝ) (β : ℝ)
   (hD : ∀ i,D i=0 ∨ D i=1)
   (he : ∑ i,(Y i-g i-β*D i)=0) (heD : ∑ i,D i*(Y i-g i-β*D i)=0) :
   (∑ i,(D i*(Y i-g i)+(1-D i)*(g i+β-Y i)))/(n : ℝ)=β ∧
   (∑ i,((g i+β)-g i))/(n : ℝ)=β := by
  
  have ht : ∀ i,D i*(Y i-g i)+(1-D i)*(g i+β-Y i)=
      β+2*(D i*(Y i-g i-β*D i))-(Y i-g i-β*D i) := by
    intro i
    rcases hD i with hd | hd <;> rw [hd] <;> ring
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  constructor
  · simp_rw [ht]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      he, heD, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hn0] <;> ring
  · simp only [add_sub_cancel_left, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hn0]

/-- The corrected estimator averages the fitted conditional mean at each observed covariate Xi.
Target P001-T94: Section 7.2.3, the maximum likelihood plug-in estimator of $\mathrm{E}[Y_i(d)]$, corrected: the fitted conditional mean evaluated at the observed covariates $\mathbf{X}_i$.
Location: p. 261 (PDF p. 279), last display on the page; the population identity above it on the same page. -/
theorem ml_potential_mean_observed_covariates {n K τ : ℕ} (g : ℝ → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (d : ℝ) (X : Fin n → Fin K → ℝ) (θ : Fin τ → ℝ) :
   mlPotentialMean g d X θ=(∑ i,∫ y,y*g y d (X i) θ)/(n : ℝ) := by
  rfl

/-- In the eighteen-unit three-cell example the fitted logit propensities give IPW ATE 59/36 whereas post-stratification gives 1.
Target P001-T96: Section 7.2.6, the sentence 'In the case where we have a discrete and finite number of values for $\mathbf{X}_i$, the IPW estimator is logically equivalent to the plug-in estimator from Section 7.2.1', as printed.
Location: p. 266 (PDF p. 284), paragraph after Definition 7.2.6. Section 7.2.1 plug-in estimator: p. 256 (PDF p. 274). Section 7.2.5: p. 264 (PDF p. 282). -/
theorem causal_ipw_not_poststratified : (((3*4/(1/3)-3*3/(2/3))+(1*3/(1/2)-5*2/(1/2))+
     (5*4/(2/3)-1*3/(1/3)) : ℝ)/18)=59/36 ∧
   ((6/18)*(4-3)+(6/18)*(3-2)+(6/18)*(4-3) : ℝ)=1 ∧ (59/36 : ℝ)≠1 := by
  norm_num

/-- Using each observed treated fraction in its covariate cell makes the IPW ATE sum equal to the post-stratified cell contrast sum.
Target P001-T97: Section 7.2.6, equivalence of the IPW estimator and the post-stratification plug-in estimator of the ATE, corrected: it holds when each fitted propensity equals the observed treated fraction in its covariate cell.
Location: p. 266 (PDF p. 284), paragraph after Definition 7.2.6. -/
theorem causal_ipw_saturated_cells {E : Type*} [Fintype E] (nt nc st sc : E → ℝ)
   (ht : ∀ x,0 < nt x) (hc : ∀ x,0 < nc x) :
   (∑ x,(st x/(nt x/(nt x+nc x))-sc x/(1-nt x/(nt x+nc x))))=
     ∑ x,(nt x+nc x)*(st x/nt x-sc x/nc x) := by
  apply Finset.sum_congr rfl
  intro x hx
  have hn : nt x+nc x≠0 := ne_of_gt (by linarith [ht x,hc x])
  have heq : 1-nt x/(nt x+nc x)=nc x/(nt x+nc x) := by field_simp [hn]; ring
  rw [heq]
  field_simp [hn, ne_of_gt (ht x), ne_of_gt (hc x)]
  <;> ring

/-- The correct arm-indicator inverse-propensity weights have conditional and unconditional means one in both arms.
Target P001-T98: The paragraph after Definition 7.2.7 (Stabilized IPW Estimator for Causal Inference): the two sums whose between-sample variation the stabilized estimator accounts for, corrected (the treatment-arm indicators).
Location: p. 267 (PDF p. 285), Definition 7.2.7 and the paragraph after it. -/
theorem treatment_weights_denominators_correction {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (D : Ω → ℝ) (hD : Measurable D) (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (p : E → ℝ) (hp : IsCEF μ X D p)
   (hpos : ∃ ε : ℝ,0 < ε ∧ ∀ ω,ε < p (X ω) ∧ p (X ω) < 1-ε) :
   IsCEF μ X (fun ω => D ω/p (X ω)) (fun _ => 1) ∧
   IsCEF μ X (fun ω => (1-D ω)/(1-p (X ω))) (fun _ => 1) ∧
   mean μ (fun ω => D ω/p (X ω))=1 ∧ mean μ (fun ω => (1-D ω)/(1-p (X ω)))=1 := by
  obtain ⟨ε,hε,hpos⟩ := hpos
  have hd : ∀ ω,|D ω|≤1 := by
    intro ω
    rcases hbinary ω with h|h <;> rw [h] <;> norm_num
  have hw1 := positive_cef_inverse_weights μ X hX D hD hd p hp ε hε (fun ω => (hpos ω).1)
  have hcomp : IsCEF μ X (fun ω => 1-D ω) (fun x => 1-p x) := by
    refine ⟨measurable_const.sub hp.1,(integrable_const 1).sub hp.2.1,?_,?_⟩
    · exact (integrable_const 1).sub hp.2.2.1
    · intro A hA
      change (∫ ω in X ⁻¹' A,1-D ω ∂μ)=(∫ ω in X ⁻¹' A,1-p (X ω) ∂μ)
      have hpi : Integrable (fun ω => p (X ω)) μ := hp.2.2.1
      rw [integral_sub (integrable_const 1).integrableOn hp.2.1.integrableOn,
        integral_sub (integrable_const 1).integrableOn hpi.integrableOn,
        hp.2.2.2 A hA]
  have hw0 := positive_cef_inverse_weights μ X hX (fun ω => 1-D ω)
    (measurable_const.sub hD)
    (fun ω => by rcases hbinary ω with h|h <;> rw [h] <;> norm_num)
    (fun x => 1-p x) hcomp ε hε (fun ω => by linarith [(hpos ω).2])
  exact ⟨hw1.1,hw0.1,hw1.2,hw0.2⟩

/-- With constant individual treatment effect one and propensity 1/4, the unnormalized weighted mean is 1/4 but the ATT is one.
Target P001-T99: Section 7.3.1, the sentence 'the estimand $\mathrm{E}[p_D(\mathbf{X}_i)\tau_i]$ ... is equivalent to the average treatment effect on the treated (ATT), $\mathrm{E}[\tau_i|D_i = 1]$', as printed.
Location: p. 273 (PDF p. 291), Section 7.3.1, second paragraph. -/
theorem att_normalization_counterexample : fmean attWitness (fun _ => (1/4 : ℝ)*1)=1/4 ∧
   fcond attWitness (fun _ => 1) (![0,1] : Fin 2 → ℝ) 1=1 ∧
   (1/4 : ℝ)≠1 ∧ (1/4 : ℝ)/(1/4)=1 := by
  norm_num [fmean, fcond, fprob, attWitness, Fin.sum_univ_succ]


/-- Expectations are linear for arbitrary integrable random variables, including an added constant.
Target P001-T106: Theorem 2.1.9 (Linearity of Expectations), Theorem 2.1.13 (Alternative Formula for Variance), Theorem 2.1.14 (Properties of Variance), Theorem 2.1.16 (Properties of Standard Deviation) and Theorem 2.1.18 (Chebyshev's Inequality).
Location: Theorem 2.1.9: p. 49 (PDF p. 67). Theorems 2.1.13 and 2.1.14: p. 52 (PDF p. 70). Theorem 2.1.16: p. 53 (PDF p. 71). Theorem 2.1.18: p. 55 (PDF p. 73). -/
theorem expectation_linearity {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X Y : Ω → ℝ) (hX : Integrable X μ) (hY : Integrable Y μ) (a b c : ℝ) :
   mean μ (fun ω => a*X ω+b*Y ω+c)=a*mean μ X+b*mean μ Y+c := by
  
  unfold mean
  change (∫ ω,a*X ω+b*Y ω+c ∂μ)=_
  rw [integral_add (f := fun ω => a*X ω+b*Y ω)
      ((hX.const_mul a).add (hY.const_mul b)) (integrable_const c)]
  rw [integral_add (hX.const_mul a) (hY.const_mul b)]
  rw [integral_const_mul, integral_const_mul]
  simp

/-- Variance is second moment minus squared mean, is unchanged by constant shifts, and scales by a squared multiplier.
Target P001-T106: Theorem 2.1.9 (Linearity of Expectations), Theorem 2.1.13 (Alternative Formula for Variance), Theorem 2.1.14 (Properties of Variance), Theorem 2.1.16 (Properties of Standard Deviation) and Theorem 2.1.18 (Chebyshev's Inequality).
Location: Theorem 2.1.9: p. 49 (PDF p. 67). Theorems 2.1.13 and 2.1.14: p. 52 (PDF p. 70). Theorem 2.1.16: p. 53 (PDF p. 71). Theorem 2.1.18: p. 55 (PDF p. 73). -/
theorem variance_affine_rules {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : Ω → ℝ) (hX : MemLp X 2 μ) (a c : ℝ) :
   var μ X=mean μ (fun ω => (X ω)^2)-(mean μ X)^2 ∧
   var μ (fun ω => X ω+c)=var μ X ∧ var μ (fun ω => a*X ω)=a^2*var μ X := by
  exact ⟨variance_eq_sub hX,variance_add_const hX.aestronglyMeasurable c,
    variance_const_mul a X μ⟩

/-- Standard deviation is unchanged by shifts and scales by the absolute value of a multiplier.
Target P001-T106: Theorem 2.1.9 (Linearity of Expectations), Theorem 2.1.13 (Alternative Formula for Variance), Theorem 2.1.14 (Properties of Variance), Theorem 2.1.16 (Properties of Standard Deviation) and Theorem 2.1.18 (Chebyshev's Inequality).
Location: Theorem 2.1.9: p. 49 (PDF p. 67). Theorems 2.1.13 and 2.1.14: p. 52 (PDF p. 70). Theorem 2.1.16: p. 53 (PDF p. 71). Theorem 2.1.18: p. 55 (PDF p. 73). -/
theorem standard_deviation_rules {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : Ω → ℝ) (hX : MemLp X 2 μ) (a c : ℝ) :
   Real.sqrt (var μ (fun ω => X ω+c))=Real.sqrt (var μ X) ∧
   Real.sqrt (var μ (fun ω => a*X ω))=|a| *Real.sqrt (var μ X) := by
  
  unfold var
  constructor
  · simp [var, variance_add_const hX.aestronglyMeasurable]
  · rw [variance_const_mul, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

/-- A finite positive-variance random variable lies at least epsilon standard deviations from its mean with probability at most 1/epsilon².
Target P001-T106: Theorem 2.1.9 (Linearity of Expectations), Theorem 2.1.13 (Alternative Formula for Variance), Theorem 2.1.14 (Properties of Variance), Theorem 2.1.16 (Properties of Standard Deviation) and Theorem 2.1.18 (Chebyshev's Inequality).
Location: Theorem 2.1.9: p. 49 (PDF p. 67). Theorems 2.1.13 and 2.1.14: p. 52 (PDF p. 70). Theorem 2.1.16: p. 53 (PDF p. 71). Theorem 2.1.18: p. 55 (PDF p. 73). -/
theorem chebyshev_standard_deviations {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : Ω → ℝ) (hX : MemLp X 2 μ) (hv : 0 < var μ X) (ε : ℝ) (hε : 0 < ε) :
   prob μ {ω | ε*Real.sqrt (var μ X) ≤ |X ω-mean μ X|} ≤ 1/ε^2 := by
  
  have hc : 0 < ε*Real.sqrt (var μ X) := mul_pos hε (Real.sqrt_pos.2 hv)
  have h := chebyshev_probability μ X hX (ε*Real.sqrt (var μ X)) hc
  have heq : var μ X/(ε*Real.sqrt (var μ X))^2=1/ε^2 := by
    rw [mul_pow,Real.sq_sqrt (le_of_lt hv)]
    field_simp [ne_of_gt hv,ne_of_gt hε]
  simpa [heq] using h

/-- The expectation of any CEF version equals the expectation of the original integrable outcome.
Target P001-T107: Theorem 2.2.17 (Law of Iterated Expectations), Theorem 2.2.18 (Law of Total Variance) and Theorem 2.2.20 (The CEF is the Best Predictor).
Location: Theorem 2.2.17: p. 72 (PDF p. 90). Theorem 2.2.18: p. 73 (PDF p. 91). Theorem 2.2.20: p. 75 (PDF p. 93), proof on pp. 75–76 (PDF pp. 93–94). -/
theorem iterated_expectation {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (Y : Ω → ℝ)
   (hYi : Integrable Y μ) (m : E → ℝ) (hm : IsCEF μ X Y m) :
   mean μ Y=mean μ (m ∘ X) := by
  have h := hm.2.2.2 Set.univ MeasurableSet.univ
  simpa [mean] using h

/-- Total variance is expected conditional variance plus variance of the CEF, and CEF prediction minimizes MSE with the exact excess-risk identity.
Target P001-T107: Theorem 2.2.17 (Law of Iterated Expectations), Theorem 2.2.18 (Law of Total Variance) and Theorem 2.2.20 (The CEF is the Best Predictor).
Location: Theorem 2.2.17: p. 72 (PDF p. 90). Theorem 2.2.18: p. 73 (PDF p. 91). Theorem 2.2.20: p. 75 (PDF p. 93), proof on pp. 75–76 (PDF pp. 93–94). -/
theorem total_variance_and_cef_best_prediction {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y : Ω → ℝ) (hY : MemLp Y 2 μ) (m v : E → ℝ) (hm : IsCEF μ X Y m)
   (hm2 : MemLp (m ∘ X) 2 μ) (hv : IsCEF μ X (fun ω => (Y ω-m (X ω))^2) v) :
   var μ Y=mean μ (v ∘ X)+var μ (m ∘ X) ∧
   ∀ g : E → ℝ,Measurable g → MemLp (g ∘ X) 2 μ →
     mean μ (fun ω => (Y ω-g (X ω))^2)=mean μ (v ∘ X)+mean μ (fun ω => (m (X ω)-g (X ω))^2) ∧
     mean μ (fun ω => (Y ω-m (X ω))^2) ≤ mean μ (fun ω => (Y ω-g (X ω))^2) := by
  let R : Ω → ℝ := fun ω => Y ω-m (X ω)
  have hR2 : MemLp R 2 μ := hY.sub hm2
  rcases cef_residual_orthogonality_correction μ X hX Y hY m hm hm2 with
    ⟨hRcef, hmean, horth⟩
  change mean μ R=0 at hmean
  have hER := iterated_expectation μ X (fun ω => (Y ω-m (X ω))^2) hv.2.1 v hv
  change mean μ (fun ω => (R ω)^2)=mean μ (v ∘ X) at hER
  have hresVar : var μ R=mean μ (v ∘ X) := by
    rw [var, variance_eq_sub hR2]
    change mean μ (fun ω => (R ω)^2)-(mean μ R)^2=_
    rw [hmean, hER]
    ring
  have hCov : covariance (m ∘ X) Y μ=var μ (m ∘ X) := by
    have hc := horth m hm.1 hm2
    change covariance (m ∘ X) (Y-(m ∘ X)) μ=0 at hc
    rw [covariance_sub_right hm2 hY hm2, covariance_self hm2.aemeasurable] at hc
    exact sub_eq_zero.mp hc
  refine ⟨?_, ?_⟩
  · have hV := variance_sub hY hm2
    change var μ R=var μ Y-2*covariance Y (m ∘ X) μ+var μ (m ∘ X) at hV
    rw [covariance_comm Y (m ∘ X), hCov, hresVar] at hV
    linarith
  · intro g hg hg2
    let D : Ω → ℝ := fun ω => m (X ω)-g (X ω)
    have hD2 : MemLp D 2 μ := hm2.sub hg2
    have hO := horth (fun x => m x-g x) (hm.1.sub hg) hD2
    change covariance D R μ=0 at hO
    rw [covariance_eq_sub hD2 hR2] at hO
    have hDR0 : mean μ (fun ω => D ω*R ω)=0 := by
      change mean μ (fun ω => D ω*R ω)-mean μ D*mean μ R=0 at hO
      simpa [hmean] using hO
    have hEq : mean μ (fun ω => (Y ω-g (X ω))^2)=
        mean μ (v ∘ X)+mean μ (fun ω => (D ω)^2) := by
      have hfun : (fun ω => (Y ω-g (X ω))^2)=
          (fun ω => (R ω)^2+(2*(D ω*R ω)+(D ω)^2)) := by
        funext ω
        dsimp [R, D]
        ring
      have hDRi : Integrable (fun ω => D ω*R ω) μ := hD2.integrable_mul hR2
      have h2DRi : Integrable (fun ω => 2*(D ω*R ω)) μ := hDRi.const_mul 2
      have hDsqi : Integrable (fun ω => (D ω)^2) μ := hD2.integrable_sq
      have hsumi : Integrable (fun ω => 2*(D ω*R ω)+(D ω)^2) μ := h2DRi.add hDsqi
      rw [hfun]
      unfold mean
      rw [integral_add hR2.integrable_sq hsumi,
        integral_add h2DRi hDsqi, integral_const_mul]
      change mean μ (fun ω => (R ω)^2)+(2*mean μ (fun ω => D ω*R ω)+
        mean μ (fun ω => (D ω)^2))=_
      rw [hER, hDR0]
      simp [mean]
    refine ⟨hEq, ?_⟩
    change mean μ (fun ω => (R ω)^2) ≤ _
    rw [hER, hEq]
    exact le_add_of_nonneg_right (integral_nonneg (fun ω => sq_nonneg (D ω)))

/-- The iid sample mean deviates from the population mean by at least epsilon with probability at most Var(X)/(epsilon² n).
Target P001-T108: Theorem 3.2.3 (The Expected Value of the Sample Mean Is the Population Mean), Theorem 3.2.4 (Sampling Variance of the Sample Mean) and Theorem 3.2.5 (Chebyshev's Inequality for the Sample Mean).
Location: Theorem 3.2.3: p. 97 (PDF p. 115). Theorems 3.2.4 and 3.2.5: p. 98 (PDF p. 116), proof of 3.2.5 continuing on p. 99 (PDF p. 117). -/
theorem iid_sample_mean_chebyshev {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ)
   (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
   prob μ {ω | ε ≤ |sampleMean X n ω-mean μ (X 0)|} ≤ var μ (X 0)/(ε^2*(n : ℝ)) := by
  
  have h := chebyshev_probability μ (sampleMean X n) (sample_mean_memLp μ X hiid h2 n) ε hε
  rcases iid_sample_mean_finite_moments μ X hiid h2 n hn with ⟨hm,hv⟩
  rw [hm,hv] at h
  simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h

/-- Every continuous function on a compact interval is uniformly approximable by a real polynomial.
Target P001-T109: Theorem 4.3.3 (Polynomial Approximation of the CEF), with Theorem 4.3.2 (Weierstrass Approximation Theorem).
Location: p. 158 (PDF p. 176); proof on pp. 158–159 (PDF pp. 176–177). -/
theorem weierstrass_approximation (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
   (ε : ℝ) (hε : 0 < ε) : ∃ p : Polynomial ℝ,∀ x∈Set.Icc a b,|f x-p.eval x| < ε := by
  
  obtain ⟨p,hp⟩ := exists_polynomial_near_of_continuousOn a b f hf ε hε
  refine ⟨p, ?_⟩
  intro x hx
  simpa only [abs_sub_comm] using hp x hx



theorem bernoulli_log_strict_max (q s t : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hdir : (t-s)*(q-s) ≤ 0) (hne : t≠s) :
    q*Real.log t+(1-q)*Real.log (1-t) < q*Real.log s+(1-q)*Real.log (1-s) := by
  have hr : t/s≠1 := by
    intro h
    exact hne ((div_eq_one_iff_eq hs0.ne').mp h)
  have hr' : (1-t)/(1-s)≠1 := by
    intro h
    have he := (div_eq_one_iff_eq (sub_pos.mpr hs1).ne').mp h
    exact hne (by linarith)
  have hl := Real.log_lt_sub_one_of_pos (div_pos ht0 hs0) hr
  have hl' := Real.log_lt_sub_one_of_pos (div_pos (sub_pos.mpr ht1) (sub_pos.mpr hs1)) hr'
  rw [Real.log_div ht0.ne' hs0.ne'] at hl
  rw [Real.log_div (sub_pos.mpr ht1).ne' (sub_pos.mpr hs1).ne'] at hl'
  have hweighted : q*(Real.log t-Real.log s)+(1-q)*(Real.log (1-t)-Real.log (1-s)) <
      q*(t/s-1)+(1-q)*((1-t)/(1-s)-1) := by
    by_cases hq : q=0
    · simp only [hq,zero_mul,sub_zero,one_mul,zero_add]
      exact hl'
    · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hl (lt_of_le_of_ne hq0 (Ne.symm hq)))
        (mul_le_mul_of_nonneg_left hl'.le (sub_nonneg.mpr hq1))
  have he : q*(t/s-1)+(1-q)*((1-t)/(1-s)-1) = (t-s)*(q-s)/(s*(1-s)) := by
    field_simp [hs0.ne',(sub_pos.mpr hs1).ne']
    <;> ring
  have hnon : (t-s)*(q-s)/(s*(1-s)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hdir (mul_nonneg hs0.le (sub_nonneg.mpr hs1.le))
  rw [he] at hweighted
  linarith

/-- For every nonempty binary sample, the Bernoulli likelihood on [0,1] has its unique maximum at the fraction of ones, including all-zero and all-one samples.
Target P001-T110: Example 5.2.3 (Maximum Likelihood Estimation for a Biased Coin Flip): the ML estimate of $p$ is the sample mean.
Location: pp. 187–189 (PDF pp. 205–207); footnote 9, p. 189. -/
theorem bernoulli_ml_unique_sample_fraction {n : ℕ} (hn : 0 < n) (Y : Fin n → Bool) :
   let k := (Finset.univ.filter (fun i => Y i=true)).card
   let a := (k : ℝ)/(n : ℝ)
   a∈Set.Icc (0 : ℝ) 1 ∧ ∀ t∈Set.Icc (0 : ℝ) 1,
     (1-t)^(n-k)*t^k ≤ (1-a)^(n-k)*a^k ∧
     ((1-t)^(n-k)*t^k=(1-a)^(n-k)*a^k ↔ t=a) := by
  classical
  let k := (Finset.univ.filter (fun i => Y i=true)).card
  let a : ℝ := (k:ℝ)/(n:ℝ)
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hk : k ≤ n := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      (Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => Y i=true))
  have hkn : (k:ℝ) ≤ n := by exact_mod_cast hk
  have ha0 : 0 ≤ a := div_nonneg (Nat.cast_nonneg k) hnR.le
  have ha1 : a ≤ 1 := (div_le_iff₀ hnR).mpr (by simpa using hkn)
  change a∈Set.Icc (0:ℝ) 1 ∧ ∀ t∈Set.Icc (0:ℝ) 1,
    (1-t)^(n-k)*t^k ≤ (1-a)^(n-k)*a^k ∧
    ((1-t)^(n-k)*t^k=(1-a)^(n-k)*a^k ↔ t=a)
  refine ⟨⟨ha0,ha1⟩,?_⟩
  intro t ht
  by_cases hk0 : k=0
  · have ha : a=0 := by simp [a,hk0]
    simp only [hk0,ha,Nat.sub_zero,pow_zero,mul_one,sub_zero,one_pow]
    refine ⟨pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1]),?_⟩
    constructor
    · intro hh
      have he : 1-t=1 := (pow_left_inj₀ (by linarith [ht.2]) zero_le_one hn.ne').mp
        (by simpa using hh)
      linarith
    · intro hh
      simp [hh]
  · by_cases hkn' : k=n
    · have ha : a=1 := by simp [a,hkn',hnR.ne']
      simp only [hkn',ha,Nat.sub_self,pow_zero,one_mul,sub_self,one_pow]
      refine ⟨pow_le_one₀ ht.1 ht.2,?_⟩
      constructor
      · intro hh
        exact (pow_left_inj₀ ht.1 zero_le_one hn.ne').mp (by simpa using hh)
      · intro hh
        simp [hh]
    · have hkpos : 0<k := Nat.pos_of_ne_zero hk0
      have hknlt : k<n := lt_of_le_of_ne hk hkn'
      have hnk : 0<n-k := Nat.sub_pos_of_lt hknlt
      have hap : 0<a := div_pos (by exact_mod_cast hkpos) hnR
      have halt : a<1 := (div_lt_one hnR).mpr (by exact_mod_cast hknlt)
      have hmax : 0<(1-a)^(n-k)*a^k := mul_pos (pow_pos (sub_pos.mpr halt) _) (pow_pos hap _)
      by_cases ht0 : t=0
      · simp only [ht0,zero_pow hkpos.ne',mul_zero]
        exact ⟨hmax.le,iff_of_false (Ne.symm hmax.ne') (Ne.symm hap.ne')⟩
      · by_cases ht1 : t=1
        · simp only [ht1,sub_self,zero_pow hnk.ne',zero_mul]
          exact ⟨hmax.le,iff_of_false (Ne.symm hmax.ne') (Ne.symm halt.ne)⟩
        · have htp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
          have htl : t<1 := lt_of_le_of_ne ht.2 ht1
          by_cases hta : t=a
          · subst t
            exact ⟨le_rfl,by simp⟩
          · have hlog (z : ℝ) (hz0 : 0<z) (hz1 : z<1) :
                Real.log ((1-z)^(n-k)*z^k) =
                  (n:ℝ)*(a*Real.log z+(1-a)*Real.log (1-z)) := by
              rw [Real.log_mul (pow_ne_zero _ (sub_pos.mpr hz1).ne') (pow_ne_zero _ hz0.ne'),
                Real.log_pow,Real.log_pow,Nat.cast_sub hk]
              dsimp [a]
              field_simp [hnR.ne']
              <;> ring
            have hl := bernoulli_log_strict_max a a t ha0 ha1 hap halt htp htl (by simp) hta
            have hlt : (1-t)^(n-k)*t^k < (1-a)^(n-k)*a^k := by
              apply (Real.log_lt_log_iff
                (mul_pos (pow_pos (sub_pos.mpr htl) _) (pow_pos htp _)) hmax).mp
              rw [hlog t htp htl,hlog a hap halt]
              exact mul_lt_mul_of_pos_left hl hnR
            exact ⟨hlt.le,iff_of_false hlt.ne hta⟩

/-- For sample (1,0,1), the Bernoulli likelihood has unique maximum at 2/3.
Target P001-T110: Example 5.2.3 (Maximum Likelihood Estimation for a Biased Coin Flip): the ML estimate of $p$ is the sample mean.
Location: pp. 187–189 (PDF pp. 205–207); footnote 9, p. 189. -/
theorem three_coin_flips_maximum (t : ℝ) (ht : t∈Set.Icc (0 : ℝ) 1) :
   (1-t)*t^2 ≤ (1-(2/3 : ℝ))*(2/3)^2 ∧
   ((1-t)*t^2=(1-(2/3 : ℝ))*(2/3)^2 ↔ t=2/3) := by
  have hs := sq_nonneg (t-2/3)
  have hp : 0 < t+1/3 := by linarith [ht.1]
  have hprod := mul_nonneg hs (le_of_lt hp)
  constructor
  · nlinarith
  · constructor
    · intro h
      have hz : (t-2/3)^2*(t+1/3)=0 := by nlinarith [h]
      have hsq : (t-2/3)^2=0 := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hp)
      have hlin := (sq_eq_zero_iff).mp hsq
      linarith
    · intro h; rw [h]


/-- With bounded potential outcomes, the ATE lies between the imputed endpoints; their width is exactly b−a and every intermediate effect is attainable with the same observables.
Target P001-T114: Theorem 7.1.7 (Sharp Bounds for the ATE) and the width of the bounds; with the estimates of Example 7.1.6.
Location: Theorem 7.1.7: p. 241 (PDF p. 259); proof on pp. 241–242 (PDF pp. 259–260). Width: pp. 242–243 (PDF pp. 260–261). Example 7.1.6: p. 240 (PDF p. 258). -/
theorem ate_sharp_bounds_and_width {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1) (hD : Measurable D)
   (a b : ℝ) (hbound : ∀ ω,Y0 ω∈Set.Icc a b ∧ Y1 ω∈Set.Icc a b)
   (hbinary : ∀ ω,D ω=0 ∨ D ω=1) :
   let Y := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
   let L := mean μ (fun ω => ateLower (Y ω) (D ω) a b)
   let U := mean μ (fun ω => ateUpper (Y ω) (D ω) a b)
   mean μ (fun ω => Y1 ω-Y0 ω)∈Set.Icc L U ∧ U-L=b-a ∧
   ∀ c∈Set.Icc L U,∃ Z0 Z1 : Ω → ℝ,Measurable Z0 ∧ Measurable Z1 ∧
     (∀ ω,Z0 ω∈Set.Icc a b ∧ Z1 ω∈Set.Icc a b) ∧
     (fun ω => observedOutcome (Z0 ω) (Z1 ω) (D ω))=Y ∧ mean μ (fun ω => Z1 ω-Z0 ω)=c := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hab : a≤b := (hbound ω₀).1.1.trans (hbound ω₀).1.2
  let y : Ω → ℝ := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
  let l : Ω → ℝ := fun ω => ateLower (y ω) (D ω) a b
  let u : Ω → ℝ := fun ω => ateUpper (y ω) (D ω) a b
  have hint (g : Ω → ℝ) (hgm : Measurable g) (hgb : ∀ ω, g ω∈Set.Icc a b) :
      Integrable g μ := by
    apply Integrable.of_bound hgm.aestronglyMeasurable (max |a| |b|)
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs (hgb ω).1 (hgb ω).2
  have hi0 := hint Y0 h0 (fun ω => (hbound ω).1)
  have hi1 := hint Y1 h1 (fun ω => (hbound ω).2)
  have hlm : Measurable l := by dsimp [l,y,ateLower,observedOutcome]; fun_prop
  have hum : Measurable u := by dsimp [u,y,ateUpper,observedOutcome]; fun_prop
  have hlb : ∀ ω,l ω∈Set.Icc (a-b) (b-a) := by
    intro ω
    rcases hbinary ω with hr|hr <;> simp [l,y,ateLower,observedOutcome,hr]
    · constructor <;> linarith [(hbound ω).1.1,(hbound ω).1.2]
    · constructor <;> linarith [(hbound ω).2.1,(hbound ω).2.2]
  have hub : ∀ ω,u ω∈Set.Icc (a-b) (b-a) := by
    intro ω
    rcases hbinary ω with hr|hr <;> simp [u,y,ateUpper,observedOutcome,hr]
    · constructor <;> linarith [(hbound ω).1.1,(hbound ω).1.2]
    · constructor <;> linarith [(hbound ω).2.1,(hbound ω).2.2]
  have hli : Integrable l μ := by
    apply Integrable.of_bound hlm.aestronglyMeasurable (max |a-b| |b-a|)
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs (hlb ω).1 (hlb ω).2
  have hui : Integrable u μ := by
    apply Integrable.of_bound hum.aestronglyMeasurable (max |a-b| |b-a|)
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs (hub ω).1 (hub ω).2
  have hlτ : ∀ ω,l ω≤Y1 ω-Y0 ω := by
    intro ω
    rcases hbinary ω with hr|hr <;> simp [l,y,ateLower,observedOutcome,hr]
    · linarith [(hbound ω).2.1]
    · linarith [(hbound ω).1.2]
  have hτu : ∀ ω,Y1 ω-Y0 ω≤u ω := by
    intro ω
    rcases hbinary ω with hr|hr <;> simp [u,y,ateUpper,observedOutcome,hr]
    · linarith [(hbound ω).2.2]
    · linarith [(hbound ω).1.1]
  have hw (ω : Ω) : u ω-l ω=b-a := by
    rcases hbinary ω with hr|hr <;> simp [u,l,y,ateLower,ateUpper,observedOutcome,hr] <;> ring
  have hwidth : (∫ ω,u ω ∂μ)-(∫ ω,l ω ∂μ)=b-a := by
    rw [← integral_sub hui hli]
    simp_rw [hw]
    simp
  change (∫ ω,Y1 ω-Y0 ω ∂μ)∈Set.Icc (∫ ω,l ω ∂μ) (∫ ω,u ω ∂μ) ∧
    (∫ ω,u ω ∂μ)-(∫ ω,l ω ∂μ)=b-a ∧ _
  refine ⟨⟨integral_mono hli (hi1.sub hi0) hlτ,integral_mono (hi1.sub hi0) hui hτu⟩,
    hwidth,?_⟩
  intro c hc
  change c∈Set.Icc (∫ ω,l ω ∂μ) (∫ ω,u ω ∂μ) at hc
  let q : ℝ := a+c-(∫ ω,l ω ∂μ)
  have hqa : a≤q := by dsimp [q]; linarith [hc.1]
  have hqb : q≤b := by dsimp [q]; linarith [hc.2]
  let A0 : Ω → ℝ := fun ω => Y0 ω*(1-D ω)+(a+b-q)*D ω
  let A1 : Ω → ℝ := fun ω => Y1 ω*D ω+q*(1-D ω)
  have hA0 : Measurable A0 := by dsimp [A0]; fun_prop
  have hA1 : Measurable A1 := by dsimp [A1]; fun_prop
  refine ⟨A0,A1,hA0,hA1,?_,?_,?_⟩
  · intro ω
    rcases hbinary ω with hr|hr
    · simpa [A0,A1,hr] using And.intro (hbound ω).1 (And.intro hqa hqb)
    · simp only [A0,A1,hr,sub_self,mul_zero,mul_one,zero_add,add_zero]
      exact ⟨⟨by linarith,by linarith⟩,(hbound ω).2⟩
  · funext ω
    rcases hbinary ω with hr|hr <;> simp [observedOutcome,A0,A1,y,hr]
  · have hid (ω : Ω) : A1 ω-A0 ω=l ω+(c-(∫ ω,l ω ∂μ)) := by
      rcases hbinary ω with hr|hr <;> simp [A0,A1,l,y,ateLower,observedOutcome,q,hr] <;> ring
    change (∫ ω,A1 ω-A0 ω ∂μ)=c
    simp_rw [hid]
    rw [integral_add hli (integrable_const _)]
    simp

/-- For each observation the upper and lower ATE imputation formulas differ by b−a.
Target P001-T114: Theorem 7.1.7 (Sharp Bounds for the ATE) and the width of the bounds; with the estimates of Example 7.1.6.
Location: Theorem 7.1.7: p. 241 (PDF p. 259); proof on pp. 241–242 (PDF pp. 259–260). Width: pp. 242–243 (PDF pp. 260–261). Example 7.1.6: p. 240 (PDF p. 258). -/
theorem ate_bounds_width_finite (y d a b : ℝ) : ateUpper y d a b-ateLower y d a b=b-a := by
  unfold ateUpper ateLower; ring

/-- Random assignment identifies the ATE by observed arm means; in every binary-treatment model the arm contrast decomposes into ATT plus the control-potential selection bias.
Target P001-T115: Theorem 7.1.10 (ATE under Random Assignment) and the selection-bias decomposition.
Location: Definition 7.1.9: p. 244 (PDF p. 262). Theorem 7.1.10: p. 245 (PDF p. 263). Decomposition: p. 247 (PDF p. 265). -/
theorem random_assignment_ate_and_selection_bias {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1) (hD : Measurable D)
   (hi0 : Integrable Y0 μ) (hi1 : Integrable Y1 μ) (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (hp : 0 < prob μ {ω | D ω=1} ∧ 0 < prob μ {ω | D ω=0}) :
   let Y := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
   let arm := fun Z d => (∫ ω in {ω | D ω=d},Z ω ∂μ)/prob μ {ω | D ω=d}
   (IndepFun (fun ω => (Y0 ω,Y1 ω)) D μ → mean μ (fun ω => Y1 ω-Y0 ω)=arm Y 1-arm Y 0) ∧
   arm Y 1-arm Y 0=arm (fun ω => Y1 ω-Y0 ω) 1+arm Y0 1-arm Y0 0 := by
  let Y := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
  let arm := fun (Z : Ω → ℝ) (d : ℝ) => (∫ ω in {ω | D ω=d},Z ω ∂μ)/prob μ {ω | D ω=d}
  change (IndepFun (fun ω => (Y0 ω,Y1 ω)) D μ →
    mean μ (fun ω => Y1 ω-Y0 ω)=arm Y 1-arm Y 0) ∧
    arm Y 1-arm Y 0=arm (fun ω => Y1 ω-Y0 ω) 1+arm Y0 1-arm Y0 0
  have hA (d : ℝ) : MeasurableSet {ω | D ω=d} := measurableSet_eq_fun hD measurable_const
  have hY1 : arm Y 1=arm Y1 1 := by
    dsimp [arm]
    congr 1
    apply setIntegral_congr_fun (hA 1)
    intro ω hω
    change D ω=1 at hω
    simp [Y,observedOutcome,hω]
  have hY0 : arm Y 0=arm Y0 0 := by
    dsimp [arm]
    congr 1
    apply setIntegral_congr_fun (hA 0)
    intro ω hω
    change D ω=0 at hω
    simp [Y,observedOutcome,hω]
  have harm (Z : Ω → ℝ) (hc : IsCEF μ D Z (fun _ => mean μ Z))
      (d : ℝ) (hpd : 0<prob μ {ω | D ω=d}) : arm Z d=mean μ Z := by
    have he := hc.2.2.2 {d} (measurableSet_singleton d)
    have hset : D ⁻¹' ({d} : Set ℝ)={ω | D ω=d} := by ext ω; simp
    rw [hset] at he
    have he' : (∫ ω in {ω | D ω=d},Z ω ∂μ)=prob μ {ω | D ω=d}*mean μ Z := by
      simpa [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,prob,Measure.real] using he
    dsimp [arm]
    rw [he']
    field_simp [hpd.ne']
  constructor
  · intro hind
    have hc0 := independent_constant_cef μ D Y0 hD h0 hi0
      ((hind.comp measurable_fst measurable_id).symm)
    have hc1 := independent_constant_cef μ D Y1 hD h1 hi1
      ((hind.comp measurable_snd measurable_id).symm)
    rw [hY1,hY0,harm Y1 hc1 1 hp.1,harm Y0 hc0 0 hp.2]
    exact integral_sub hi1 hi0
  · rw [hY1,hY0]
    dsimp [arm]
    rw [integral_sub hi1.integrableOn hi0.integrableOn,sub_div]
    ring


/-- The iid sample mean converges in probability to the population mean under a finite second moment, including the zero-variance case.
Target P001-T125: Theorem 3.2.8 (Weak Law of Large Numbers).
Location: p. 100 (PDF p. 118). Definition 3.2.6: p. 99 (PDF p. 117). -/
theorem weak_law_finite_variance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ) : CP μ (sampleMean X) (mean μ (X 0)) := by
  
  intro ε hε
  change Tendsto (fun n : ℕ => (μ {ω | ε ≤ dist (sampleMean X n ω) (mean μ (X 0))}).toReal) atTop (nhds 0)
  have hupper : ∀ᶠ n in atTop,
      prob μ {ω | ε ≤ |sampleMean X n ω-mean μ (X 0)|} ≤ var μ (X 0)/(ε^2*(n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact iid_sample_mean_chebyshev μ X hiid h2 n hn ε hε
  have hni : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => var μ (X 0)/(ε^2*(n : ℝ))) atTop (nhds 0) := by
    have hg : Tendsto (fun n : ℕ => (var μ (X 0)/ε^2)*(n : ℝ)⁻¹) atTop (nhds 0) := by
      simpa only [mul_zero] using hni.const_mul (var μ (X 0)/ε^2)
    convert hg using 1
    ext n
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have h := squeeze_zero' (Eventually.of_forall (fun (n : ℕ) => ENNReal.toReal_nonneg)) hupper hlim
  simpa [Real.dist_eq] using h

/-- The centered root-n iid sample mean converges in distribution to the normal law with its finite positive population variance.
Target P001-T126: Theorem 3.2.24 (Central Limit Theorem).
Location: p. 109 (PDF p. 127). Definition 3.2.23: p. 109. Definition 3.2.22: p. 108 (PDF p. 126). -/
theorem central_limit_finite_variance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ) (hv : 0 < var μ (X 0)) :
   CD μ (fun n ω => Real.sqrt n*(sampleMean X n ω-mean μ (X 0)))
     (gaussianReal 0 ⟨var μ (X 0),le_of_lt hv⟩) := by
  
  let v : ℝ≥0 := ⟨var μ (X 0),le_of_lt hv⟩
  let ν := gaussianReal 0 v
  have hv0 : v≠0 := by
    intro h
    have he := congrArg (fun a : ℝ≥0 => (a : ℝ)) h
    change var μ (X 0)=0 at he
    linarith
  letI : NullSingletonClass ν := nullSingletonClass_gaussianReal hv0
  have hv' : (variance (X 0) μ).toNNReal=v := by
    apply Subtype.ext
    simp [v,var,Real.toNNReal_of_nonneg (le_of_lt hv)]
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (P := μ) (P' := ν) (Y := id)
    (by simpa only [hv'] using (HasLaw.id : HasLaw id ν ν))
    h2 hiid.2.1 hiid.2.2
  have he (n : ℕ) (ω : Ω) :
      (Real.sqrt n)⁻¹*((∑ k∈Finset.range n,X k ω)-(n : ℝ)*(∫ z,X 0 z ∂μ))=
      Real.sqrt n*(sampleMean X n ω-mean μ (X 0)) := by
    by_cases hn : n=0
    · simp [hn,sampleMean]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hs : Real.sqrt (n : ℝ)≠0 := (Real.sqrt_pos.2 hnR).ne'
      unfold sampleMean mean
      rw [← Real.sqrt_div_self]
      field_simp [ne_of_gt hnR] <;> ring
  have ht := hclt.tendsto
  simp only [Measure.map_id] at ht
  intro x hx
  have hboundary : ν (frontier (Set.Iic x))=0 := by simp [frontier_Iic]
  have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' ht hboundary
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top ν (Set.Iic x))).comp hp
  have hmap (n : ℕ) :
      (μ.map (fun ω => (Real.sqrt n)⁻¹*
        ((∑ k∈Finset.range n,X k ω)-(n : ℝ)*(∫ z,X 0 z ∂μ)))) (Set.Iic x)=
      μ {ω | Real.sqrt n*(sampleMean X n ω-mean μ (X 0)) ≤ x} := by
    rw [Measure.map_apply_of_aemeasurable (hclt.forall_aemeasurable n) measurableSet_Iic]
    congr 1
    ext ω
    simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_setOf_eq,he]
  change Tendsto (fun (n : ℕ) =>
      ((μ.map (fun ω => (Real.sqrt n)⁻¹*
        ((∑ k∈Finset.range n,X k ω)-(n : ℝ)*(∫ z,X 0 z ∂μ)))) (Set.Iic x)).toReal)
      atTop (nhds ((ν (Set.Iic x)).toReal)) at hreal
  simpa only [hmap,cdf,AronowAudit.P001.prob] using hreal


theorem pdf_closed_interval_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (f : ℝ → ℝ) (hf : HasPDF (μ.map X) f) (a b : ℝ) (hab : a≤b) :
    prob μ {ω | X ω∈Set.Icc a b}=cdf μ X b-cdf μ X a := by
  let ν := μ.map X
  letI : NullSingletonClass ν := by
    dsimp [ν]
    rw [hf.2.2.2]
    infer_instance
  have hmap (s : Set ℝ) (hs : MeasurableSet s) :
      ν.real s=prob μ {ω | X ω∈s} := by
    dsimp [ν,measureReal_def,prob]
    rw [Measure.map_apply hX hs]
    rfl
  have he : Set.Iic b \ Set.Iic a=Set.Ioc a b := by
    ext t
    simp only [Set.mem_sdiff,Set.mem_Iic,Set.mem_Ioc,not_le]
    tauto
  rw [← hmap _ measurableSet_Icc,← measureReal_congr (μ:=ν) Ioc_ae_eq_Icc,
    ← he,measureReal_sdiff (Set.Iic_subset_Iic.mpr hab) measurableSet_Iic,
    hmap _ measurableSet_Iic,hmap _ measurableSet_Iic]
  rfl

theorem iid_indicator_sample_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X)
    (A : Set ℝ) (hA : MeasurableSet A) (n : ℕ) (hn : 0<n) :
    let Z := fun i ω => A.indicator (fun _ => (1:ℝ)) (X i ω)
    let q := prob μ {ω | X 0 ω∈A}
    mean μ (sampleMean Z n)=q ∧ var μ (sampleMean Z n)=q*(1-q)/(n:ℝ) := by
  classical
  let g := A.indicator (fun _ : ℝ => (1:ℝ))
  let Z := fun i ω => g (X i ω)
  have hg : Measurable g := measurable_const.indicator hA
  have hZ : IID μ Z := ⟨fun i => hg.comp (hiid.1 i),
    hiid.2.1.comp (fun _ => g) (fun _ => hg),fun i => (hiid.2.2 i).comp hg⟩
  have h2 : MemLp (Z 0) 2 μ := MemLp.of_bound (hZ.1 0).aestronglyMeasurable 1
    (ae_of_all _ (by intro ω; by_cases hh : X 0 ω∈A <;> simp [Z,g,Set.indicator,hh]))
  have hm : mean μ (Z 0)=prob μ {ω | X 0 ω∈A} := by
    change (∫ ω, {ω | X 0 ω∈A}.indicator (fun _ => (1:ℝ)) ω ∂μ)=_
    have hset : MeasurableSet {ω | X 0 ω∈A} := hA.preimage (hiid.1 0)
    rw [integral_indicator hset]
    simp [prob,Measure.real]
  have hs : (∫ ω,(Z 0 ω)^2 ∂μ)=mean μ (Z 0) := by
    apply integral_congr_ae
    exact ae_of_all _ (by intro ω; by_cases hh : X 0 ω∈A <;> simp [Z,g,Set.indicator,hh])
  have hv : var μ (Z 0)=prob μ {ω | X 0 ω∈A}*(1-prob μ {ω | X 0 ω∈A}) := by
    rw [var,variance_eq_sub h2]
    change (∫ ω,(Z 0 ω)^2 ∂μ)-(mean μ (Z 0))^2=_
    rw [hs,hm]
    ring
  simpa only [Z,g,hm,hv] using iid_sample_mean_finite_moments μ Z hZ h2 n hn

theorem rectangular_kernel_moments_core {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X)
    (f : ℝ → ℝ) (hf : HasPDF (μ.map (X 0)) f) (n : ℕ) (hn : 0<n)
    (h : ℝ) (hh : 0<h) (x : ℝ) :
    let p := cdf μ (X 0) (x+h)-cdf μ (X 0) (x-h)
    mean μ (fun ω => kernelDensity rectangleKernel h (firstSample X n ω) x)=p/(2*h) ∧
    var μ (fun ω => kernelDensity rectangleKernel h (firstSample X n ω) x)=
      p*(1-p)/(4*h^2*(n:ℝ)) := by
  classical
  let A := Set.Icc (x-h) (x+h)
  let g := A.indicator (fun _ : ℝ => (1:ℝ))
  let Z := fun i ω => g (X i ω)
  have hi (t : ℝ) : rectangleKernel ((x-t)/h)/h=g t/(2*h) := by
    have he : |(x-t)/h|≤1 ↔ t∈A := by
      rw [abs_le]
      constructor
      · rintro ⟨hl,hu⟩
        exact ⟨by have hh' := (div_le_iff₀ hh).mp hu; linarith,
          by have hh' := (le_div_iff₀ hh).mp hl; linarith⟩
      · rintro ⟨hl,hu⟩
        exact ⟨(le_div_iff₀ hh).mpr (by linarith),(div_le_iff₀ hh).mpr (by linarith)⟩
    by_cases ht : t∈A <;> simp [rectangleKernel,g,Set.indicator,he,ht]
    <;> ring
  have he : (fun ω => kernelDensity rectangleKernel h (firstSample X n ω) x)=
      fun ω => sampleMean Z n ω/(2*h) := by
    funext ω
    unfold kernelDensity firstSample sampleMean
    simp_rw [hi]
    rw [← Finset.sum_div]
    rw [Fin.sum_univ_eq_sum_range (fun i => g (X i ω)) n]
    dsimp [Z]
    ring
  have hp : prob μ {ω | X 0 ω∈A}=cdf μ (X 0) (x+h)-cdf μ (X 0) (x-h) :=
    pdf_closed_interval_probability μ (X 0) (hiid.1 0) f hf _ _ (by linarith)
  have hm := iid_indicator_sample_moments μ X hiid A measurableSet_Icc n hn
  change mean μ (sampleMean Z n)=_ ∧ var μ (sampleMean Z n)=_ at hm
  rw [hp] at hm
  constructor
  · rw [he,mean,integral_div]
    exact congrArg (fun z => z/(2*h)) hm.1
  · rw [he,var]
    simp only [div_eq_mul_inv]
    rw [variance_mul_const]
    change var μ (sampleMean Z n)*(2*h)⁻¹^2=_
    rw [hm.2]
    ring

theorem continuous_pdf_cdf_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (f : ℝ → ℝ) (hf : HasPDF (μ.map X) f) (hc : Continuous f) (x : ℝ) :
    HasDerivAt (cdf μ X) (f x) x := by
  have hF (t : ℝ) : cdf μ X t=∫ u in Set.Iic t,f u := by
    change (μ (X ⁻¹' Set.Iic t)).toReal=_
    rw [← Measure.map_apply hX measurableSet_Iic,hf.2.2.2,
      withDensity_apply _ measurableSet_Iic,
      ← ofReal_integral_eq_lintegral_ofReal hf.2.2.1.integrableOn (ae_of_all _ hf.2.1)]
    exact ENNReal.toReal_ofReal (integral_nonneg hf.2.1)
  have he : cdf μ X=(fun t => (∫ u in Set.Iic 0,f u)+∫ u in (0:ℝ)..t,f u) := by
    funext t
    rw [hF]
    have hh := intervalIntegral.integral_Iic_sub_Iic (a:=(0:ℝ)) (b:=t)
      hf.2.2.1.integrableOn hf.2.2.1.integrableOn
    linarith
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _

theorem symmetric_difference_quotient_tendsto (F : ℝ → ℝ) (x d : ℝ)
    (hd : HasDerivAt F d x) (h : ℕ → ℝ) (hp : ∀ n,0<h n)
    (hz : Tendsto h atTop (nhds 0)) :
    Tendsto (fun n => (F (x+h n)-F (x-h n))/(2*h n)) atTop (nhds d) := by
  have ht : Tendsto h atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz,Eventually.of_forall hp⟩
  have htn : Tendsto (fun n => -h n) atTop (nhdsWithin 0 (Set.Iio 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using hz.neg,
      Eventually.of_forall (fun n => neg_neg_of_pos (hp n))⟩
  have hr := hd.tendsto_slope_zero_right.comp ht
  have hl := hd.tendsto_slope_zero_left.comp htn
  have hh := (hr.add hl).div_const 2
  convert hh using 1
  · funext n
    simp only [Function.comp_def,smul_eq_mul]
    field_simp [(hp n).ne']
    <;> ring
  · ring

theorem probability_convergence_from_mean_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ)
    (h2 : ∀ n,MemLp (Z n) 2 μ) (m v : ℕ → ℝ) (c : ℝ)
    (hm : ∀ n,0<n → mean μ (Z n)=m n) (hv : ∀ n,0<n → var μ (Z n)=v n)
    (hmlim : Tendsto m atTop (nhds c)) (hvlim : Tendsto v atTop (nhds 0)) : CP μ Z c := by
  intro ε hε
  have hε2 : 0<ε/2 := by linarith
  have hmb : ∀ᶠ n in atTop, |m n-c|<ε/2 := by
    apply eventually_atTop.2
    simpa only [Real.dist_eq] using (Metric.tendsto_atTop.mp hmlim) (ε/2) hε2
  have hupper : ∀ᶠ n in atTop,
      prob μ {ω | ε≤dist (Z n ω) c}≤v n/(ε/2)^2 := by
    filter_upwards [eventually_gt_atTop (0:ℕ),hmb] with n hn hmn
    have hb := chebyshev_probability μ (Z n) (h2 n) (ε/2) hε2
    rw [hm n hn,hv n hn] at hb
    calc
      _ ≤ prob μ {ω | ε/2≤|Z n ω-m n|} := by
        apply measureReal_mono _ (measure_ne_top μ _)
        intro ω hω
        change ε≤|Z n ω-c| at hω
        have ht : |Z n ω-c|≤|Z n ω-m n|+|m n-c| := by
          calc
            _ = |(Z n ω-m n)+(m n-c)| := by congr 1;ring
            _ ≤ _ := abs_add_le _ _
        change ε/2≤|Z n ω-m n|
        linarith
      _ ≤ _ := hb
  have hl : Tendsto (fun n => v n/(ε/2)^2) atTop (nhds 0) := by
    simpa only [zero_div] using hvlim.div_const ((ε/2)^2)
  exact squeeze_zero' (Eventually.of_forall (fun n => ENNReal.toReal_nonneg)) hupper hl

theorem rectangular_kernel_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ i,Measurable (X i)) (n : ℕ) (h x : ℝ) :
    MemLp (fun ω => kernelDensity rectangleKernel h (firstSample X n ω) x) 2 μ := by
  have habs : Measurable (fun t : ℝ => |t|) := by
    simpa [Real.norm_eq_abs] using (measurable_id.norm : Measurable (fun t : ℝ => ‖t‖))
  have hg : Measurable rectangleKernel :=
    measurable_const.piecewise (measurableSet_le habs measurable_const) measurable_const
  have hi (i : Fin n) : MemLp (fun ω => rectangleKernel ((x-X i ω)/h)/h) 2 μ := by
    have hk : MemLp (fun ω => rectangleKernel ((x-X i ω)/h)) 2 μ :=
      MemLp.of_bound (hg.comp ((measurable_const.sub (hm i)).div_const h)).aestronglyMeasurable (1/2)
        (ae_of_all _ (by intro ω; dsimp [rectangleKernel];split_ifs <;> norm_num))
    simpa only [div_eq_mul_inv,mul_comm] using hk.const_mul h⁻¹
  have hs := memLp_finsetSum Finset.univ (fun i _ => hi i)
  simpa only [kernelDensity,firstSample,div_eq_mul_inv,mul_comm] using hs.const_mul (n:ℝ)⁻¹

/-- For a population density continuous on ℝ, the rectangular kernel estimator is consistent at every real point if the positive bandwidths h tend to zero and n*h tends to infinity.
Target P001-T127: Theorem 3.3.8 (Consistency of the Kernel Density Estimator, Rectangular Kernel).
Location: p. 122 (PDF p. 140); proof sketch on p. 123 (PDF p. 141); the continuity condition is stated on p. 121 (PDF p. 139). -/
theorem rectangular_kernel_consistency {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (f : ℝ → ℝ) (hf : HasPDF (μ.map (X 0)) f)
   (hc : Continuous f) (h : ℕ → ℝ) (hpos : ∀ n,0 < h n)
   (hzero : Tendsto h atTop (nhds 0)) (hninf : Tendsto (fun (n : ℕ) => (n : ℝ)*h n) atTop atTop) :
   ∀ x : ℝ, CP μ (fun n ω => kernelDensity rectangleKernel (h n) (firstSample X n ω) x) (f x) := by
  intro x
  let Z := fun n ω => kernelDensity rectangleKernel (h n) (firstSample X n ω) x
  let p := fun n => cdf μ (X 0) (x+h n)-cdf μ (X 0) (x-h n)
  let m := fun n => p n/(2*h n)
  let v := fun n => p n*(1-p n)/(4*(h n)^2*(n:ℝ))
  have hmlim : Tendsto m atTop (nhds (f x)) :=
    symmetric_difference_quotient_tendsto (cdf μ (X 0)) x (f x)
      (continuous_pdf_cdf_hasDerivAt μ (X 0) (hiid.1 0) f hf hc x) h hpos hzero
  have hplim : Tendsto p atTop (nhds 0) := by
    have he : p=(fun n => 2*h n*m n) := by
      funext n
      dsimp [m]
      field_simp [(hpos n).ne']
    rw [he]
    simpa only [mul_zero,zero_mul] using (hzero.const_mul 2).mul hmlim
  have hvform (n : ℕ) : v n=(m n*(1-p n)/2)*((n:ℝ)*h n)⁻¹ := by
    by_cases hn : n=0
    · subst n
      simp [v]
    · have hnR : (n:ℝ)≠0 := by exact_mod_cast hn
      dsimp [v,m]
      field_simp [(hpos n).ne',hnR]
      <;> ring
  have hvlim : Tendsto v atTop (nhds 0) := by
    have hi : Tendsto (fun (n:ℕ) => ((n:ℝ)*h n)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hninf
    have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have hl := ((hmlim.mul (hone.sub hplim)).div_const 2).mul hi
    simp only [sub_zero,mul_one,mul_zero] at hl
    convert hl using 1
    funext n
    exact hvform n
  apply probability_convergence_from_mean_variance μ Z
    (fun n => rectangular_kernel_memLp μ X hiid.1 n (h n) x) m v (f x) _ _ hmlim hvlim
  · intro n hn
    exact (rectangular_kernel_moments_core μ X hiid f hf n hn (h n) (hpos n) x).1
  · intro n hn
    exact (rectangular_kernel_moments_core μ X hiid f hf n hn (h n) (hpos n) x).2

/-!
Two probability helpers for the normal-confidence-interval theorem.
The first adapts the continuous CDF squeeze from StatLean's `SteinMethod` module
(Apache-2.0); see NOTICE at the repository root.
The interval helper works directly with the book's CDF-convergence definition;
it derives probability bounds on the good random-width event.
-/
theorem continuous_squeeze_at_zero {G : ℕ → ℝ} {F : ℝ → ℝ}
    (hF : ContinuousAt F 0)
    (hb : ∀ ε > (0:ℝ), ∀ᶠ n in atTop, F (-ε)-ε ≤ G n ∧ G n ≤ F ε+ε) :
    Tendsto G atTop (nhds (F 0)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ,hδ,hδF⟩ := Metric.tendsto_nhds_nhds.mp hF (η/2) (by linarith)
  let ε := min (δ/2) (η/4)
  have he : 0 < ε := lt_min (by linarith) (by linarith)
  have hed : ε ≤ δ/2 := min_le_left _ _
  have heη : ε ≤ η/4 := min_le_right _ _
  have hl := hδF (show dist (-ε) 0 < δ by rw [Real.dist_eq,sub_zero,abs_neg,abs_of_pos he]; linarith)
  have hr := hδF (show dist ε 0 < δ by rw [Real.dist_eq,sub_zero,abs_of_pos he]; linarith)
  rw [Real.dist_eq, abs_lt] at hl hr
  filter_upwards [hb ε he] with n hn
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith [hn.1,hn.2]

theorem cd_cp_random_width_interval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z W : ℕ → Ω → ℝ)
    (hZ : ∀ n,Measurable (Z n)) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hCD : CD μ Z ν) (hF : Continuous (fun x => prob ν (Set.Iic x)))
    (w : ℝ) (hw : 0 < w) (hW : CP μ W w) :
    Tendsto (fun n => prob μ {ω | |Z n ω| < W n ω}) atTop
      (nhds (prob ν (Set.Iic w)-prob ν (Set.Iic (-w)))) := by
  let F := fun x => prob ν (Set.Iic x)
  let Ψ := fun e => F (w+e)-F (-w-e)
  have hFc : Continuous F := hF
  have hFm : Monotone F := by
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (Set.Iic_subset_Iic.mpr hab))
  have hΨ : Continuous Ψ := by dsimp [Ψ]; fun_prop
  have hIoc (n : ℕ) (a b : ℝ) (hab : a ≤ b) :
      prob μ {ω | a < Z n ω ∧ Z n ω ≤ b} = cdf μ (Z n) b-cdf μ (Z n) a := by
    have he : {ω | a < Z n ω ∧ Z n ω ≤ b} = {ω | Z n ω ≤ b} \ {ω | Z n ω ≤ a} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_le, and_comm]
    rw [he]
    exact measureReal_sdiff (μ := μ) (fun ω hω => hω.trans hab)
      ((measurableSet_Iic : MeasurableSet (Set.Iic a)).preimage (hZ n))
  have hlim (a b : ℝ) : Tendsto (fun n => cdf μ (Z n) b-cdf μ (Z n) a)
      atTop (nhds (F b-F a)) :=
    (hCD b hF.continuousAt).sub (hCD a hF.continuousAt)
  have hg : Tendsto (fun n => prob μ {ω | |Z n ω| < W n ω}) atTop (nhds (Ψ 0)) := by
    apply continuous_squeeze_at_zero hΨ.continuousAt
    intro ε hε
    let Bad := fun n => {ω | ε/2 ≤ dist (W n ω) w}
    have hb : Tendsto (fun n => prob μ (Bad n)) atTop (nhds 0) := hW (ε/2) (by linarith)
    have hupper (n : ℕ) : prob μ {ω | |Z n ω| < W n ω} ≤
        (cdf μ (Z n) (w+ε)-cdf μ (Z n) (-w-ε)) + prob μ (Bad n) := by
      have hsub : {ω | |Z n ω| < W n ω} ⊆
          {ω | -w-ε < Z n ω ∧ Z n ω ≤ w+ε} ∪ Bad n := by
        intro ω hω
        by_cases hd : ε/2 ≤ dist (W n ω) w
        · exact Or.inr hd
        · apply Or.inl
          have hd' : dist (W n ω) w < ε/2 := lt_of_not_ge hd
          rw [Real.dist_eq,abs_lt] at hd'
          change |Z n ω| < W n ω at hω
          rw [abs_lt] at hω
          change -w-ε < Z n ω ∧ Z n ω ≤ w+ε
          constructor <;> linarith [hω.1,hω.2,hd'.1,hd'.2]
      have hle := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
      rw [show μ.real {ω | -w-ε < Z n ω ∧ Z n ω ≤ w+ε} =
        cdf μ (Z n) (w+ε)-cdf μ (Z n) (-w-ε) from hIoc n _ _ (by linarith)] at hle
      exact hle
    have hlow : ∀ᶠ n in atTop, Ψ (-ε)-ε ≤ prob μ {ω | |Z n ω| < W n ω} := by
      by_cases hsmall : ε < w
      · have hlower (n : ℕ) : cdf μ (Z n) (w-ε)-cdf μ (Z n) (-w+ε) ≤
            prob μ {ω | |Z n ω| < W n ω} + prob μ (Bad n) := by
          have hsub : {ω | -w+ε < Z n ω ∧ Z n ω ≤ w-ε} ⊆
              {ω | |Z n ω| < W n ω} ∪ Bad n := by
            intro ω hω
            by_cases hd : ε/2 ≤ dist (W n ω) w
            · exact Or.inr hd
            · apply Or.inl
              have hd' : dist (W n ω) w < ε/2 := lt_of_not_ge hd
              rw [Real.dist_eq,abs_lt] at hd'
              change |Z n ω| < W n ω
              rw [abs_lt]
              change -w+ε < Z n ω ∧ Z n ω ≤ w-ε at hω
              constructor <;> linarith [hω.1,hω.2,hd'.1,hd'.2]
          have hle := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
          rw [show μ.real {ω | -w+ε < Z n ω ∧ Z n ω ≤ w-ε} =
            cdf μ (Z n) (w-ε)-cdf μ (Z n) (-w+ε) from hIoc n _ _ (by linarith)] at hle
          exact hle
        have hl := (hlim (-w+ε) (w-ε)).eventually
          (eventually_gt_nhds (show F (w-ε)-F (-w+ε)-ε/2 < F (w-ε)-F (-w+ε) by linarith))
        have hbad := hb.eventually (eventually_lt_nhds (show (0:ℝ) < ε/2 by linarith))
        filter_upwards [hl,hbad] with n hn hbn
        have hbound := hlower n
        dsimp [Ψ]
        rw [sub_neg_eq_add]
        change F (w-ε)-F (-w+ε)-ε ≤ _
        linarith
      · have hΨneg : Ψ (-ε) ≤ 0 := by
          dsimp [Ψ]
          have hm := hFm (show w + -ε ≤ -w - -ε by linarith)
          linarith
        filter_upwards [] with n
        have hnonneg : 0 ≤ prob μ {ω | |Z n ω| < W n ω} := ENNReal.toReal_nonneg
        linarith
    have hu := (hlim (-w-ε) (w+ε)).eventually
      (eventually_lt_nhds (show F (w+ε)-F (-w-ε) < F (w+ε)-F (-w-ε)+ε/2 by linarith))
    have hbad := hb.eventually (eventually_lt_nhds (show (0:ℝ) < ε/2 by linarith))
    filter_upwards [hlow,hu,hbad] with n hln hun hbn
    refine ⟨hln,?_⟩
    have hbound := hupper n
    dsimp [Ψ]
    linarith
  simpa [Ψ,F] using hg

/-- An asymptotically normal estimator with a consistent nonnegative sampling-variance estimator has an asymptotically valid open normal confidence interval using the standard normal quantile.
Target P001-T128: Theorem 3.4.2 (Normal Approximation–Based Confidence Interval).
Location: p. 125 (PDF p. 143); proof on pp. 125–126 (PDF pp. 143–144). Definition 3.4.1: p. 124 (PDF p. 142). -/
theorem normal_approximation_confidence_interval {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (that vhat : ℕ → Ω → ℝ) (hthat : ∀ n,Measurable (that n)) (hvhat : ∀ n,Measurable (vhat n))
   (hpos : ∀ n ω,0 ≤ vhat n ω) (θ φ α z : ℝ) (hφ : 0 < φ) (hα : α∈Set.Ioo (0 : ℝ) 1)
   (hz : prob (gaussianReal 0 1) (Set.Iic z)=1-α/2)
   (hAN : CD μ (fun n ω => Real.sqrt n*(that n ω-θ)) (gaussianReal 0 ⟨φ^2,sq_nonneg _⟩))
   (hVC : VarianceConsistent μ vhat (φ^2)) :
   ∃ c : ℝ,1-α ≤ c ∧ Tendsto (fun (n : ℕ) => prob μ {ω | θ∈Set.Ioo
     (that n ω-z*Real.sqrt (vhat n ω)) (that n ω+z*Real.sqrt (vhat n ω))}) atTop (nhds c) := by
  let ν := gaussianReal 0 (NNReal.mk (φ^2) (sq_nonneg φ))
  let F := fun x => prob ν (Set.Iic x)
  have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hv : (NNReal.mk (φ^2) (sq_nonneg φ) : ℝ≥0) ≠ 0 := by
    intro hh
    have hc := congrArg (fun x : ℝ≥0 => (x:ℝ)) hh
    have hp := sq_pos_of_pos hφ
    change φ^2 = 0 at hc
    linarith
  have : NullSingletonClass ν := nullSingletonClass_gaussianReal hv
  have hF : Continuous F := by
    have he : F = ProbabilityTheory.cdf ν := by
      funext x
      exact (ProbabilityTheory.cdf_eq_real ν x).symm
    rw [he]
    exact continuous_iff_continuousAt.mpr (fun x => AronowAudit.P053.NormalCompletion.cdf_continuousAt ν x)
  have hz' : ProbabilityTheory.cdf (gaussianReal 0 1) z=1-α/2 := by
    simpa only [ProbabilityTheory.cdf_eq_real,measureReal_def,prob] using hz
  have hzp : 0 < z := by
    apply AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.lt_iff_lt.mp
    rw [AronowAudit.P053.NormalCompletion.normal_cdf_zero,hz']
    linarith [hα.1,hα.2]
  have hscale : (gaussianReal 0 1).map (fun x : ℝ => φ*x)=ν := by
    convert (gaussianReal_const_mul
      (HasLaw.id : HasLaw id (gaussianReal 0 1) (gaussianReal 0 1)) φ).map_eq using 1 <;>
      simp [ν]
  have hscaled (t : ℝ) : F (φ*t)=prob (gaussianReal 0 1) (Set.Iic t) := by
    dsimp [F]
    unfold prob
    rw [← hscale,Measure.map_apply (by fun_prop) measurableSet_Iic]
    congr 2
    ext x
    simp only [Set.mem_preimage,Set.mem_Iic]
    exact mul_le_mul_iff_of_pos_left hφ
  have hmass : F (z*φ)-F (-(z*φ))=1-α := by
    rw [show z*φ=φ*z by ring,show -(φ*z)=φ*(-z) by ring,hscaled z,hscaled (-z)]
    have hn := AronowAudit.P053.NormalCompletion.normal_cdf_neg z
    rw [ProbabilityTheory.cdf_eq_real,ProbabilityTheory.cdf_eq_real] at hn
    change prob (gaussianReal 0 1) (Set.Iic (-z))=1-prob (gaussianReal 0 1) (Set.Iic z) at hn
    linarith
  have hse := (variance_se_consistency_equivalence μ vhat hpos (φ^2) (sq_nonneg φ)).mp hVC
  change CP μ (fun n ω => Real.sqrt n*Real.sqrt (vhat n ω)) (Real.sqrt (φ^2)) at hse
  rw [Real.sqrt_sq_eq_abs,abs_of_pos hφ] at hse
  have hwid := probability_convergence_continuous_at μ
    (fun n ω => Real.sqrt n*Real.sqrt (vhat n ω)) φ (fun x : ℝ => z*x) hse (by fun_prop)
  change CD μ (fun n ω => Real.sqrt n*(that n ω-θ)) ν at hAN
  have hlim := cd_cp_random_width_interval μ
    (fun n ω => Real.sqrt n*(that n ω-θ))
    (fun n ω => z*(Real.sqrt n*Real.sqrt (vhat n ω)))
    (fun n => by fun_prop) ν hAN hF (z*φ) (mul_pos hzp hφ) hwid
  change Tendsto _ atTop (nhds (F (z*φ)-F (-(z*φ)))) at hlim
  rw [hmass] at hlim
  refine ⟨1-α,le_rfl,?_⟩
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  congr 1
  ext ω
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hs : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnR
  have he : θ ∈ Set.Ioo (that n ω-z*Real.sqrt (vhat n ω)) (that n ω+z*Real.sqrt (vhat n ω)) ↔
      |that n ω-θ| < z*Real.sqrt (vhat n ω) := by
    rw [Set.mem_Ioo,abs_lt]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [Set.mem_ofPred_eq,Set.mem_ofPred_eq,he,abs_mul,abs_of_pos hs,
    show z*(Real.sqrt n*Real.sqrt (vhat n ω)) = Real.sqrt n*(z*Real.sqrt (vhat n ω)) by ring,
    mul_lt_mul_iff_of_pos_left hs]

/-- On a compact parameter space, a continuous uniquely maximized population expected log likelihood and uniform sample log-likelihood convergence give consistency of every sample maximizer.
Target P001-T129: Theorem 5.2.6 (Consistency of the Maximum Likelihood Estimator) and the lemma in its proof sketch.
Location: Theorem 5.2.6: p. 193 (PDF p. 211). Proof sketch: pp. 193–194 (PDF pp. 211–212). -/
theorem ml_consistency_explicit_uniform_regularities_supporting {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {τ : ℕ} (Θ : Set (Fin τ → ℝ)) (hc : IsCompact Θ) (θ : Fin τ → ℝ) (hθ : θ∈Θ)
   (M : (Fin τ → ℝ) → ℝ) (hM : ContinuousOn M Θ)
   (hunique : ∀ t∈Θ,M t ≤ M θ ∧ (M t=M θ → t=θ))
   (L : ℕ → Ω → (Fin τ → ℝ) → ℝ) (that : ℕ → Ω → Fin τ → ℝ)
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → L n ω t ≤ L n ω (that n ω))
   (Δ : ℕ → Ω → ℝ) (herr : ∀ n ω t,t∈Θ → |L n ω t-M t| ≤ Δ n ω)
   (hlim : CP μ Δ 0) : CP μ that θ := by
  
  have hsep := compact_unique_maximum_separated Θ hc θ hθ M hM hunique
  have hz : CP μ (fun _ _ => (0 : ℝ)) 0 := by
    intro ε hε
    have hempty : {ω : Ω | ε ≤ dist (0 : ℝ) 0}=∅ := by
      ext ω
      simp only [dist_self,Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      exact not_le_of_gt hε
    simpa only [hempty,AronowAudit.P001.prob,measure_empty,ENNReal.toReal_zero]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  exact separated_argmax_consistency μ Θ M L that θ hθ hthat Δ (fun _ _ => 0)
    herr (by simpa using hmax) hsep hlim hz









/-- Two functions of X are equal as random variables exactly when they agree on X(Ω).
Target P001-T33: Theorem 1.3.2 (Equality of Functions of a Random Variable), with the functions named consistently.
Location: p. 32 (PDF p. 50). Definition 1.3.1: p. 31 (PDF p. 49). Definition 1.2.2: p. 16 (PDF p. 34). -/
theorem functions_equal_on_range {Ω : Type*} (X : Ω → ℝ) (g h : ℝ → ℝ) :
   g ∘ X = h ∘ X ↔ ∀ x ∈ Set.range X, g x = h x := by
  constructor
  · intro e x hx
    obtain ⟨ω, rfl⟩ := hx
    exact congrFun e ω
  · intro e
    funext ω
    exact e (X ω) ⟨ω, rfl⟩

/-- Set subtraction equals intersection with the complement of the subtracted set.
Target P001-T101: Glossary of Mathematical Notation, the row for set subtraction ($\backslash$): the relative-complement identity, corrected ($A\backslash B = A \cap B^C$).
Location: p. 283 (PDF p. 301), row '$\backslash$' (Set subtraction); the rows for $A^C$, $\cup$ and $\cap$ on the same page. -/
theorem relative_complement {Ω : Type*} (A B : Set Ω) : A \ B = A ∩ Bᶜ := by
  rfl

/-- A deterministic potential-outcome pair is conditionally independent of treatment on any finite probability space.
Target P001-T99: Section 7.3.1, the sentence 'the estimand $\mathrm{E}[p_D(\mathbf{X}_i)\tau_i]$ ... is equivalent to the average treatment effect on the treated (ATT), $\mathrm{E}[\tau_i|D_i = 1]$', as printed.
Location: p. 273 (PDF p. 291), Section 7.3.1, second paragraph. -/
theorem constant_potential_ignorability_finite {n : ℕ} {E F G : Type*} (P : FiniteLaw n) (y0 : E) (D : Fin n → F) (X : Fin n → G) :
   FCondIndep P (fun _ => y0) D X := by
  intro x y z hx
  by_cases hy : y0=y
  · simp [fprob,hy,mul_comm]
  · simp [fprob,hy]

/-- The two-atom design has strong ignorability, propensity 1/4 strictly between zero and one, ATT one, and the printed unnormalized expression 1/4.
Target P001-T99: Section 7.3.1, the sentence 'the estimand $\mathrm{E}[p_D(\mathbf{X}_i)\tau_i]$ ... is equivalent to the average treatment effect on the treated (ATT), $\mathrm{E}[\tau_i|D_i = 1]$', as printed.
Location: p. 273 (PDF p. 291), Section 7.3.1, second paragraph. -/
theorem att_counterexample_with_ignorability : FCondIndep attWitness (fun _ => ((0 : ℝ), (1 : ℝ))) (![0,1] : Fin 2 → ℝ) (fun _ => (0 : ℝ)) ∧
   fcond attWitness (![0,1] : Fin 2 → ℝ) (fun _ => 0) 0=1/4 ∧
   (1/8 : ℝ) < 1/4 ∧ (1/4 : ℝ) < 1-1/8 ∧
   fcond attWitness (fun _ => 1) (![0,1] : Fin 2 → ℝ) 1=1 ∧
   fmean attWitness (fun _ => (1/4 : ℝ)*(1-0))=1/4 ∧
   fmean attWitness (fun _ => (1/4 : ℝ)*(1-0))≠
     fcond attWitness (fun _ => 1-0) (![0,1] : Fin 2 → ℝ) 1 := by
  refine ⟨constant_potential_ignorability_finite attWitness (0,1) ![0,1] (fun _ => 0), ?_⟩
  norm_num [fmean,fcond,fprob,attWitness,Fin.sum_univ_succ]

/-- In the explicit electorate design, treatment positivity holds while the pair of potential outcomes fails conditional independence given the constant description.
Target P001-T21: Section 7.5, the claim that if the coded applicant descriptions account for all the information presented to voters then 'by definition, $D_i$ must be conditionally independent of potential outcomes', as printed.
Location: p. 278 (PDF p. 296), paragraph beginning 'The fact that random assignment is unlikely to hold'; the application's setting: pp. 276–278 (PDF pp. 294–296). -/
theorem electorate_potential_outcomes_not_cia_supporting : fcond binaryJoint electorateD (fun _ => 0) 0=1/2 ∧
   ¬ FCondIndep binaryJoint (fun i => (electorateOutcome 0 i,electorateOutcome 1 i))
     electorateD (fun _ => (0 : ℝ)) := by
  constructor
  · norm_num [fcond,fprob,binaryJoint,electorateD,Fin.sum_univ_succ]
  · intro h
    have he := h 0 (60,65) 1 (by norm_num [fprob,binaryJoint,Fin.sum_univ_succ])
    norm_num [fprob,binaryJoint,electorateOutcome,electorateU,electorateD,Fin.sum_univ_succ] at he

/-- The constant functional seven is Hadamard differentiable on CDFs in Kolmogorov distance, in every bounded sup-norm direction, with the zero derivative.
Target P001-T56: Theorem 3.3.6 (Asymptotic Normality of Plug-In Estimators), as printed, read with footnote 31 and Definition 3.2.28.
Location: p. 120 (PDF p. 138), Theorem 3.3.6 and footnote 31. Definition 3.2.28: p. 112 (PDF p. 130). -/
theorem constant_cdf_functional_hadamard (F : ℝ → ℝ) : CDFHadamard (fun _ => (7 : ℝ)) F := by
  refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro f g; simp
  · intro a f; simp
  · refine ⟨0, le_rfl, ?_⟩
    intro h hh; simp
  · intro h hh t hn ht hbn htlim hhlim hvalid
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

/-- The normalized three-point design has correlations one and minus one and almost-sure affine equalities, but each pointwise affine equality is impossible.
Target P001-T41: Theorem 2.2.6 (Correlation and Linear Dependence), second and third bullets, as printed.
Location: p. 63 (PDF p. 81), Theorem 2.2.6. Definition 2.2.5: p. 62 (PDF p. 80). Definition 1.3.1: p. 31 (PDF p. 49). -/
theorem finite_correlation_counterexample_full : fcorrelation nullPointLaw ![0,1,0] ![0,1,1]=1 ∧
   fcorrelation nullPointLaw ![0,1,0] ![1,0,0]= -1 ∧
   fvar nullPointLaw ![0,1,0] > 0 ∧ fvar nullPointLaw ![0,1,1] > 0 ∧ fvar nullPointLaw ![1,0,0] > 0 ∧
   fprob nullPointLaw (fun i => (![0,1,1] : Fin 3 → ℝ) i=(![0,1,0] : Fin 3 → ℝ) i)=1 ∧
   fprob nullPointLaw (fun i => (![1,0,0] : Fin 3 → ℝ) i=1-(![0,1,0] : Fin 3 → ℝ) i)=1 ∧
   (¬ ∃ a b : ℝ,∀ i : Fin 3,(![0,1,1] : Fin 3 → ℝ) i=a+b*(![0,1,0] : Fin 3 → ℝ) i) ∧
   (¬ ∃ a b : ℝ,∀ i : Fin 3,(![1,0,0] : Fin 3 → ℝ) i=a-b*(![0,1,0] : Fin 3 → ℝ) i) := by
  rcases correlation_not_pointwise_dependence with ⟨hvX,hvY,hvZ,hcY,hcZ,hnY,hnZ⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hnY, hnZ⟩
  all_goals norm_num [fcorrelation, fvar, fcov, fmean, fprob, nullPointLaw, Fin.sum_univ_succ,
    Real.sqrt_div, Real.sqrt_sq_eq_abs]

/-- The six-unit observed design has nonsingular Gram matrix with determinant 7311, and its actual OLS coefficient vector is the stated rational vector.
Target P001-T92: Example 7.2.2 (Causal Inference with OLS Regression), the two imputation tables as printed (unit 3 with $X_{[1]i} = 9$) against the claim that both imputations give the same estimate.
Location: p. 259 (PDF p. 277), the data table and the two imputation tables. -/
theorem causal_example_ols_fit : IsUnit (causalDesign.transpose*causalDesign).det ∧
   olsCoef causalDesign causalExampleY=causalExampleBeta := by
  have hGram : causalDesign.transpose*causalDesign=
      (!![6,4,34,15;4,4,19,13;34,19,248,66;15,13,66,67] : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [causalDesign, causalExampleD, causalExampleX1, causalExampleX2,
        Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
  have hdet : (causalDesign.transpose*causalDesign).det=7311 := by
    rw [hGram]
    let A : Matrix (Fin 4) (Fin 4) ℝ := !![6,4,34,15;4,4,19,13;34,19,248,66;15,13,66,67]
    have hm (j : Fin 4) : A.submatrix Fin.succ j.succAbove=
        (![!![4,19,13;19,248,66;13,66,67],
           !![4,19,13;34,248,66;15,66,67],
           !![4,4,13;34,19,66;15,13,67],
           !![4,4,19;34,19,248;15,13,66]] : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ) j := by
      fin_cases j <;> ext i k <;> fin_cases i <;> fin_cases k <;> rfl
    change A.det=7311
    rw [Matrix.det_succ_row_zero]
    simp_rw [hm]
    norm_num [A,Fin.sum_univ_succ,Matrix.det_fin_three]
  have hu : IsUnit (causalDesign.transpose*causalDesign).det := by
    rw [isUnit_iff_ne_zero, hdet]
    norm_num
  have he : (causalDesign.transpose*causalDesign).mulVec causalExampleBeta=
      causalDesign.transpose.mulVec causalExampleY := by
    ext i
    fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
      causalDesign, causalExampleD, causalExampleX1, causalExampleX2, causalExampleY,
      causalExampleBeta, Fin.sum_univ_succ]
  refine ⟨hu, ?_⟩
  unfold olsCoef
  rw [← he, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/-- The nonsingular observed-data OLS fit makes the misprinted imputation table disagree with the treatment coefficient, whereas the corrected table agrees.
Target P001-T92: Example 7.2.2 (Causal Inference with OLS Regression), the two imputation tables as printed (unit 3 with $X_{[1]i} = 9$) against the claim that both imputations give the same estimate.
Location: p. 259 (PDF p. 277), the data table and the two imputation tables. -/
theorem misprinted_imputation_counterexample_full : IsUnit (causalDesign.transpose*causalDesign).det ∧
   causalPartialImpute ![1,8,9,3,5,7]≠olsCoef causalDesign causalExampleY 1 ∧
   causalPartialImpute causalExampleX1=olsCoef causalDesign causalExampleY 1 := by
  rcases causal_example_ols_fit with ⟨hu,hb⟩
  refine ⟨hu, ?_, ?_⟩
  · rw [hb]
    exact misprinted_imputation_table_disagreement.2.2.2
  · rw [hb]
    exact corrected_imputation_table_agreement.1


/-- Any measurable nonnegative function equal almost everywhere to a PDF is another PDF of the same law and has the same lower-tail integrals.
Target P001-T30: Definition 1.2.15 and the uniqueness sentence before it, corrected: the PDF is unique up to Lebesgue-almost-everywhere equality and equals $F'$ almost everywhere; the joint analogue (Definition 1.3.11).
Location: p. 24 (PDF p. 42), sentence after Definition 1.2.14; p. 25 (PDF p. 43), Definition 1.2.15 and Theorem 1.2.16; p. 36 (PDF p. 54), Definitions 1.3.10 and 1.3.11; p. 38 (PDF p. 56), Definition 1.3.16; p. 39 (PDF p. 57), Theorem 1.3.17. -/
theorem pdf_version_change (ν : Measure ℝ) [IsProbabilityMeasure ν] (f h : ℝ → ℝ)
   (hf : HasPDF ν f) (hh : AEMeasurable h volume) (hpos : ∀ x,0 ≤ h x) (heq : h=ᵐ[volume] f) :
   HasPDF ν h ∧ ∀ x : ℝ,prob ν (Set.Iic x)=∫ t in Set.Iic x,h t := by
  have hi : Integrable h volume := hf.2.2.1.congr heq.symm
  have hν : ν=volume.withDensity (fun x => ENNReal.ofReal (h x)) := by
    rw [hf.2.2.2]
    apply withDensity_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  refine ⟨⟨hh,hpos,hi,hν⟩,?_⟩
  intro x
  unfold prob
  rw [hν,withDensity_apply _ measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ hpos)]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun t => hpos t))

/-- A jointly continuous law is the product of its marginal laws exactly when its PDF equals the product of the marginal PDFs almost everywhere.
Target P001-T30: Definition 1.2.15 and the uniqueness sentence before it, corrected: the PDF is unique up to Lebesgue-almost-everywhere equality and equals $F'$ almost everywhere; the joint analogue (Definition 1.3.11).
Location: p. 24 (PDF p. 42), sentence after Definition 1.2.14; p. 25 (PDF p. 43), Definition 1.2.15 and Theorem 1.2.16; p. 36 (PDF p. 54), Definitions 1.3.10 and 1.3.11; p. 38 (PDF p. 56), Definition 1.3.16; p. 39 (PDF p. 57), Theorem 1.3.17. -/
theorem continuous_independence_density_ae (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (f : ℝ × ℝ → ℝ) (fx fy : ℝ → ℝ)
   (hf : HasJointPDF ν f) (hx : HasPDF (ν.map Prod.fst) fx) (hy : HasPDF (ν.map Prod.snd) fy) :
   ν=(ν.map Prod.fst).prod (ν.map Prod.snd) ↔ f=ᵐ[volume] (fun xy => fx xy.1*fy xy.2) := by
  have hprod : (ν.map Prod.fst).prod (ν.map Prod.snd) =
      volume.withDensity (fun xy : ℝ × ℝ => ENNReal.ofReal (fx xy.1 * fy xy.2)) := by
    rw [hx.2.2.2, hy.2.2.2, prod_withDensity₀ hx.1.ennreal_ofReal hy.1.ennreal_ofReal]
    congr 1
    funext xy
    exact (ENNReal.ofReal_mul (hx.2.1 xy.1)).symm
  rw [hprod, hf.2.2.2]
  have hxy : AEMeasurable (fun xy : ℝ × ℝ => ENNReal.ofReal (fx xy.1 * fy xy.2)) volume :=
    (hx.1.comp_fst.mul hy.1.comp_snd).ennreal_ofReal
  rw [withDensity_eq_iff_of_sigmaFinite hf.1.ennreal_ofReal hxy]
  constructor
  · intro h
    filter_upwards [h] with xy hxy
    exact (ENNReal.ofReal_eq_ofReal_iff (hf.2.1 xy)
      (mul_nonneg (hx.2.1 xy.1) (hy.2.1 xy.2))).mp hxy
  · intro h
    filter_upwards [h] with xy hxy
    rw [hxy]

/-- For independent uniforms, the CDF mixed derivative does not exist at (0,y) when 0<y<1.
Target P001-T30: Definition 1.2.15 and the uniqueness sentence before it, corrected: the PDF is unique up to Lebesgue-almost-everywhere equality and equals $F'$ almost everywhere; the joint analogue (Definition 1.3.11).
Location: p. 24 (PDF p. 42), sentence after Definition 1.2.14; p. 25 (PDF p. 43), Definition 1.2.15 and Theorem 1.2.16; p. 36 (PDF p. 54), Definitions 1.3.10 and 1.3.11; p. 38 (PDF p. 56), Definition 1.3.16; p. 39 (PDF p. 57), Theorem 1.3.17. -/
theorem joint_cdf_mixed_derivative_boundary (y : ℝ) (hy : y∈Set.Ioo (0 : ℝ) 1) :
   ¬ DifferentiableAt ℝ (fun u => deriv (fun v => uniformCDF u*uniformCDF v) y) 0 := by
  have hd : HasDerivAt uniformCDF 1 y := by
    have he : uniformCDF =ᶠ[𝓝 y] (fun x : ℝ => x) := by
      filter_upwards [eventually_gt_nhds hy.1,eventually_lt_nhds hy.2] with x hx0 hx1
      simp [uniformCDF,min_eq_right hx1.le,max_eq_right hx0.le]
    exact (hasDerivAt_id y).congr_of_eventuallyEq he
  have he (u : ℝ) : deriv (fun v => uniformCDF u*uniformCDF v) y = uniformCDF u := by
    simpa using (hd.const_mul (uniformCDF u)).deriv
  simpa only [he] using uniform_cdf_not_differentiable_zero

/-- A nonnegative integrable joint-density slice can be divided by its strictly positive finite integral; the resulting conditional density is normalized.
Target P001-T37: Theorem 1.3.13 (Marginal PDF), corrected to hold for Lebesgue-almost every $y$.
Location: p. 37 (PDF p. 55), Theorem 1.3.13; the conditional PDF of Definition 1.3.14, p. 38 (PDF p. 56). -/
theorem conditional_density_positive_finite_slice (f : ℝ × ℝ → ℝ) (hf : Measurable f) (hpos : ∀ xy,0 ≤ f xy)
   (x : ℝ) (hi : Integrable (fun y => f (x,y)) volume)
   (hp : 0 < ∫ y,f (x,y)) :
   Integrable (fun y => f (x,y)/(∫ t,f (x,t))) volume ∧
   (∀ y,0 ≤ f (x,y)/(∫ t,f (x,t))) ∧
   (∫ y,f (x,y)/(∫ t,f (x,t)))=1 := by
  refine ⟨hi.div_const _, fun y => div_nonneg (hpos _) hp.le, ?_⟩
  rw [integral_div, div_self hp.ne']


/-- The event-integral CEF definition is preserved when covariates agree almost everywhere. -/
theorem isCEF_ae_covariate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X X' Y : Ω → ℝ) (m : ℝ → ℝ)
    (he : X =ᵐ[μ] X') (hm : IsCEF μ X Y m) : IsCEF μ X' Y m := by
  have hcomp : (m ∘ X) =ᵐ[μ] (m ∘ X') := he.fun_comp m
  refine ⟨hm.1, hm.2.1, hm.2.2.1.congr hcomp, ?_⟩
  intro A hA
  have hs : X ⁻¹' A =ᵐ[μ] X' ⁻¹' A := by
    filter_upwards [he] with ω hω
    simp only [Set.mem_preimage, hω]
  calc
    (∫ ω in X' ⁻¹' A, Y ω ∂μ) = ∫ ω in X ⁻¹' A, Y ω ∂μ := setIntegral_congr_set hs.symm
    _ = ∫ ω in X ⁻¹' A, m (X ω) ∂μ := hm.2.2.2 A hA
    _ = ∫ ω in X' ⁻¹' A, m (X ω) ∂μ := setIntegral_congr_set hs
    _ = ∫ ω in X' ⁻¹' A, m (X' ω) ∂μ := integral_congr_ae (ae_restrict_of_ae hcomp)

/-- Covariance is unchanged by almost-everywhere equality of either argument. -/
theorem covariance_ae_congr {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    covariance X Y μ=covariance X' Y' μ := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  apply integral_congr_ae
  filter_upwards [hX,hY] with ω hx hy
  rw [hx,hy]

/-- Integrable CEF versions agree almost everywhere for an a.e.-measurable real covariate. -/
theorem isCEF_unique_real {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (hX : AEMeasurable X μ)
    (m n : ℝ → ℝ) (hm : IsCEF μ X Y m) (hn : IsCEF μ X Y n) :
    (m ∘ X) =ᵐ[μ] (n ∘ X) := by
  let X' := hX.mk X
  have he : X =ᵐ[μ] X' := hX.ae_eq_mk
  have hm' := isCEF_ae_covariate μ X X' Y m he hm
  have hn' := isCEF_ae_covariate μ X X' Y n he hn
  have heq := (isCEF_condExp μ X' hX.measurable_mk Y m hm').trans
    (isCEF_condExp μ X' hX.measurable_mk Y n hn').symm
  exact (he.fun_comp m).trans (heq.trans (he.fun_comp n).symm)

/-- An L² CEF preserves covariance with an L² real covariate. -/
theorem isCEF_covariance_real {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (m : ℝ → ℝ)
    (hm : IsCEF μ X Y m) (hm2 : MemLp (m ∘ X) 2 μ) :
    covariance X Y μ=covariance X (m ∘ X) μ := by
  let X' := hX.aemeasurable.mk X
  have he : X =ᵐ[μ] X' := hX.aemeasurable.ae_eq_mk
  have hm' := isCEF_ae_covariate μ X X' Y m he hm
  have hm2' : MemLp (m ∘ X') 2 μ := hm2.ae_eq (he.fun_comp m)
  have hX' : MemLp X' 2 μ := hX.ae_eq he
  have horth := (cef_residual_orthogonality_correction μ X' hX.aemeasurable.measurable_mk
    Y hY m hm' hm2').2.2 id measurable_id hX'
  have horthX : covariance X (fun ω => Y ω-m (X ω)) μ=0 := by
    have hr : (fun ω => Y ω-m (X ω)) =ᵐ[μ] (fun ω => Y ω-m (X' ω)) := by
      filter_upwards [he] with ω hx
      rw [hx]
    rw [covariance_ae_congr μ he hr]
    exact horth
  change covariance X (Y-(m ∘ X)) μ=0 at horthX
  rw [covariance_sub_right hX hY hm2] at horthX
  exact sub_eq_zero.mp horthX

/-- The risk Hessian has the corrected entries and positive determinant; the BLP approximates the CEF optimally and its residual is orthogonal to the intercept and X.
Target P001-T43: Theorem 2.2.21 (Best Linear Predictor) and the first-order conditions in its proof, with the derivatives taken in the free arguments $(a, b)$ and evaluated at $(\alpha, \beta)$; the two corollaries and Theorem 2.2.22.
Location: Theorem 2.2.21: p. 76 (PDF p. 94). Proof and footnote 19: pp. 77–78 (PDF pp. 95–96). Corollaries: p. 78 (PDF p. 96). Theorem 2.2.22: p. 79 (PDF p. 97). -/
theorem blp_hessian_and_cef_corollaries {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hv : 0 < var μ X)
   (m : ℝ → ℝ) (hm : IsCEF μ X Y m) (hm2 : MemLp (m ∘ X) 2 μ) :
   (∀ a b : ℝ,
     deriv (fun t => deriv (fun u => linearRisk μ X Y u b) t) a=2 ∧
     deriv (fun t => deriv (fun u => linearRisk μ X Y a u) t) b=2*mean μ (fun ω => (X ω)^2) ∧
     deriv (fun t => deriv (fun u => linearRisk μ X Y u t) a) b=2*mean μ X) ∧
   2*(2*mean μ (fun ω => (X ω)^2))-(2*mean μ X)^2=4*var μ X ∧
   (∀ a b : ℝ,linearRisk μ X (m ∘ X) (blpIntercept μ X Y) (blpSlope μ X Y) ≤ linearRisk μ X (m ∘ X) a b) ∧
   mean μ (fun ω => Y ω-(blpIntercept μ X Y+blpSlope μ X Y*X ω))=0 ∧
   mean μ (fun ω => X ω*(Y ω-(blpIntercept μ X Y+blpSlope μ X Y*X ω)))=0 ∧
   covariance X (fun ω => Y ω-(blpIntercept μ X Y+blpSlope μ X Y*X ω)) μ=0 ∧
   (∀ a b : ℝ,IsCEF μ X Y (fun x => a+b*x) →
     ∀ᵐ ω ∂μ,m (X ω)=blpIntercept μ X Y+blpSlope μ X Y*X ω) := by
  have hDa (a b : ℝ) : deriv (fun u => linearRisk μ X Y u b) a=
      -2*(mean μ Y-a-b*mean μ X) := by
    rw [((blp_corrected_derivatives_and_minimum μ X Y hX hY hv).1 a b).1.deriv]
    congr 1
    unfold mean
    change (∫ ω, ((fun ω : Ω => Y ω)-(fun _ : Ω => a)) ω-(fun ω => b*X ω) ω ∂μ)=_
    rw [integral_sub ((hY.integrable one_le_two).sub (integrable_const a))
      ((hX.integrable one_le_two).const_mul b)]
    change (∫ ω,Y ω-a ∂μ)-(∫ ω,b*X ω ∂μ)=_
    rw [integral_sub (hY.integrable one_le_two) (integrable_const a), integral_const_mul]
    simp
  have hDb (a b : ℝ) : deriv (fun u => linearRisk μ X Y a u) b=
      -2*covariance X Y μ+2*b*var μ X-2*mean μ X*(mean μ Y-a-b*mean μ X) := by
    have hl := ((hasDerivAt_id b).const_mul (-2*covariance X Y μ)).const_add (var μ Y)
    have hq := ((hasDerivAt_id b).pow 2).mul_const (var μ X)
    have hb := ((hasDerivAt_const b (mean μ Y-a)).sub
      ((hasDerivAt_id b).mul_const (mean μ X))).pow 2
    have hd := (hl.add hq).add hb
    dsimp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq] at hd
    have hderiv : HasDerivAt (fun u => linearRisk μ X Y a u)
        (-2*covariance X Y μ+2*b*var μ X-2*mean μ X*(mean μ Y-a-b*mean μ X)) b := by
      convert hd using 1
      · funext t
        rw [linearRisk_mean_covariance_form μ X Y hX hY]
        dsimp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
        ring
      · ring
    exact hderiv.deriv
  have hXsq : mean μ (fun ω => (X ω)^2)=var μ X+(mean μ X)^2 := by
    have hc := variance_eq_sub hX
    change var μ X=mean μ (fun ω => (X ω)^2)-(mean μ X)^2 at hc
    linarith
  have hEY := iterated_expectation μ X Y hm.2.1 m hm
  have hCov := isCEF_covariance_real μ X Y hX hY m hm hm2
  have hSlope : blpSlope μ X (m ∘ X)=blpSlope μ X Y := by
    unfold blpSlope
    rw [← hCov]
  have hIntercept : blpIntercept μ X (m ∘ X)=blpIntercept μ X Y := by
    unfold blpIntercept
    rw [hSlope, ← hEY]
  have hnormal := (blp_corrected_derivatives_and_minimum μ X Y hX hY hv).2.1
    (blpIntercept μ X Y) (blpSlope μ X Y) |>.mpr ⟨rfl,rfl⟩
  let R : Ω → ℝ := fun ω => Y ω-(blpIntercept μ X Y+blpSlope μ X Y*X ω)
  have hBX : MemLp (fun ω => blpSlope μ X Y*X ω) 2 μ := hX.const_mul (blpSlope μ X Y)
  have hFit : MemLp (fun ω => blpIntercept μ X Y+blpSlope μ X Y*X ω) 2 μ :=
    (memLp_const (blpIntercept μ X Y) : MemLp (fun _ : Ω => blpIntercept μ X Y) 2 μ).add hBX
  have hR : MemLp R 2 μ := hY.sub hFit
  have hMeanR : mean μ R=0 := by
    convert hnormal.1 using 1
    congr 1
    funext ω
    dsimp [R]
    ring
  have hMeanXR : mean μ (fun ω => X ω*R ω)=0 := by
    convert hnormal.2 using 1
    congr 1
    funext ω
    dsimp [R]
    ring
  refine ⟨?_, ?_, ?_, hMeanR, hMeanXR, ?_, ?_⟩
  · intro a b
    refine ⟨?_, ?_, ?_⟩
    · simp_rw [hDa]
      have hd := (((hasDerivAt_const a (mean μ Y)).sub (hasDerivAt_id a)).sub_const
        (b*mean μ X)).const_mul (-2)
      convert hd.deriv using 1 <;> norm_num
    · simp_rw [hDb]
      have hd := (((hasDerivAt_id b).const_mul (2*var μ X)).const_add
        (-2*covariance X Y μ)).sub
        ((((hasDerivAt_const b (mean μ Y-a)).sub
          ((hasDerivAt_id b).mul_const (mean μ X)))).const_mul (2*mean μ X))
      have hderiv : HasDerivAt
          (fun t => -2*covariance X Y μ+2*t*var μ X-
            2*mean μ X*(mean μ Y-a-t*mean μ X))
          (2*mean μ (fun ω => (X ω)^2)) b := by
        convert hd using 1
        · funext t
          dsimp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]
          ring
        · rw [hXsq]
          ring
      exact hderiv.deriv
    · simp_rw [hDa]
      have hd := (((hasDerivAt_id b).mul_const (mean μ X)).const_sub
        (mean μ Y-a)).const_mul (-2)
      convert hd.deriv using 1 <;> norm_num
  · rw [hXsq]
    ring
  · intro a b
    have hmin := (blp_corrected_derivatives_and_minimum μ X (m ∘ X)
      hX hm2 hv).2.2 a b |>.1
    rw [hSlope, hIntercept] at hmin
    exact hmin
  · change covariance X R μ=0
    rw [covariance_eq_sub hX hR]
    change mean μ (fun ω => X ω*R ω)-mean μ X*mean μ R=0
    rw [hMeanXR,hMeanR]
    ring
  · intro a b hab
    have hA2 : MemLp ((fun x => a+b*x) ∘ X) 2 μ :=
      (memLp_const a : MemLp (fun _ : Ω => a) 2 μ).add (hX.const_mul b)
    have hc := isCEF_covariance_real μ X Y hX hY (fun x => a+b*x) hab hA2
    have he := iterated_expectation μ X Y hab.2.1 (fun x => a+b*x) hab
    have hcoeff := (blp_two_equation_characterization μ X Y hX hY hv a b).2.mp
      ⟨hc.symm, he.symm⟩
    have heq := isCEF_unique_real μ X Y hX.aemeasurable m (fun x => a+b*x) hm hab
    filter_upwards [heq] with ω hω
    simpa only [Function.comp_apply,hcoeff.1,hcoeff.2] using hω

/-- The standard uniform law is restricted Lebesgue measure on the unit interval. -/
theorem uniformLaw_zero_one_eq_restrict :
    uniformLaw 0 1=volume.restrict (Set.Icc (0 : ℝ) 1) := by
  unfold uniformLaw
  have hf : (fun x : ℝ => ENNReal.ofReal (if x ∈ Set.Icc (0 : ℝ) 1 then (1-0)⁻¹ else 0))=
      (Set.Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) := by
    funext x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [hx,Set.indicator]
  rw [hf]
  exact withDensity_indicator_one measurableSet_Icc

/-- Every natural power has its usual unit-uniform moment. -/
theorem integral_pow_uniformLaw_zero_one (k : ℕ) :
    (∫ x : ℝ,x^k ∂uniformLaw 0 1)=1/((k : ℝ)+1) := by
  rw [uniformLaw_zero_one_eq_restrict,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),integral_pow]
  simp

/-- For X uniform on [0,1] and independent standard normal W, Y=10X²+W has CEF 10X² and BLP −5/3+10X.
Target P001-T46: Example 2.2.24 (BLP under Nonlinearity), the CEF formula, corrected; with the CEF and BLP of Example 2.2.23.
Location: Example 2.2.24: p. 82 (PDF p. 100), second sentence. Example 2.2.23: pp. 79–81 (PDF pp. 97–99). -/
theorem uniform_quadratic_cef_and_blp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X W : Ω → ℝ) (hX : Measurable X) (hW : Measurable W)
   (hi : IndepFun X W μ) (hx : μ.map X=uniformLaw 0 1) (hw : μ.map W=gaussianReal 0 1) :
   let Y := fun ω => 10*(X ω)^2+W ω
   IsCEF μ X Y (fun x => 10*x^2) ∧
   mean μ X=1/2 ∧ mean μ (fun ω => (X ω)^2)=1/3 ∧ mean μ (fun ω => (X ω)^3)=1/4 ∧
   var μ X=1/12 ∧ mean μ Y=10/3 ∧ covariance X Y μ=5/6 ∧
   blpSlope μ X Y=10 ∧ blpIntercept μ X Y= -5/3 := by
  let Y : Ω → ℝ := fun ω => 10*(X ω)^2+W ω
  have hU2 : MemLp id 2 (uniformLaw 0 1) := by
    rw [uniformLaw_zero_one_eq_restrict]
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    exact (continuous_pow 2).continuousOn.integrableOn_Icc
  have hUU2 : MemLp (fun x : ℝ => x^2) 2 (uniformLaw 0 1) := by
    rw [uniformLaw_zero_one_eq_restrict]
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    have h4 : Integrable (fun x : ℝ => x^4) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      (continuous_pow 4).continuousOn.integrableOn_Icc
    exact h4.congr (ae_of_all _ (fun x => by ring))
  have hX2m : MemLp id 2 (μ.map X) := by rw [hx]; exact hU2
  have hX2 : MemLp X 2 μ := hX2m.comp_of_map hX.aemeasurable
  have hXX2m : MemLp (fun x : ℝ => x^2) 2 (μ.map X) := by rw [hx]; exact hUU2
  have hXX2 : MemLp (fun ω => (X ω)^2) 2 μ := hXX2m.comp_of_map hX.aemeasurable
  have hW2m : MemLp id 2 (μ.map W) := by
    rw [hw]
    exact memLp_id_gaussianReal' 2 (by norm_num)
  have hW2 : MemLp W 2 μ := hW2m.comp_of_map hW.aemeasurable
  have hWi : Integrable W μ := hW2.integrable one_le_two
  have hmom (k : ℕ) : mean μ (fun ω => (X ω)^k)=1/((k : ℝ)+1) := by
    have hp : AEStronglyMeasurable (fun x : ℝ => x^k) (μ.map X) := by fun_prop
    unfold mean
    rw [← integral_map hX.aemeasurable hp,hx,integral_pow_uniformLaw_zero_one]
  have hM1 : mean μ X=1/2 := by
    have h := hmom 1
    norm_num at h
    exact h
  have hM2 : mean μ (fun ω => (X ω)^2)=1/3 := by
    have h := hmom 2
    norm_num at h
    exact h
  have hM3 : mean μ (fun ω => (X ω)^3)=1/4 := by
    have h := hmom 3
    norm_num at h
    exact h
  have hW0 : mean μ W=0 := by
    have hp : AEStronglyMeasurable (id : ℝ → ℝ) (μ.map W) := by fun_prop
    calc
      mean μ W=(∫ x : ℝ,x ∂μ.map W) := (integral_map hW.aemeasurable hp).symm
      _=0 := by rw [hw]; exact integral_id_gaussianReal
  have hGi : Integrable (fun ω => 10*(X ω)^2) μ := (hXX2.integrable one_le_two).const_mul 10
  have hG2 : MemLp (fun ω => 10*(X ω)^2) 2 μ := hXX2.const_mul 10
  have hCEF : IsCEF μ X Y (fun x => 10*x^2) :=
    additive_independent_noise_cef μ X W hX hW hi hWi hW0 (fun x => 10*x^2) (by fun_prop) hGi
  have hVX : var μ X=1/12 := by
    rw [var,variance_eq_sub hX2]
    change mean μ (fun ω => (X ω)^2)-(mean μ X)^2=1/12
    rw [hM2,hM1]
    norm_num
  have hEY : mean μ Y=10/3 := by
    unfold mean Y
    rw [integral_add hGi hWi,integral_const_mul]
    change 10*mean μ (fun ω => (X ω)^2)+mean μ W=10/3
    rw [hM2,hW0]
    norm_num
  have hprod : mean μ (fun ω => X ω*(X ω)^2)=1/4 := by
    calc
      _=mean μ (fun ω => (X ω)^3) := integral_congr_ae (ae_of_all _ (fun ω => by ring))
      _=1/4 := hM3
  have hCovXX : covariance X (fun ω => (X ω)^2) μ=1/12 := by
    rw [covariance_eq_sub hX2 hXX2]
    change mean μ (fun ω => X ω*(X ω)^2)-mean μ X*mean μ (fun ω => (X ω)^2)=1/12
    rw [hprod,hM1,hM2]
    norm_num
  have hCov : covariance X Y μ=5/6 := by
    change covariance X ((fun ω => 10*(X ω)^2)+W) μ=5/6
    rw [covariance_add_right hX2 hG2 hW2,covariance_const_mul_right,
      hi.covariance_eq_zero hX2 hW2,hCovXX]
    norm_num
  have hSlope : blpSlope μ X Y=10 := by unfold blpSlope; rw [hCov,hVX]; norm_num
  have hIntercept : blpIntercept μ X Y= -5/3 := by unfold blpIntercept; rw [hEY,hSlope,hM1]; norm_num
  exact ⟨hCEF,hM1,hM2,hM3,hVX,hEY,hCov,hSlope,hIntercept⟩

/-- Independent integrable outcomes have a constant CEF for a.e.-measurable real covariates and outcomes. -/
theorem independent_constant_cef_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (hYi : Integrable Y μ)
    (hi : IndepFun X Y μ) : IsCEF μ X Y (fun _ => mean μ Y) := by
  let X' := hX.mk X
  let Y' := hY.mk Y
  have heX : X =ᵐ[μ] X' := hX.ae_eq_mk
  have heY : Y =ᵐ[μ] Y' := hY.ae_eq_mk
  have hYi' : Integrable Y' μ := hYi.congr heY
  have hi' : IndepFun X' Y' μ := hi.congr heX heY
  have hc := independent_constant_cef μ X' Y' hX.measurable_mk hY.measurable_mk hYi' hi'
  have hcX := isCEF_ae_covariate μ X' X Y' (fun _ => mean μ Y') heX.symm hc
  have hmean : mean μ Y'=mean μ Y := integral_congr_ae heY.symm
  refine ⟨measurable_const,hYi,integrable_const _,?_⟩
  intro A hA
  calc
    (∫ ω in X ⁻¹' A,Y ω ∂μ)=∫ ω in X ⁻¹' A,Y' ω ∂μ :=
      integral_congr_ae (ae_restrict_of_ae heY)
    _=∫ ω in X ⁻¹' A,mean μ Y' ∂μ := hcX.2.2.2 A hA
    _=∫ ω in X ⁻¹' A,mean μ Y ∂μ := by rw [hmean]

/-- The constant mean minimizes affine prediction risk under independence, allowing zero covariate variance. -/
theorem independent_affine_risk_minimum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hi : IndepFun X Y μ) (a b : ℝ) :
    linearRisk μ X Y (mean μ Y) 0 ≤ linearRisk μ X Y a b := by
  rw [linearRisk_mean_covariance_form μ X Y hX hY,
    linearRisk_mean_covariance_form μ X Y hX hY, hi.covariance_eq_zero hX hY]
  have hV : 0 ≤ var μ X := variance_nonneg X μ
  nlinarith [sq_nonneg (mean μ Y-a-b*mean μ X), mul_nonneg (sq_nonneg b) hV]

/-- Under independence, the conditional variance is constant and the constant mean minimizes prediction risk among all affine functions of the independent covariate and its measurable transformations.
Target P001-T47: Theorem 2.2.25 (Implications of Independence, Part III), fourth bullet, first sub-bullet, corrected.
Location: pp. 82–83 (PDF pp. 100–101). -/
theorem independence_variance_and_blp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hi : IndepFun X Y μ) :
   IsCEF μ X (fun ω => (Y ω-mean μ Y)^2) (fun _ => var μ Y) ∧
   (∀ a b : ℝ,linearRisk μ X Y (mean μ Y) 0 ≤ linearRisk μ X Y a b) ∧
   ∀ g h : ℝ → ℝ,Measurable g → Measurable h →
     MemLp (g ∘ X) 2 μ → MemLp (h ∘ Y) 2 μ → ∀ a b : ℝ,
     linearRisk μ (g ∘ X) (h ∘ Y) (mean μ (h ∘ Y)) 0 ≤ linearRisk μ (g ∘ X) (h ∘ Y) a b := by
  let f : ℝ → ℝ := fun y => (y-mean μ Y)^2
  have hf : Measurable f := by unfold f; fun_prop
  have hYc : MemLp (fun ω => Y ω-mean μ Y) 2 μ :=
    hY.sub (memLp_const (mean μ Y) : MemLp (fun _ : Ω => mean μ Y) 2 μ)
  have hYi : Integrable (fun ω => (Y ω-mean μ Y)^2) μ := hYc.integrable_sq
  have hV : mean μ (fun ω => (Y ω-mean μ Y)^2)=var μ Y :=
    (variance_eq_integral hY.aemeasurable).symm
  have hc := independent_constant_cef_ae μ X (fun ω => (Y ω-mean μ Y)^2)
    hX.aemeasurable hYi.aemeasurable hYi (hi.comp measurable_id hf)
  rw [hV] at hc
  refine ⟨hc,fun a b => independent_affine_risk_minimum μ X Y hX hY hi a b,?_⟩
  intro g h hg hh hg2 hh2 a b
  exact independent_affine_risk_minimum μ (g ∘ X) (h ∘ Y) hg2 hh2 (hi.comp hg hh) a b

/-- The partial derivative of the multivariate affine predictor in each coordinate equals its corresponding coefficient at every covariate vector.
Target P001-T49: Section 2.3, the two expansions of the multivariate BLP used to interpret $\beta_1$, corrected; with Definition 2.3.6 and Theorem 2.3.7 (Coefficients of the BLP Are Partial Derivatives).
Location: p. 87 (PDF p. 105), first paragraph and Theorem 2.3.7. Definition 2.3.6: p. 86 (PDF p. 104). -/
theorem linear_predictor_partial_derivative {K : ℕ} (b : Fin (K+1) → ℝ) (x : Fin K → ℝ) (k : Fin K) :
   HasDerivAt (fun t : ℝ => linearPredictor b (Function.update x k t)) (b k.succ) (x k) ∧
   partialAt (linearPredictor b) x k=b k.succ := by
  
  have hAffine (c d u : ℝ) : HasDerivAt (fun t : ℝ => c+d*t) d u := by
    exact (hasDerivAt_const_mul (x := u) d).const_add c
  have he : (fun t : ℝ => linearPredictor b (Function.update x k t))=
      (fun t : ℝ => (linearPredictor b x-b k.succ*x k)+b k.succ*t) := by
    funext t
    rw [linear_predictor_update_identity]
    ring
  have hd : HasDerivAt (fun t : ℝ => linearPredictor b (Function.update x k t))
      (b k.succ) (x k) := by
    rw [he]
    exact hAffine _ _ _
  refine ⟨hd,?_⟩
  change deriv (fun t : ℝ => linearPredictor b (Function.update x k (x k+t))) 0=b k.succ
  have he' : (fun t : ℝ => linearPredictor b (Function.update x k (x k+t)))=
      (fun t : ℝ => linearPredictor b x+b k.succ*t) := by
    funext t
    rw [linear_predictor_update_identity]
    ring
  rw [he']
  exact (hAffine (linearPredictor b x) (b k.succ) 0).deriv

/-- The mean and variance under the empirical distribution are the sample mean and the mean of squares minus the square of the mean.
Target P001-T50: Three misprinted displays, corrected: the variance in Example 3.1.3 (p. 94); the variance functional $T_{\mathrm{V}}(F)$ (p. 118, repeated in Example 3.3.5, p. 119); the last line of Example 3.3.4 (p. 119).
Location: (a) p. 94 (PDF p. 112), Example 3.1.3 (continued), second bullet. (b) p. 118 (PDF p. 136), display for $\mathrm{V}[X] = T_{\mathrm{V}}(F)$, last line; p. 119 (PDF p. 137), first display of Example 3.3.5. (c) p. 119 (PDF p. 137), Example 3.3.4, last line of the display. Definition 3.1.2 and Example 3.1.3: p. 93 (PDF p. 111). -/
theorem empirical_variance_identity (X : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
   let μ := empirical (fun i (_ : Unit) => X i) n ()
   IsProbabilityMeasure μ ∧ mean μ id=(∑ i∈Finset.range n,X i)/(n : ℝ) ∧
   var μ id=(∑ i∈Finset.range n,(X i)^2)/(n : ℝ)-((∑ i∈Finset.range n,X i)/(n : ℝ))^2 := by
  let μ := empirical (fun i (_ : Unit) => X i) n ()
  have hμ : IsProbabilityMeasure μ := by
    constructor
    simp [μ, empirical, Measure.sum_apply, hn.ne']
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)
  letI := hμ
  have hsq : Integrable (fun x : ℝ => x^2) μ := by
    unfold μ empirical
    exact (integrable_finsetSum_measure.2 (fun i hi => integrable_dirac (by simp))).smul_measure (by simp [hn.ne'])
  have h2 : MemLp id 2 μ := (memLp_two_iff_integrable_sq (by fun_prop)).2 hsq
  have hfirst : mean μ id=(∑ i∈Finset.range n,X i)/(n : ℝ) := by
    unfold mean μ empirical
    rw [integral_smul_measure]
    rw [integral_finsetSum_measure (fun i hi => integrable_dirac (by simp))]
    simp [ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]
  have hsecond : (∫ x : ℝ, x^2 ∂μ)=(∑ i∈Finset.range n,(X i)^2)/(n : ℝ) := by
    unfold μ empirical
    rw [integral_smul_measure]
    rw [integral_finsetSum_measure (fun i hi => integrable_dirac (by simp))]
    simp [ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]
  refine ⟨hμ, hfirst, ?_⟩
  rw [var, variance_eq_sub h2]
  change (∫ x : ℝ, x^2 ∂μ)-(mean μ id)^2=_
  rw [hfirst, hsecond]

/-- The sample average of the indicators Xi≤x consistently estimates the CDF at every fixed x.
Target P001-T52: Footnote 12 (the expectation of an indicator), with the domain of $D$ corrected; with Theorem 3.2.9 (Estimating the CDF), to whose statement it is attached.
Location: p. 102 (PDF p. 120), Theorem 3.2.9 and footnote 12. -/
theorem empirical_cdf_consistency {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (x : ℝ) :
   CP μ (sampleMean (fun i ω => if X i ω ≤ x then (1 : ℝ) else 0)) (cdf μ (X 0) x) := by
  let g : ℝ → ℝ := fun t => if t ≤ x then 1 else 0
  let Z : ℕ → Ω → ℝ := fun i => g ∘ X i
  have hg : Measurable g := by
    exact measurable_const.piecewise measurableSet_Iic measurable_const
  have hZ : IID μ Z := by
    refine ⟨fun i => hg.comp (hiid.1 i), ?_, fun i => (hiid.2.2 i).comp hg⟩
    exact hiid.2.1.comp (fun _ => g) (fun _ => hg)
  have hA : MeasurableSet {ω | X 0 ω ≤ x} := measurableSet_le (hiid.1 0) measurable_const
  have hZi : Integrable (Z 0) μ := by
    refine ((integrable_const (1 : ℝ)).indicator hA).congr ?_
    filter_upwards [] with ω
    by_cases hω : X 0 ω ≤ x <;> simp [Z, g, Function.comp_def, Set.indicator, hω]
  have he : mean μ (Z 0)=cdf μ (X 0) x := by
    change (∫ ω, Set.indicator {ω | X 0 ω ≤ x} (fun _ => (1 : ℝ)) ω ∂μ)=_
    rw [integral_indicator hA]
    simp [cdf, prob, Measure.real]
  have hlim := strong_law_ae_real Z hZi
    (fun i j hij => hZ.2.1.indepFun hij) hZ.2.2
  have hZm : ∀ i, Measurable (Z i) := hZ.1
  have hm : ∀ n, Measurable (sampleMean Z n) := by
    intro n
    unfold sampleMean
    fun_prop
  have hmeasure := tendstoInMeasure_of_tendsto_ae
    (fun n => (hm n).aestronglyMeasurable) hlim
  intro ε hε
  have hh := (tendstoInMeasure_iff_measureReal_dist.mp hmeasure) ε hε
  simpa only [prob, Measure.real, ← he, mean, Z, g, Function.comp_def, sampleMean] using hh

/-- The constant functional seven is Hadamard differentiable in every direction with zero derivative, on any domain.
Target P001-T56: Theorem 3.3.6 (Asymptotic Normality of Plug-In Estimators), as printed, read with footnote 31 and Definition 3.2.28.
Location: p. 120 (PDF p. 138), Theorem 3.3.6 and footnote 31. Definition 3.2.28: p. 112 (PDF p. 130). -/
theorem constant_functional_hadamard {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
   (D H : Set E) (F : E) : HadamardAt D H (fun _ => 7) F (0 : E →L[ℝ] ℝ) := by
  intro h hh t hn ht htlim hhlim hvalid
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

/-- With no observation at x−h, the rectangular kernel density equals the empirical CDF difference at x+h and x−h, divided by 2h.
Target P001-T60: Definition 3.3.9 (Kernel Plug-In Estimator), last line: the integrand, corrected to the kernel density estimator $\hat f_K$.
Location: p. 123 (PDF p. 141), Definition 3.3.9, last line. -/
theorem rectangular_kernel_empirical_cdf_identity {n : ℕ} (hn : 0 < n) (X : Fin n → ℝ) (h : ℝ) (hh : 0 < h) (x : ℝ)
   (hboundary : ∀ i,X i≠x-h) :
   kernelDensity rectangleKernel h X x=
     (((∑ i,if X i ≤ x+h then (1 : ℝ) else 0)/(n : ℝ))-
      ((∑ i,if X i ≤ x-h then (1 : ℝ) else 0)/(n : ℝ)))/(2*h) := by
  have hi (i : Fin n) : rectangleKernel ((x-X i)/h)/h =
      ((if X i ≤ x+h then (1:ℝ) else 0)-(if X i ≤ x-h then (1:ℝ) else 0))/(2*h) := by
    by_cases hu : X i ≤ x+h
    · by_cases hl : X i ≤ x-h
      · have hlt : X i < x-h := lt_of_le_of_ne hl (hboundary i)
        have ha : ¬ |(x-X i)/h| ≤ 1 := by
          intro ha
          rw [abs_le,le_div_iff₀ hh,div_le_iff₀ hh] at ha
          nlinarith [ha.1,ha.2]
        simp [rectangleKernel,hu,hl,ha]
      · have ha : |(x-X i)/h| ≤ 1 := by
          rw [abs_le,le_div_iff₀ hh,div_le_iff₀ hh]
          constructor <;> linarith
        simp only [rectangleKernel,if_pos ha,if_pos hu,if_neg hl,sub_zero]
        field_simp
    · have ha : ¬ |(x-X i)/h| ≤ 1 := by
        intro ha
        rw [abs_le,le_div_iff₀ hh,div_le_iff₀ hh] at ha
        nlinarith [ha.1,ha.2]
      have hl : ¬ X i ≤ x-h := by linarith
      simp [rectangleKernel,hu,hl,ha]
  unfold kernelDensity
  simp_rw [hi]
  rw [← Finset.sum_div,Finset.sum_sub_distrib]
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR,hh.ne']


/-- A zero conditional mean and constant conditional variance imply that the expected squared-residual regressor product is sigma² times the expected regressor product.
Target P001-T67: Section 4.2.3, the display reducing the asymptotic covariance of the OLS estimator under a linear CEF and homoskedasticity, with the stray observation subscript removed.
Location: p. 155 (PDF p. 173), display beginning $n\mathrm{V}[\hat{\boldsymbol\beta}] \approx$; the sandwich form: p. 152 (PDF p. 170). -/
theorem homoskedastic_population_moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K : ℕ} (X : Ω → Fin K → ℝ) (hX : Measurable X) (ε : Ω → ℝ) (hε : MemLp ε 2 μ)
   (hzero : IsCEF μ X ε (fun _ => 0)) (σ2 : ℝ) (hσ : 0 ≤ σ2)
   (hv : IsCEF μ X (fun ω => (ε ω-0)^2) (fun _ => σ2))
   (hXX : ∀ j k,Integrable (fun ω => X ω j*X ω k) μ)
   (hεXX : ∀ j k,Integrable (fun ω => (ε ω)^2*X ω j*X ω k) μ) :
   IsCEF μ X (fun ω => (ε ω)^2) (fun _ => σ2) ∧
   ∀ j k,mean μ (fun ω => (ε ω)^2*X ω j*X ω k)=σ2*mean μ (fun ω => X ω j*X ω k) := by
  have hv' : IsCEF μ X (fun ω => (ε ω)^2) (fun _ => σ2) := by
    simpa only [sub_zero] using hv
  refine ⟨hv',?_⟩
  intro j k
  let G : Ω → ℝ := fun ω => X ω j*X ω k
  let E2 : Ω → ℝ := fun ω => (ε ω)^2
  have hXm : Measurable[MeasurableSpace.comap X inferInstance] X :=
    measurable_iff_comap_le.mpr le_rfl
  have hG : StronglyMeasurable[MeasurableSpace.comap X inferInstance] G :=
    (((measurable_pi_apply j).comp hXm).mul ((measurable_pi_apply k).comp hXm)).stronglyMeasurable
  have hProd : Integrable (G*E2) μ := (hεXX j k).congr (ae_of_all _ (fun ω => by
    dsimp [G,E2]
    ring))
  have hCond : μ[E2 | MeasurableSpace.comap X inferInstance] =ᵐ[μ] (fun _ => σ2) :=
    (isCEF_condExp μ X hX E2 (fun _ => σ2) hv').symm
  have hMul := condExp_mul_of_stronglyMeasurable_left hG hProd hv'.2.1
  have hInt : (∫ ω,(G*E2) ω ∂μ)=σ2*∫ ω,G ω ∂μ := by
    rw [← integral_condExp hX.comap_le (f := G*E2)]
    calc
      (∫ ω,μ[G*E2 | MeasurableSpace.comap X inferInstance] ω ∂μ)=∫ ω,G ω*σ2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hMul,hCond] with ω hmul hcond
        simp only [hmul,Pi.mul_apply,hcond]
      _=σ2*∫ ω,G ω ∂μ := by rw [integral_mul_const]; ring
  change (∫ ω,(ε ω)^2*X ω j*X ω k ∂μ)=σ2*∫ ω,G ω ∂μ
  rw [← hInt]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => by dsimp [G,E2]; ring)

/-- The grouped estimator difference has the corrected cell coefficients; saturation makes the stabilized denominator exactly one.
Target P001-T85: Section 6.2.5, equivalence of the IPW estimator and the post-stratification plug-in estimator, corrected: it holds when the estimated response probability in each cell is the observed respondent fraction.
Location: p. 228 (PDF p. 246), first paragraph. -/
theorem missing_ipw_difference_and_stabilization {E : Type*} [Fintype E] (N r S q : E → ℝ) (n : ℝ) (hn : 0 < n)
   (hN : ∀ x,0 < N x) (hr : ∀ x,0 < r x) (htotal : ∑ x,N x=n) :
   (∑ x,S x/q x)/n-(∑ x,N x*S x/r x)/n=
     (∑ x,S x*(1/q x-N x/r x))/n ∧
   (∑ x,r x/(r x/N x))/n=1 := by
  
  constructor
  · rw [← sub_div,← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    ring
  · have he (x : E) : r x/(r x/N x)=N x := by
      field_simp [ne_of_gt (hN x),ne_of_gt (hr x)]
    simp_rw [he]
    rw [htotal]
    exact div_self (ne_of_gt hn)


/-- With both arms in every cell, equality of IPW and post-stratification for all arm outcome sums is equivalent to each fitted propensity equaling its observed treated fraction.
Target P001-T97: Section 7.2.6, equivalence of the IPW estimator and the post-stratification plug-in estimator of the ATE, corrected: it holds when each fitted propensity equals the observed treated fraction in its covariate cell.
Location: p. 266 (PDF p. 284), paragraph after Definition 7.2.6. -/
theorem causal_ipw_saturation_necessary {E : Type*} [Fintype E] [DecidableEq E] (nt nc q : E → ℝ)
   (ht : ∀ x,0 < nt x) (hc : ∀ x,0 < nc x) (hq : ∀ x,q x∈Set.Ioo (0 : ℝ) 1) :
   (∀ st sc : E → ℝ,
     (∑ x,(st x/q x-sc x/(1-q x)))=∑ x,(nt x+nc x)*(st x/nt x-sc x/nc x)) ↔
     ∀ x,q x=nt x/(nt x+nc x) := by
  
  constructor
  · intro h
    have hN : ∀ x,0 < nt x+nc x := by intro x; linarith [ht x,hc x]
    apply (missing_ipw_saturation_necessary (fun x => nt x+nc x) nt q hN ht
      (fun x => (hq x).1)).1
    intro S
    simpa [mul_div_assoc] using h S (fun _ => 0)
  · intro h st sc
    simp_rw [h]
    exact causal_ipw_saturated_cells nt nc st sc ht hc

/-- For iid units and uniformly bounded propensity, both arm-indicator reciprocal weight averages have expectation one for every positive n; both all-unit reciprocal means exceed one.
Target P001-T98: The paragraph after Definition 7.2.7 (Stabilized IPW Estimator for Causal Inference): the two sums whose between-sample variation the stabilized estimator accounts for, corrected (the treatment-arm indicators).
Location: p. 267 (PDF p. 285), Definition 7.2.7 and the paragraph after it. -/
theorem treatment_weight_sample_means {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → E) (D : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,D i ω))) (p : E → ℝ)
   (hp : IsCEF μ (X 0) (D 0) p) (hbinary : ∀ i ω,D i ω=0 ∨ D i ω=1)
   (hpos : ∃ ε : ℝ,0 < ε ∧ ∀ i ω,ε < p (X i ω) ∧ p (X i ω) < 1-ε) :
   (∀ n,0 < n → mean μ (sampleMean (fun i ω => D i ω/p (X i ω)) n)=1 ∧
     mean μ (sampleMean (fun i ω => (1-D i ω)/(1-p (X i ω))) n)=1) ∧
   1 < mean μ (fun ω => 1/p (X 0 ω)) ∧ 1 < mean μ (fun ω => 1/(1-p (X 0 ω))) := by
  obtain ⟨ε,hε,hpos⟩ := hpos
  let g1 : E×ℝ → ℝ := fun xd => xd.2/p xd.1
  let g0 : E×ℝ → ℝ := fun xd => (1-xd.2)/(1-p xd.1)
  have hg1 : Measurable g1 := measurable_snd.div (hp.1.comp measurable_fst)
  have hg0 : Measurable g0 := (measurable_const.sub measurable_snd).div
    (measurable_const.sub (hp.1.comp measurable_fst))
  let W1 := fun i ω => g1 (X i ω,D i ω)
  let W0 := fun i ω => g0 (X i ω,D i ω)
  have hi1 : IID μ W1 := ⟨fun i => hg1.comp (hiid.1 i),
    hiid.2.1.comp (fun _ => g1) (fun _ => hg1),fun i => (hiid.2.2 i).comp hg1⟩
  have hi0 : IID μ W0 := ⟨fun i => hg0.comp (hiid.1 i),
    hiid.2.1.comp (fun _ => g0) (fun _ => hg0),fun i => (hiid.2.2 i).comp hg0⟩
  have hb1 (i : ℕ) (ω : Ω) : |W1 i ω|≤1/ε := by
    change |D i ω/p (X i ω)|≤1/ε
    rw [abs_div,abs_of_pos (hε.trans (hpos i ω).1)]
    apply div_le_div₀ (by norm_num) _ hε (hpos i ω).1.le
    rcases hbinary i ω with h|h <;> rw [h] <;> norm_num
  have hb0 (i : ℕ) (ω : Ω) : |W0 i ω|≤1/ε := by
    have hd : ε<1-p (X i ω) := by linarith [(hpos i ω).2]
    change |(1-D i ω)/(1-p (X i ω))|≤1/ε
    rw [abs_div,abs_of_pos (hε.trans hd)]
    apply div_le_div₀ (by norm_num) _ hε hd.le
    rcases hbinary i ω with h|h <;> rw [h] <;> norm_num
  have h21 : MemLp (W1 0) 2 μ := MemLp.of_bound (hi1.1 0).aestronglyMeasurable (1/ε)
    (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hb1 0 ω))
  have h20 : MemLp (W0 0) 2 μ := MemLp.of_bound (hi0.1 0).aestronglyMeasurable (1/ε)
    (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hb0 0 ω))
  have hw := treatment_weights_denominators_correction μ (X 0) ((hiid.1 0).fst)
    (D 0) ((hiid.1 0).snd) (hbinary 0) p hp ⟨ε,hε,fun ω => hpos 0 ω⟩
  have hm1 : mean μ (W1 0)=1 := hw.2.2.1
  have hm0 : mean μ (W0 0)=1 := hw.2.2.2
  have hstrict (q : Ω → ℝ) (hqm : Measurable q)
      (hq : ∀ ω,ε<q ω ∧ q ω<1-ε) : 1<mean μ (fun ω => 1/q ω) := by
    have hqi : Integrable (fun ω => 1/q ω) μ := by
      apply Integrable.of_bound (measurable_const.div hqm).aestronglyMeasurable (1/ε)
      apply ae_of_all
      intro ω
      change ‖1/q ω‖≤1/ε
      rw [Real.norm_eq_abs,abs_div,abs_one,abs_of_pos (hε.trans (hq ω).1)]
      exact div_le_div₀ (by norm_num) le_rfl hε (hq ω).1.le
    have hlow (ω : Ω) : 1+ε≤1/q ω := by
      apply (le_div_iff₀ (hε.trans (hq ω).1)).mpr
      calc
        (1+ε)*q ω ≤ (1+ε)*(1-ε) := mul_le_mul_of_nonneg_left (hq ω).2.le (by linarith)
        _ ≤ 1 := by nlinarith [sq_nonneg ε]
    have hh := integral_mono (integrable_const (1+ε)) hqi hlow
    have hh' : 1+ε≤mean μ (fun ω => 1/q ω) := by simpa [mean] using hh
    linarith
  refine ⟨?_,hstrict (fun ω => p (X 0 ω)) (hp.1.comp (hiid.1 0).fst) (hpos 0),?_⟩
  · intro n hn
    have h1 := (iid_sample_mean_finite_moments μ W1 hi1 h21 n hn).1
    have h0 := (iid_sample_mean_finite_moments μ W0 hi0 h20 n hn).1
    exact ⟨h1.trans hm1,h0.trans hm0⟩
  · apply hstrict (fun ω => 1-p (X 0 ω)) (measurable_const.sub (hp.1.comp (hiid.1 0).fst))
    intro ω
    constructor <;> linarith [(hpos 0 ω).1,(hpos 0 ω).2]


/-- For every fixed positive n and bandwidth, the rectangular kernel expectation and variance are exactly the Bernoulli-window formulas in the proof of consistency.
Target P001-T127: Theorem 3.3.8 (Consistency of the Kernel Density Estimator, Rectangular Kernel).
Location: p. 122 (PDF p. 140); proof sketch on p. 123 (PDF p. 141); the continuity condition is stated on p. 121 (PDF p. 139). -/
theorem rectangular_kernel_fixed_sample_moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (f : ℝ → ℝ) (hf : HasPDF (μ.map (X 0)) f)
   (n : ℕ) (hn : 0 < n) (h : ℝ) (hh : 0 < h) (x : ℝ) :
   let p := cdf μ (X 0) (x+h)-cdf μ (X 0) (x-h)
   mean μ (fun ω => kernelDensity rectangleKernel h (firstSample X n ω) x)=p/(2*h) ∧
   var μ (fun ω => kernelDensity rectangleKernel h (firstSample X n ω) x)=p*(1-p)/(4*h^2*(n : ℝ)) := by
  exact rectangular_kernel_moments_core μ X hiid f hf n hn h hh x

/-- No estimator on the same sampling experiment can converge in probability to two distinct values of the unused mixture parameter.
Target P001-T11: Section 5.2.5, the sentence 'If any subset of the models ... jointly characterize the conditional distribution of $Y$, then this estimator is consistent and asymptotically efficient', as printed.
Location: p. 199 (PDF p. 217), second paragraph; the mixture and its parameter vector: pp. 198–199 (PDF pp. 216–217). -/
theorem nonidentification_no_two_consistent_targets_supporting {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (that : ℕ → Ω → Fin 3 → ℝ) (hm : ∀ n,Measurable (that n)) :
   ¬ (CP μ that (![1,1/3,1/4] : Fin 3 → ℝ) ∧ CP μ that (![1,1/3,3/4] : Fin 3 → ℝ)) := by
  
  rintro ⟨ha,hb⟩
  have he := probability_limit_unique μ that _ _ ha hb
  have hc := congrFun he 2
  norm_num at hc

/-- For an iid correctly specified conditional model, average sample log-criterion maximizers are consistent under compactness, population uniqueness and uniform convergence.
Target P001-T129: Theorem 5.2.6 (Consistency of the Maximum Likelihood Estimator) and the lemma in its proof sketch.
Location: Theorem 5.2.6: p. 193 (PDF p. 211). Proof sketch: pp. 193–194 (PDF pp. 211–212). -/
theorem maximum_likelihood_consistency_correct_model {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (Θ : Set (Fin τ → ℝ))
   (hc : IsCompact Θ) (θ : Fin τ → ℝ) (hθ : θ∈Θ)
   (hg : ∀ t∈Θ,Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
   (hnonneg : ∀ t∈Θ,∀ y x,0 ≤ g y x t)
   (hnorm : ∀ t∈Θ,∀ x,(∫⁻ y,ENNReal.ofReal (g y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=conditionalModelLaw νX κ g θ)
   (hlog : ∀ t∈Θ,Integrable (fun ω => Real.log (g (Y 0 ω) (X 0 ω) t)) μ)
   (hpos : ∀ t∈Θ,∀ᵐ ω ∂μ,0 < g (Y 0 ω) (X 0 ω) t)
   (hM : ContinuousOn (expectedLogLikelihood μ (X 0) (Y 0) g) Θ)
   (hunique : ∀ t∈Θ,expectedLogLikelihood μ (X 0) (Y 0) g t ≤ expectedLogLikelihood μ (X 0) (Y 0) g θ ∧
     (expectedLogLikelihood μ (X 0) (Y 0) g t=expectedLogLikelihood μ (X 0) (Y 0) g θ → t=θ))
   (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n,Measurable (that n))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → sampleLogLikelihood X Y g n ω t ≤ sampleLogLikelihood X Y g n ω (that n ω))
   (Δ : ℕ → Ω → ℝ) (hΔ : ∀ n ω t,t∈Θ →
     |sampleLogLikelihood X Y g n ω t-expectedLogLikelihood μ (X 0) (Y 0) g t| ≤ Δ n ω)
   (hlim : CP μ Δ 0) : CP μ that θ := by
  
  exact ml_consistency_explicit_uniform_regularities_supporting μ Θ hc θ hθ
    (expectedLogLikelihood μ (X 0) (Y 0) g) hM hunique
    (sampleLogLikelihood X Y g) that hthat hmax Δ hΔ hlim

/-- Average sample log-criterion maximizers consistently estimate the full parameter of an identified correctly specified mixture under compactness, population uniqueness and uniform convergence.
Target P001-T12: Section 5.2.5, the 'any subset' sentence, corrected: consistency and efficiency of the mixture ML estimator under identification of the full parameter vector.
Location: p. 199 (PDF p. 217), second paragraph. -/
theorem identified_mixture_ml_consistency_supporting {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {M K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (p : (Fin τ → ℝ) → Fin M → ℝ) (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (Θ : Set (Fin τ → ℝ)) (hc : IsCompact Θ) (θ : Fin τ → ℝ) (hθ : θ∈Θ)
   (hp : ∀ t∈Θ,(∀ m,0 ≤ p t m) ∧ (∑ m,p t m)=1)
   (hg : ∀ t∈Θ,∀ m,Measurable (fun xy : (Fin K → ℝ) × ℝ => g m xy.2 xy.1 t))
   (hnonneg : ∀ t∈Θ,∀ m y x,0 ≤ g m y x t)
   (hnorm : ∀ t∈Θ,∀ m x,(∫⁻ y,ENNReal.ofReal (g m y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=conditionalModelLaw νX κ (mixtureFamily p g) θ)
   (hlog : ∀ t∈Θ,Integrable
     (fun ω => Real.log (mixtureFamily p g (Y 0 ω) (X 0 ω) t)) μ)
   (hpositiveModel : ∀ t∈Θ,∀ᵐ ω ∂μ,0 < mixtureFamily p g (Y 0 ω) (X 0 ω) t)
   (hM : ContinuousOn (expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g)) Θ)
   (hunique : ∀ t∈Θ,expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t ≤ 
     expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) θ ∧
     (expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t=
       expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) θ → t=θ))
   (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n,Measurable (that n))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → sampleLogLikelihood X Y (mixtureFamily p g) n ω t ≤ 
     sampleLogLikelihood X Y (mixtureFamily p g) n ω (that n ω))
   (Δ : ℕ → Ω → ℝ) (hΔ : ∀ n ω t,t∈Θ →
     |sampleLogLikelihood X Y (mixtureFamily p g) n ω t-
       expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t| ≤ Δ n ω)
   (hlim : CP μ Δ 0) : CP μ that θ := by
  
  exact ml_consistency_explicit_uniform_regularities_supporting μ Θ hc θ hθ
    (expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g)) hM hunique
    (sampleLogLikelihood X Y (mixtureFamily p g)) that hthat hmax Δ hΔ hlim


/-- The log normalizer "log(1+exp(xβ))" of the binary logit model
(Definition 5.1.9, p. 183; the grouped ML fit in T84). -/
def logitSoftplus (t : ℝ) : ℝ := Real.log (1+Real.exp t)

/-- The logistic log normalizer has a strict supporting line at every real predictor. -/
theorem logit_softplus_tangent (c t : ℝ) :
  logitSoftplus c+(Real.exp c/(1+Real.exp c))*(t-c) ≤ logitSoftplus t ∧
  (logitSoftplus c+(Real.exp c/(1+Real.exp c))*(t-c)=logitSoftplus t ↔ t=c) := by
  let p : ℝ := Real.exp c/(1+Real.exp c)
  have hd : 0 < 1+Real.exp c := by positivity
  have hp : 0 < p := div_pos (Real.exp_pos _) hd
  have hq : 0 < 1-p := by
    have he : 1-p=1/(1+Real.exp c) := by dsimp [p]; field_simp [hd.ne']; ring
    rw [he]
    positivity
  have hsum : 1-p+p=1 := by ring
  have hr : (1+Real.exp t)/(1+Real.exp c)=(1-p)+p*Real.exp (t-c) := by
    dsimp [p]
    rw [Real.exp_sub]
    field_simp [hd.ne', Real.exp_ne_zero c]
    ring
  have hj := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (t-c)) hq.le hp.le hsum
  have hle : Real.exp (p*(t-c)) ≤ (1+Real.exp t)/(1+Real.exp c) := by
    rw [hr]
    simpa [smul_eq_mul] using hj
  have hlog := Real.log_le_log (Real.exp_pos _) hle
  rw [Real.log_exp, Real.log_div (by positivity) (by positivity)] at hlog
  refine ⟨?_, ?_⟩
  · change logitSoftplus c+p*(t-c) ≤ logitSoftplus t
    unfold logitSoftplus
    linarith
  · constructor
    · intro he
      by_contra hne
      have hne' : (0 : ℝ) ≠ t-c := by intro hz; apply hne; linarith
      have hj' := strictConvexOn_exp.2 (Set.mem_univ (0 : ℝ))
        (Set.mem_univ (t-c)) hne' hq hp hsum
      have hlt : Real.exp (p*(t-c)) < (1+Real.exp t)/(1+Real.exp c) := by
        rw [hr]
        simpa [smul_eq_mul] using hj'
      have hl := Real.log_lt_log (Real.exp_pos _) hlt
      rw [Real.log_exp, Real.log_div (by positivity) (by positivity)] at hl
      change logitSoftplus c+p*(t-c)=logitSoftplus t at he
      unfold logitSoftplus at he
      linarith
    · intro he
      rw [he]
      ring

/-- The logistic log normalizer has its strict global supporting line at log(7/5), with slope 7/12; equality occurs only at that point.
Target P001-T84: Section 6.2.5, the sentence 'In the case where there is a discrete and finite number of values for $\mathbf{X}_i$, the IPW estimator is logically equivalent to the plug-in estimator from Section 6.2.1', as printed.
Location: p. 228 (PDF p. 246), first paragraph. Definition 6.2.7: p. 227 (PDF p. 245). Section 6.2.1 plug-in estimator: p. 219 (PDF p. 237). Section 6.2.4: pp. 225–226 (PDF pp. 243–244). -/
theorem logit_logsumexp_tangent (t : ℝ) :
  logitSoftplus (Real.log (7/5))+(7/12)*(t-Real.log (7/5)) ≤ logitSoftplus t ∧
  (logitSoftplus (Real.log (7/5))+(7/12)*(t-Real.log (7/5))=logitSoftplus t ↔
    t=Real.log (7/5)) := by
  let c : ℝ := Real.log (7/5)
  have hec : Real.exp c=7/5 := Real.exp_log (by norm_num)
  have hr : (1+Real.exp t)/(1+Real.exp c)=5/12+(7/12)*Real.exp (t-c) := by
    rw [Real.exp_sub,hec]
    norm_num
    ring
  have hj := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (t-c))
    (by norm_num : (0 : ℝ) ≤ 5/12) (by norm_num : (0 : ℝ) ≤ 7/12)
    (by norm_num : (5/12 : ℝ)+7/12=1)
  have hle : Real.exp ((7/12)*(t-c)) ≤ (1+Real.exp t)/(1+Real.exp c) := by
    rw [hr]
    simpa [smul_eq_mul] using hj
  have hlog := Real.log_le_log (Real.exp_pos _) hle
  rw [Real.log_exp,Real.log_div (by positivity) (by positivity)] at hlog
  refine ⟨?_,?_⟩
  · change logitSoftplus c+(7/12)*(t-c) ≤ logitSoftplus t
    unfold logitSoftplus
    linarith
  · constructor
    · intro he
      by_contra hne
      have hne' : (0 : ℝ) ≠ t-c := by intro hz; apply hne; change t=c; linarith
      have hj' := strictConvexOn_exp.2 (Set.mem_univ (0 : ℝ))
        (Set.mem_univ (t-c)) hne'
        (by norm_num : (0 : ℝ) < 5/12) (by norm_num : (0 : ℝ) < 7/12)
        (by norm_num : (5/12 : ℝ)+7/12=1)
      have hlt : Real.exp ((7/12)*(t-c)) < (1+Real.exp t)/(1+Real.exp c) := by
        rw [hr]
        simpa [smul_eq_mul] using hj'
      have hl := Real.log_lt_log (Real.exp_pos _) hlt
      rw [Real.log_exp,Real.log_div (by positivity) (by positivity)] at hl
      change logitSoftplus c+(7/12)*(t-c)=logitSoftplus t at he
      unfold logitSoftplus at he
      linarith
    · intro he
      rw [he]
      ring

/-- The grouped Bernoulli logit log likelihood is exactly the sum of r_j times the linear predictor minus N_j times its log normalizer.
Target P001-T84: Section 6.2.5, the sentence 'In the case where there is a discrete and finite number of values for $\mathbf{X}_i$, the IPW estimator is logically equivalent to the plug-in estimator from Section 6.2.1', as printed.
Location: p. 228 (PDF p. 246), first paragraph. Definition 6.2.7: p. 227 (PDF p. 245). Section 6.2.1 plug-in estimator: p. 219 (PDF p. 237). Section 6.2.4: pp. 225–226 (PDF pp. 243–244). -/
theorem grouped_logit_canonical_identity (N r : Fin 3 → ℝ) (a b : ℝ) :
  groupedLogitLikelihood N r a b = ∑ j : Fin 3,
    (r j*(a+b*((![-1,0,1] : Fin 3 → ℝ) j))-
      N j*logitSoftplus (a+b*((![-1,0,1] : Fin 3 → ℝ) j))) := by
  unfold groupedLogitLikelihood
  apply Finset.sum_congr rfl
  intro j hj
  let t := a+b*((![-1,0,1] : Fin 3 → ℝ) j)
  have hp : 0 < 1+Real.exp t := by positivity
  have hr : 1-Real.exp t/(1+Real.exp t)=(1+Real.exp t)⁻¹ := by
    field_simp [hp.ne']
    ring
  change r j*Real.log (Real.exp t/(1+Real.exp t))+
    (N j-r j)*Real.log (1-Real.exp t/(1+Real.exp t)) =
      r j*t-N j*logitSoftplus t
  rw [hr,Real.log_div (Real.exp_ne_zero t) hp.ne',Real.log_exp,Real.log_inv]
  unfold logitSoftplus
  ring

/-- For cell sizes (4,4,4) and responses (2,3,2), the global unique grouped logit ML vector is (log(7/5),0).
Target P001-T84: Section 6.2.5, the sentence 'In the case where there is a discrete and finite number of values for $\mathbf{X}_i$, the IPW estimator is logically equivalent to the plug-in estimator from Section 6.2.1', as printed.
Location: p. 228 (PDF p. 246), first paragraph. Definition 6.2.7: p. 227 (PDF p. 245). Section 6.2.1 plug-in estimator: p. 219 (PDF p. 237). Section 6.2.4: pp. 225–226 (PDF pp. 243–244). -/
theorem missing_grouped_logit_unique (a b : ℝ) :
  groupedLogitLikelihood missingCellSize missingCellResponse a b ≤
    groupedLogitLikelihood missingCellSize missingCellResponse (Real.log (7/5)) 0 ∧
  (groupedLogitLikelihood missingCellSize missingCellResponse a b=
    groupedLogitLikelihood missingCellSize missingCellResponse (Real.log (7/5)) 0 ↔
    a=Real.log (7/5) ∧ b=0) := by
  let c : ℝ := Real.log (7/5)
  have hc (u v : ℝ) : groupedLogitLikelihood missingCellSize missingCellResponse u v=
      7*u-4*(logitSoftplus (u-v)+logitSoftplus u+logitSoftplus (u+v)) := by
    rw [grouped_logit_canonical_identity]
    norm_num [missingCellSize,missingCellResponse,Fin.sum_univ_succ]
    ring
  have h0 : groupedLogitLikelihood missingCellSize missingCellResponse c 0=
      7*c-12*logitSoftplus c := by rw [hc]; simp; ring
  have hminus := logit_logsumexp_tangent (a-b)
  have hcenter := logit_logsumexp_tangent a
  have hplus := logit_logsumexp_tangent (a+b)
  change logitSoftplus c+(7/12)*(a-b-c) ≤ logitSoftplus (a-b) ∧ _ at hminus
  change logitSoftplus c+(7/12)*(a-c) ≤ logitSoftplus a ∧ _ at hcenter
  change logitSoftplus c+(7/12)*(a+b-c) ≤ logitSoftplus (a+b) ∧ _ at hplus
  constructor
  · rw [hc,h0]
    linarith [hminus.1,hcenter.1,hplus.1]
  · constructor
    · intro he
      change groupedLogitLikelihood missingCellSize missingCellResponse a b=
        groupedLogitLikelihood missingCellSize missingCellResponse c 0 at he
      rw [hc,h0] at he
      have ha : a=c := hcenter.2.mp (by linarith [hminus.1,hcenter.1,hplus.1])
      have hm : a-b=c := hminus.2.mp (by linarith [hminus.1,hcenter.1,hplus.1])
      exact ⟨ha,by linarith⟩
    · rintro ⟨rfl,rfl⟩
      rfl

/-- The twelve-unit example has a unique fitted logit ML vector (log(7/5),0), every cell has respondents and nonrespondents, and actual IPW and post-stratification differ.
Target P001-T84: Section 6.2.5, the sentence 'In the case where there is a discrete and finite number of values for $\mathbf{X}_i$, the IPW estimator is logically equivalent to the plug-in estimator from Section 6.2.1', as printed.
Location: p. 228 (PDF p. 246), first paragraph. Definition 6.2.7: p. 227 (PDF p. 245). Section 6.2.1 plug-in estimator: p. 219 (PDF p. 237). Section 6.2.4: pp. 225–226 (PDF pp. 243–244). -/
theorem missing_ipw_logit_ml_counterexample : (∀ a b : ℝ,
    groupedLogitLikelihood missingCellSize missingCellResponse a b ≤ 
      groupedLogitLikelihood missingCellSize missingCellResponse (Real.log (7/5)) 0 ∧
    (groupedLogitLikelihood missingCellSize missingCellResponse a b=
      groupedLogitLikelihood missingCellSize missingCellResponse (Real.log (7/5)) 0 ↔
      a=Real.log (7/5) ∧ b=0)) ∧
   (∀ j : Fin 3,0 < missingCellResponse j ∧ missingCellResponse j < missingCellSize j ∧
      logitProbability (Real.log (7/5)) 0 ((![-1,0,1] : Fin 3 → ℝ) j)=7/12) ∧
   (∑ j,missingCellOutcomeSum j/
      logitProbability (Real.log (7/5)) 0 ((![-1,0,1] : Fin 3 → ℝ) j))/12=3/7 ∧
   (∑ j,missingCellSize j*missingCellOutcomeSum j/missingCellResponse j)/12=5/12 ∧
   (3/7 : ℝ)≠5/12 := by
  refine ⟨missing_grouped_logit_unique,?_,?_,?_,?_⟩
  · intro j
    fin_cases j <;> norm_num [missingCellResponse,missingCellSize,logitProbability,
      Real.exp_log (by norm_num : (0 : ℝ) < 7/5)]
  · norm_num [missingCellOutcomeSum,logitProbability,Fin.sum_univ_succ,
      Real.exp_log (by norm_num : (0 : ℝ) < 7/5)]
  · norm_num [missingCellSize,missingCellOutcomeSum,missingCellResponse,Fin.sum_univ_succ]
  · norm_num

/-- The three-cell causal logit likelihood has the claimed unique global ML fit. -/
theorem causal_grouped_logit_unique (a b : ℝ) :
    groupedLogitLikelihood causalCellSize causalCellTreatment a b ≤
      groupedLogitLikelihood causalCellSize causalCellTreatment 0 (Real.log 2) ∧
    (groupedLogitLikelihood causalCellSize causalCellTreatment a b=
      groupedLogitLikelihood causalCellSize causalCellTreatment 0 (Real.log 2) ↔
      a=0 ∧ b=Real.log 2) := by
  let c : ℝ := Real.log 2
  have hec : Real.exp c=2 := Real.exp_log (by norm_num)
  have hem : Real.exp (-c)=1/2 := by rw [Real.exp_neg, hec]; norm_num
  have hc (u v : ℝ) : groupedLogitLikelihood causalCellSize causalCellTreatment u v=
      9*u+2*v-6*(logitSoftplus (u-v)+logitSoftplus u+logitSoftplus (u+v)) := by
    rw [grouped_logit_canonical_identity]
    norm_num [causalCellSize, causalCellTreatment, Fin.sum_univ_succ]
    ring
  have h0 : groupedLogitLikelihood causalCellSize causalCellTreatment 0 c=
      2*c-6*(logitSoftplus (-c)+logitSoftplus 0+logitSoftplus c) := by
    rw [hc]
    simp
  have hminus := logit_softplus_tangent (-c) (a-b)
  have hcenter := logit_softplus_tangent 0 a
  have hplus := logit_softplus_tangent c (a+b)
  norm_num only [hem, hec, Real.exp_zero, neg_neg] at hminus hcenter hplus
  constructor
  · change groupedLogitLikelihood causalCellSize causalCellTreatment a b ≤
      groupedLogitLikelihood causalCellSize causalCellTreatment 0 c
    rw [hc, h0]
    linarith [hminus.1, hcenter.1, hplus.1]
  · constructor
    · intro he
      change groupedLogitLikelihood causalCellSize causalCellTreatment a b=
        groupedLogitLikelihood causalCellSize causalCellTreatment 0 c at he
      rw [hc, h0] at he
      have ha : a=0 := hcenter.2.mp (by linarith [hminus.1, hcenter.1, hplus.1])
      have hb : a+b=c := hplus.2.mp (by linarith [hminus.1, hcenter.1, hplus.1])
      exact ⟨ha, by change b=c; linarith⟩
    · rintro ⟨rfl,rfl⟩
      rfl

/-- The eighteen-unit example has the unique fitted logit ML vector (0,log 2), both arms in every cell, and IPW 59/36 against post-stratification one.
Target P001-T96: Section 7.2.6, the sentence 'In the case where we have a discrete and finite number of values for $\mathbf{X}_i$, the IPW estimator is logically equivalent to the plug-in estimator from Section 7.2.1', as printed.
Location: p. 266 (PDF p. 284), paragraph after Definition 7.2.6. Section 7.2.1 plug-in estimator: p. 256 (PDF p. 274). Section 7.2.5: p. 264 (PDF p. 282). -/
theorem causal_ipw_logit_ml_counterexample : (∀ a b : ℝ,
    groupedLogitLikelihood causalCellSize causalCellTreatment a b ≤ 
      groupedLogitLikelihood causalCellSize causalCellTreatment 0 (Real.log 2) ∧
    (groupedLogitLikelihood causalCellSize causalCellTreatment a b=
      groupedLogitLikelihood causalCellSize causalCellTreatment 0 (Real.log 2) ↔
      a=0 ∧ b=Real.log 2)) ∧
   (∀ j : Fin 3,0 < causalCellTreatment j ∧ causalCellTreatment j < causalCellSize j ∧
     logitProbability 0 (Real.log 2) ((![-1,0,1] : Fin 3 → ℝ) j)=
       ((![1/3,1/2,2/3] : Fin 3 → ℝ) j)) ∧
   (∑ j,(causalCellTreatedSum j/
     logitProbability 0 (Real.log 2) ((![-1,0,1] : Fin 3 → ℝ) j)-
     causalCellControlSum j/(1-logitProbability 0 (Real.log 2) ((![-1,0,1] : Fin 3 → ℝ) j))))/18=59/36 ∧
   (∑ j,causalCellSize j*(causalCellTreatedSum j/causalCellTreatment j-
      causalCellControlSum j/(causalCellSize j-causalCellTreatment j)))/18=1 ∧
   (59/36 : ℝ)≠1 := by
  refine ⟨causal_grouped_logit_unique, ?_, ?_, ?_, by norm_num⟩
  · intro j
    fin_cases j <;> norm_num [causalCellTreatment, causalCellSize, logitProbability,
      Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ)<2)]
  · norm_num [causalCellTreatedSum, causalCellControlSum, logitProbability,
      Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ)<2), Fin.sum_univ_succ]
  · norm_num [causalCellSize, causalCellTreatment, causalCellTreatedSum,
      causalCellControlSum, Fin.sum_univ_succ]



theorem uniform_index_integral {n : ℕ} [NeZero n] (f : Fin n → ℝ) :
    ∫ i, f i ∂(PMF.uniformOfFintype (Fin n)).toMeasure = (∑ i, f i)/(n:ℝ) := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

theorem uniform_resampling_integral {n : ℕ} [NeZero n] (f : (Fin n → Fin n) → ℝ) :
    ∫ a, f a ∂(Measure.pi fun _ : Fin n => (PMF.uniformOfFintype (Fin n)).toMeasure) =
      (∑ a, f a)/((n:ℝ)^n) := by
  rw [integral_fintype .of_finite]
  have hm (a : Fin n → Fin n) :
      (Measure.pi fun _ : Fin n => (PMF.uniformOfFintype (Fin n)).toMeasure).real {a} =
        ((n:ℝ)^n)⁻¹ := by
    simp [Measure.real, Measure.pi_singleton,
      ENNReal.toReal_pow, ENNReal.toReal_inv]
  simp_rw [hm, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

theorem iid_sample_variance_cp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ) :
    CP μ (sampleVariance X) (var μ (X 0)) := by
  let XS : ℕ → Ω → ℝ := fun i ω => (X i ω)^2
  have hXS : IID μ XS := by
    refine ⟨?_,?_,?_⟩
    · intro i; exact (hiid.1 i).pow_const 2
    · exact hiid.2.1.comp (fun (_ : ℕ) (x : ℝ) => x^2) (fun _ => by fun_prop)
    · intro i; exact (hiid.2.2 i).comp (u := fun x : ℝ => x^2) (by fun_prop)
  have hAS := strong_law_ae_real X (h2.integrable one_le_two)
    (fun i j hij => hiid.2.1.indepFun hij) hiid.2.2
  have hSS := strong_law_ae_real XS h2.integrable_sq
    (fun i j hij => hXS.2.1.indepFun hij) hXS.2.2
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => sampleVariance X n ω)
      atTop (nhds (var μ (X 0))) := by
    filter_upwards [hAS,hSS] with ω hω hωS
    have h := hωS.sub (hω.pow 2)
    simpa only [sampleVariance,sampleMean,XS,var,variance_eq_sub h2,mean,Pi.pow_apply] using h
  have hXi : ∀ i, Measurable (X i) := hiid.1
  have hm (n : ℕ) : Measurable (sampleVariance X n) := by
    unfold sampleVariance sampleMean
    fun_prop
  have hmeasure := tendstoInMeasure_of_tendsto_ae
    (fun n => (hm n).aestronglyMeasurable) hlim
  intro ε hε
  simpa only [prob,Measure.real] using
    (tendstoInMeasure_iff_measureReal_dist.mp hmeasure) ε hε

/-- For every nonempty fixed sample, n times the ordinary bootstrap variance of its mean equals the empirical second moment minus squared empirical mean.
Target P001-T62: Section 3.4.3, consistency of the bootstrap standard deviation for the standard error, corrected: the added moment condition.
Location: p. 131 (PDF p. 149), sentence after the four bootstrap steps; Definition 3.2.32, pp. 113–114 (PDF pp. 131–132). -/
theorem bootstrap_sample_mean_exact_variance {n : ℕ} (hn : 0 < n) (X : Fin n → ℝ) :
   (n : ℝ)*bootVar finiteSampleMean X=(∑ i,(X i)^2)/(n : ℝ)-(finiteSampleMean X)^2 := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let P := (PMF.uniformOfFintype (Fin n)).toMeasure
  let Q := Measure.pi fun _ : Fin n => P
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hX : MemLp X 2 P := eLpNorm_lt_top_of_finite (by fun_prop)
  have hint (i : Fin n) : ∫ a, X (a i) ∂Q = ∫ j, X j ∂P := by
    have hmp := measurePreserving_eval (fun _ : Fin n => P) i
    have hh : AEStronglyMeasurable X (Q.map fun a : Fin n → Fin n => a i) := by
      rw [hmp.map_eq]
      exact hX.aestronglyMeasurable
    rw [← hmp.map_eq]
    exact (integral_map hmp.measurable.aemeasurable hh).symm
  have hmean : ∫ a, finiteSampleMean (resample X a) ∂Q = finiteSampleMean X := by
    change ∫ a, (∑ i, X (a i))/(n:ℝ) ∂Q = _
    rw [integral_div, integral_finsetSum _ (fun i _ => (show Integrable (fun a : Fin n → Fin n => X (a i)) Q from .of_finite))]
    simp_rw [hint]
    rw [uniform_index_integral]
    simp [finiteSampleMean, hn0]
  have hboot : bootMean finiteSampleMean X = finiteSampleMean X := by
    rw [← hmean, uniform_resampling_integral]
    rfl
  have hvar : variance (fun a : Fin n → Fin n => finiteSampleMean (resample X a)) Q =
      variance X P / (n:ℝ) := by
    have hsum := variance_sum_pi (μ := fun _ : Fin n => P) (X := fun _ : Fin n => X) (fun _ => hX)
    have hfun : (∑ i : Fin n, fun a : Fin n → Fin n => X (a i)) =
        fun a : Fin n → Fin n => ∑ i, X (a i) := by funext a; simp
    rw [hfun] at hsum
    change variance (fun a : Fin n → Fin n => (∑ i, X (a i))/(n:ℝ)) Q = _
    simp_rw [div_eq_mul_inv, mul_comm _ ((n:ℝ)⁻¹)]
    rw [variance_const_mul, hsum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hbvar : bootVar finiteSampleMean X =
      variance (fun a : Fin n → Fin n => finiteSampleMean (resample X a)) Q := by
    rw [variance_eq_integral (by exact (show Measurable (fun a : Fin n → Fin n => finiteSampleMean (resample X a)) from measurable_of_countable _).aemeasurable), hmean, uniform_resampling_integral]
    simp only [bootVar, hboot]
  rw [hbvar, hvar, variance_eq_sub hX, uniform_index_integral, uniform_index_integral]
  change (n:ℝ)*(((∑ i, (X i)^2)/(n:ℝ)-((∑ i,X i)/(n:ℝ))^2)/(n:ℝ)) = _
  dsimp [finiteSampleMean]
  field_simp

/-- For iid observations with finite positive variance the ideal bootstrap sampling variance and standard error for the sample mean are consistent.
Target P001-T62: Section 3.4.3, consistency of the bootstrap standard deviation for the standard error, corrected: the added moment condition.
Location: p. 131 (PDF p. 149), sentence after the four bootstrap steps; Definition 3.2.32, pp. 113–114 (PDF pp. 131–132). -/
theorem bootstrap_sample_mean_consistency {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ) (hv : 0 < var μ (X 0)) :
   CP μ (fun n ω => (n : ℝ)*bootVar finiteSampleMean (firstSample X n ω)) (var μ (X 0)) ∧
   CP μ (fun n ω => Real.sqrt n*Real.sqrt (bootVar finiteSampleMean (firstSample X n ω)))
     (Real.sqrt (var μ (X 0))) := by
  have he : (fun (n : ℕ) ω => (n : ℝ)*bootVar finiteSampleMean (firstSample X n ω)) = sampleVariance X := by
    funext n ω
    by_cases hn : n = 0
    · simp [hn,sampleVariance,sampleMean]
    · rw [bootstrap_sample_mean_exact_variance (Nat.pos_of_ne_zero hn)]
      simp only [finiteSampleMean,firstSample,sampleVariance,sampleMean]
      rw [Fin.sum_univ_eq_sum_range (fun i => (X i ω)^2) n,
        Fin.sum_univ_eq_sum_range (fun i => X i ω) n]
  have hcp : CP μ (fun n ω => (n : ℝ)*bootVar finiteSampleMean (firstSample X n ω))
      (var μ (X 0)) := he ▸ iid_sample_variance_cp μ X hiid h2
  refine ⟨hcp,?_⟩
  have hs := probability_convergence_continuous_at μ _ _ Real.sqrt hcp Real.continuous_sqrt.continuousAt
  simpa only [Real.sqrt_mul (Nat.cast_nonneg _)] using hs


/-- The covariance matrix with corrected coordinate indices is symmetric and has coordinate variances on its diagonal.
Target P001-T48: Definition 2.3.1 (Covariance Matrix), the index quantifier, corrected; with Theorem 2.3.2 (Multivariate Variance Rule).
Location: p. 84 (PDF p. 102). -/
theorem covariance_matrix_symmetry_and_diagonal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K : ℕ} (X : Ω → Fin K → ℝ) (h2 : ∀ k,MemLp (fun ω => X ω k) 2 μ) :
   (covarianceMatrix μ X).IsSymm ∧
   ∀ k,covarianceMatrix μ X k k=var μ (fun ω => X ω k) := by
  
  constructor
  · apply Matrix.IsSymm.ext
    intro i j
    exact covariance_comm (fun ω => X ω j) (fun ω => X ω i)
  · intro k
    exact covariance_self (h2 k).aemeasurable

/-- The corrected polynomial squared-residual criterion is the OLS criterion on powers zero through J; with nonsingular Gram matrix its unique minimizer is the OLS coefficient vector.
Target P001-T70: Definition 4.3.9 (Polynomial Least Squares Sieve Estimator), the least squares criterion, corrected (the missing square).
Location: p. 169 (PDF p. 187), the display defining $\hat{\boldsymbol\beta}$ (the definition begins on p. 168, PDF p. 186). -/
theorem polynomial_squared_criterion_ols {n J : ℕ} (X Y : Fin n → ℝ)
   (P : Matrix (Fin n) (Fin (J+1)) ℝ) (hP : ∀ i k,P i k=X i^k.val)
   (hunit : IsUnit (P.transpose*P).det) :
   (∀ b : Fin (J+1) → ℝ,olsRSS P Y b=∑ i,(Y i-∑ k,b k*X i^k.val)^2) ∧
   (∀ b : Fin (J+1) → ℝ,olsRSS P Y (olsCoef P Y) ≤ olsRSS P Y b ∧
     (olsRSS P Y b=olsRSS P Y (olsCoef P Y) ↔ b=olsCoef P Y)) := by
  refine ⟨?_,(ols_correct_rows_solution_residuals P Y hunit ?_).1⟩
  · intro b
    unfold olsRSS Matrix.mulVec dotProduct
    simp_rw [hP,mul_comm]
  · intro i
    rw [hP]
    simp

/-- Under the stated constant-scale normal location-model factorization, the residual Y - m(X) has law N(0,s²) and is independent of X. Identifying m as an IsCEF additionally requires integrability of Y and m(X).
Target P001-T74: Section 5.1.1, the comparison of the classical linear model's errors with deviations from the CEF, corrected ('uncorrelated with' for 'independent of'); with Theorem 2.2.19 (Properties of Deviations from the CEF).
Location: p. 181 (PDF p. 199), paragraph after the display $Y = \mathbf{X}\boldsymbol\beta + \varepsilon$. Theorem 2.2.19: p. 74 (PDF p. 92), proof on pp. 74–75. -/
theorem classical_normal_residual_independent {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (Y : Ω → ℝ)
   (hX : Measurable X) (hY : Measurable Y) (m : E → ℝ) (hm : Measurable m)
   (s : ℝ) (hs : 0 < s)
   (hlaw : μ.map (fun ω => (X ω,Y ω))=
     ((μ.map X).prod (gaussianReal 0 ⟨s^2,sq_nonneg _⟩)).map
       (fun xy => (xy.1,m xy.1+xy.2))) :
   μ.map (fun ω => Y ω-m (X ω))=gaussianReal 0 ⟨s^2,sq_nonneg _⟩ ∧
   IndepFun X (fun ω => Y ω-m (X ω)) μ := by
  let v : ℝ≥0 := ⟨s^2,sq_nonneg _⟩
  haveI : IsProbabilityMeasure (gaussianReal (0 : ℝ) v) := inferInstance
  let ν := (μ.map X).prod (gaussianReal 0 v)
  let T : E × ℝ → E × ℝ := fun xy => (xy.1,m xy.1+xy.2)
  let S : E × ℝ → E × ℝ := fun xy => (xy.1,xy.2-m xy.1)
  have hT : Measurable T := measurable_fst.prodMk ((hm.comp measurable_fst).add measurable_snd)
  have hS : Measurable S := measurable_fst.prodMk (measurable_snd.sub (hm.comp measurable_fst))
  have hXY : Measurable (fun ω => (X ω,Y ω)) := hX.prodMk hY
  have hR : Measurable (fun ω => Y ω-m (X ω)) := hY.sub (hm.comp hX)
  have hXR : Measurable (fun ω => (X ω,Y ω-m (X ω))) := hX.prodMk hR
  have hJoint : μ.map (fun ω => (X ω,Y ω-m (X ω)))=ν := by
    have he : (fun ω => (X ω,Y ω-m (X ω)))=S ∘ (fun ω => (X ω,Y ω)) := rfl
    rw [he, ← Measure.map_map hS hXY, hlaw]
    change (ν.map T).map S=ν
    rw [Measure.map_map hS hT]
    have hST : S ∘ T=id := by
      funext xy
      simp [S,T,Function.comp_def]
    rw [hST,Measure.map_id]
  have hLaw : μ.map (fun ω => Y ω-m (X ω))=gaussianReal 0 v := by
    have hmap := congrArg (fun ρ : Measure (E × ℝ) => ρ.map Prod.snd) hJoint
    rw [Measure.map_map measurable_snd hXR] at hmap
    dsimp only [ν] at hmap
    rw [Measure.map_snd_prod] at hmap
    simpa [Function.comp_def] using hmap
  refine ⟨hLaw,?_⟩
  apply (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hR.aemeasurable).mpr
  rw [hLaw]
  exact hJoint


/-- Embedding a probability-law CDF in the sup-norm space retains its value at every real point.
Target P001-T57: Theorem 3.3.6 (Asymptotic Normality of Plug-In Estimators), corrected with the non-degeneracy condition.
Location: p. 120 (PDF p. 138), Theorem 3.3.6 and footnote 31; Definition 3.2.28, p. 112 (PDF p. 130). -/
theorem kolmogorov_embedding_preserves_cdf_supporting (ν : Measure ℝ) [IsProbabilityMeasure ν] :
   ∀ x : ℝ,kolmogorovEmbed (cdf ν id) x=cdf ν id x := by
  have hb : Memℓp (cdf ν id) ∞ := by
    apply memℓp_infty
    refine ⟨1, ?_⟩
    rintro y ⟨x,rfl⟩
    change ‖cdf ν id x‖ ≤ 1
    unfold cdf AronowAudit.P001.prob
    rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    exact measureReal_le_one
  intro x
  simp [kolmogorovEmbed,hb]

/-- Under the open-support condition, an existing coordinate derivative of one continuous CEF version is also the derivative of every other continuous version.
Target P001-T4: Definition 4.3.7 (Partial Derivative at the Average), corrected with a support condition at the covariate mean.
Location: p. 167 (PDF p. 185), Definition 4.3.7; p. 168 (PDF p. 186), first paragraph. -/
theorem pda_derivative_transfers_on_open_support {K : ℕ} (U : Set (Fin K → ℝ)) (hU : IsOpen U) (x : Fin K → ℝ)
   (hx : x∈U) (m m' : (Fin K → ℝ) → ℝ)
   (hm : ContinuousOn m U) (hm' : ContinuousOn m' U)
   (heq : m=ᵐ[volume.restrict U] m') (k : Fin K) (a : ℝ)
   (hd : HasDerivAt (fun t => m (Function.update x k (x k+t))) a 0) :
   HasDerivAt (fun t => m' (Function.update x k (x k+t))) a 0 := by
  have he := (pda_unique_on_open_support_supporting U hU x hx m m' hm hm' heq k).1
  apply hd.congr_of_eventuallyEq
  have ht : Continuous (fun t : ℝ => Function.update x k (x k+t)) := by fun_prop
  have hmem : ∀ᶠ t in nhds (0 : ℝ),Function.update x k (x k+t)∈U :=
    ht.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hx)
  filter_upwards [hmem] with t ht
  exact (he ht).symm


/-- The two explicit full mixture parameters give identical normalized sample laws at every sample size, and no estimator in that common experiment can be consistent for both parameter vectors.
Target P001-T11: Section 5.2.5, the sentence 'If any subset of the models ... jointly characterize the conditional distribution of $Y$, then this estimator is consistent and asymptotically efficient', as printed.
Location: p. 199 (PDF p. 217), second paragraph; the mixture and its parameter vector: pp. 198–199 (PDF pp. 216–217). -/
theorem unused_component_counterexample_full_supporting {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (that : ℕ → Ω → Fin 3 → ℝ) (hm : ∀ n,Measurable (that n)) :
   disjointMixture 1 (1/3) (1/4)=disjointMixture 1 (1/3) (3/4) ∧
   (∑ i : Fin 4,disjointMixture 1 (1/3) (1/4) i)=1 ∧
   (∀ i : Fin 4,0 ≤ disjointMixture 1 (1/3) (1/4) i) ∧
   (∀ n (y : Fin n → Fin 4),(∏ i,disjointMixture 1 (1/3) (1/4) (y i))=
     ∏ i,disjointMixture 1 (1/3) (3/4) (y i)) ∧
   ¬ (CP μ that (![1,1/3,1/4] : Fin 3 → ℝ) ∧ CP μ that (![1,1/3,3/4] : Fin 3 → ℝ)) := by
  rcases unused_component_nonidentification_supporting with ⟨he,hn,hp,hs,hdisjoint⟩
  exact ⟨he,hn,hp,hs,nonidentification_no_two_consistent_targets_supporting μ that hm⟩

/-- The first K+1 geometric first-moment terms equal one minus (K+2) times the remaining geometric tail.
Target P001-T1: Section 3.3.1, the sentence 'our assumption about finite variance was sufficient to imply that the population mean is well behaved', read with footnote 31, as printed.
Location: p. 120 (PDF p. 138), paragraph after Theorem 3.3.6, and footnote 31. The mean functional $T_{\mathrm{E}}$: p. 118 (PDF p. 136). -/
theorem geometric_partial_first_moment (K : ℕ) : (∑ k∈Finset.range (K+1),(k : ℝ)*geoMass k)=
   1-((K : ℝ)+2)*(1/2 : ℝ)^(K+1) := by
  induction K with
  | zero => norm_num [geoMass]
  | succ K ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [geoMass,pow_succ,Nat.cast_succ,Nat.cast_add,Nat.cast_one]
    ring

/-- The first K+1 geometric second-moment terms equal three minus (K²+4K+6) times the remaining geometric tail.
Target P001-T1: Section 3.3.1, the sentence 'our assumption about finite variance was sufficient to imply that the population mean is well behaved', read with footnote 31, as printed.
Location: p. 120 (PDF p. 138), paragraph after Theorem 3.3.6, and footnote 31. The mean functional $T_{\mathrm{E}}$: p. 118 (PDF p. 136). -/
theorem geometric_partial_second_moment (K : ℕ) : (∑ k∈Finset.range (K+1),(k : ℝ)^2*geoMass k)=
   3-((K : ℝ)^2+4*(K : ℝ)+6)*(1/2 : ℝ)^(K+1) := by
  induction K with
  | zero => norm_num [geoMass]
  | succ K ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [geoMass,pow_succ,Nat.cast_succ,Nat.cast_add,Nat.cast_one]
    ring

/-- For a positive variance estimate, the studentized statistic has the exact multiplicative form used in the proof, and open confidence-interval coverage is equivalent to lying between the two normal critical values.
Target P001-T128: Theorem 3.4.2 (Normal Approximation–Based Confidence Interval).
Location: p. 125 (PDF p. 143); proof on pp. 125–126 (PDF pp. 143–144). Definition 3.4.1: p. 124 (PDF p. 142). -/
theorem studentization_finite_identity_and_coverage (n : ℕ) (hn : 0 < n) (that θ v φ z : ℝ) (hv : 0 < v) (hφ : 0 < φ) :
   (that-θ)/Real.sqrt v=(Real.sqrt n*(that-θ)/φ)*(φ/Real.sqrt ((n : ℝ)*v)) ∧
   (θ∈Set.Ioo (that-z*Real.sqrt v) (that+z*Real.sqrt v) ↔
     (-z < (that-θ)/Real.sqrt v ∧ (that-θ)/Real.sqrt v < z)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnS : Real.sqrt (n : ℝ)≠0 := (Real.sqrt_pos.2 hnR).ne'
  have hvS : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  constructor
  · rw [Real.sqrt_mul (le_of_lt hnR)]
    field_simp [hnS,hvS.ne',hφ.ne']
  · rw [Set.mem_Ioo,lt_div_iff₀ hvS,div_lt_iff₀ hvS]
    constructor <;> intro h <;> constructor <;> nlinarith [h.1,h.2]


/-- Adding one common intercept to all scores leaves the nearest-donor algorithm, including its fixed tie choice, unchanged.
Target P001-T16: Section 7.2.4 and footnote 20, corrected: for nearest-neighbour matching the ordinary bootstrap can give inconsistent standard errors even without bias, and root-$n$ consistency and bootstrap validity are separate questions.
Location: p. 264 (PDF p. 282), end of Section 7.2.4 and footnote 13; p. 279 (PDF p. 297), footnote 20. -/
theorem nearest_donor_common_shift {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool) (a : ℝ) (i : Fin n) :
   nearestDonor (fun j => a+p j) r i=nearestDonor p r i := by
  simp only [nearestDonor,add_sub_add_left_eq_sub]

/-- The specified estimated score and true propensity score give exactly the same donor for every unit in every fixed sample.
Target P001-T16: Section 7.2.4 and footnote 20, corrected: for nearest-neighbour matching the ordinary bootstrap can give inconsistent standard errors even without bias, and root-$n$ consistency and bootstrap validity are separate questions.
Location: p. 264 (PDF p. 282), end of Section 7.2.4 and footnote 13; p. 279 (PDF p. 297), footnote 20. -/
theorem estimated_score_matches_equal {n : ℕ} (s : Fin n → ℝ × Bool × Bool) (r : Fin n → Bool) (i : Fin n) :
   nearestDonor (estimatedMatchScore s) r i=nearestDonor (fun j => (s j).1) r i := by
  have he : estimatedMatchScore s=
      (fun j => (estimatedMatchIntercept s-1/4)+(s j).1) := by
    funext j
    unfold estimatedMatchScore
    ring
  rw [he]
  exact nearest_donor_common_shift _ r _ i

/-- For every sample, rematching with the specified estimated scores gives exactly the known-score matching statistic.
Target P001-T16: Section 7.2.4 and footnote 20, corrected: for nearest-neighbour matching the ordinary bootstrap can give inconsistent standard errors even without bias, and root-$n$ consistency and bootstrap validity are separate questions.
Location: p. 264 (PDF p. 282), end of Section 7.2.4 and footnote 13; p. 279 (PDF p. 297), footnote 20. -/
theorem estimated_matching_statistic_equal {n : ℕ} (s : Fin n → ℝ × Bool × Bool) : causalMatchEstimated s=causalMatch s := by
  unfold causalMatchEstimated causalMatch
  simp only [estimated_score_matches_equal]


/-- For every nonempty binary sample, the unique likelihood maximum over [1/10,9/10] is the sample success fraction clipped to that interval.
Target P001-T7: Theorem 5.2.8 (The ML Estimator Is Consistent for the Minimum KL Divergence Predictor), with the target defined by the KL divergence at a fixed $\mathbf{x}$, as printed.
Location: p. 195 (PDF p. 213), Theorem 5.2.8 and Definition 5.2.7. -/
theorem clipped_bernoulli_mle {n : ℕ} (hn : 0 < n) (Y : Fin n → ℝ) (hY : ∀ i,Y i=0 ∨ Y i=1) :
   let tstar := clip (1/10) (9/10) ((∑ i,Y i)/(n : ℝ))
   tstar∈Set.Icc (1/10 : ℝ) (9/10) ∧
   ∀ t∈Set.Icc (1/10 : ℝ) (9/10),
     (∏ i,if Y i=1 then t else 1-t) ≤ (∏ i,if Y i=1 then tstar else 1-tstar) ∧
     ((∏ i,if Y i=1 then t else 1-t)=(∏ i,if Y i=1 then tstar else 1-tstar) ↔ t=tstar) := by
  let q : ℝ := (∑ i,Y i)/(n:ℝ)
  let s := clip (1/10) (9/10) q
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hq0 : 0 ≤ q := div_nonneg (Finset.sum_nonneg (fun i _ => by rcases hY i with h|h <;> simp [h])) hnR.le
  have hq1 : q ≤ 1 := by
    apply (div_le_iff₀ hnR).mpr
    have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin n))) =>
      (show Y i ≤ (1:ℝ) by rcases hY i with h|h <;> simp [h]))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,one_mul] using hh
  have hs : s∈Set.Icc (1/10:ℝ) (9/10) :=
    ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  have hpos (t : ℝ) (ht : t∈Set.Icc (1/10:ℝ) (9/10)) :
      0 < ∏ i,if Y i=1 then t else 1-t := by
    apply Finset.prod_pos
    intro i _
    split_ifs <;> linarith [ht.1,ht.2]
  have hlog (t : ℝ) (ht : t∈Set.Icc (1/10:ℝ) (9/10)) :
      Real.log (∏ i,if Y i=1 then t else 1-t) =
        (n:ℝ)*(q*Real.log t+(1-q)*Real.log (1-t)) := by
    rw [Real.log_prod (fun i _ => (show (if Y i=1 then t else 1-t)≠0 by
      split_ifs <;> linarith [ht.1,ht.2]))]
    have hi (i : Fin n) : Real.log (if Y i=1 then t else 1-t) =
        Y i*Real.log t+(1-Y i)*Real.log (1-t) := by
      rcases hY i with hh|hh <;> simp [hh]
    simp_rw [hi]
    rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul,Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    dsimp [q]
    field_simp
    <;> ring
  refine ⟨hs,?_⟩
  intro t ht
  by_cases he : t=s
  · subst t
    exact ⟨le_rfl,by simp [s,q]⟩
  · have hdir : (t-s)*(q-s) ≤ 0 := by
      by_cases hlo : q ≤ 1/10
      · have hs' : s=1/10 := by dsimp [s,clip]; rw [min_eq_right (by linarith),max_eq_left hlo]
        rw [hs']
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith [ht.1]) (by linarith)
      · by_cases hhi : 9/10 ≤ q
        · have hs' : s=9/10 := by dsimp [s,clip]; rw [min_eq_left hhi,max_eq_right (by norm_num)]
          rw [hs']
          exact mul_nonpos_of_nonpos_of_nonneg (by linarith [ht.2]) (by linarith)
        · have hs' : s=q := by dsimp [s,clip]; rw [min_eq_right (le_of_not_ge hhi),max_eq_right (le_of_not_ge hlo)]
          simp [hs']
    have hl := bernoulli_log_strict_max q s t hq0 hq1 (by linarith [hs.1]) (by linarith [hs.2])
      (by linarith [ht.1]) (by linarith [ht.2]) hdir he
    have hp : (∏ i,if Y i=1 then t else 1-t) < ∏ i,if Y i=1 then s else 1-s := by
      apply (Real.log_lt_log_iff (hpos t ht) (hpos s hs)).mp
      rw [hlog t ht,hlog s hs]
      exact mul_lt_mul_of_pos_left hl hnR
    exact ⟨hp.le,⟨fun h => (hp.ne h).elim,fun h => (he h).elim⟩⟩

/-- The slope penalty is nonnegative, homogeneous and subadditive, and vanishes at the unit-intercept vector even though its full l1 norm is one.
Target P001-T71: Definition 4.3.10 (Lasso Estimator), corrected: the coefficient vector in $\mathbb{R}^{K+1}$ and the penalty on the slope coefficients.
Location: pp. 169–170 (PDF pp. 187–188). -/
theorem slope_penalty_seminorm_and_unpenalized_intercept {K : ℕ} (b c : Fin (K+1) → ℝ) :
   0 ≤ slopePenalty b ∧
   (∀ a : ℝ,slopePenalty (a • b)=|a| *slopePenalty b) ∧
   slopePenalty (b+c) ≤ slopePenalty b+slopePenalty c ∧
   slopePenalty (Pi.single 0 (1 : ℝ) : Fin (K+1) → ℝ)=0 ∧
   (∑ j : Fin (K+1),|(Pi.single 0 (1 : ℝ) : Fin (K+1) → ℝ) j|)=1 := by
  refine ⟨Finset.sum_nonneg (fun k hk => abs_nonneg _), ?_, ?_, ?_, ?_⟩
  · intro a
    simp [slopePenalty,abs_mul,← Finset.mul_sum]
  · unfold slopePenalty
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k hk
    exact abs_add_le _ _
  · simp [slopePenalty,Pi.single_apply,Fin.succ_ne_zero]
  · rw [Fin.sum_univ_succ]
    simp [Pi.single_apply,Fin.succ_ne_zero]

/-- Every conditional binary probability law gives a propensity in [0,1] at every covariate value in its domain.
Target P001-T82: Section 6.2.4, the range of the response propensity and the description of impossible estimates, corrected.
Location: p. 225 (PDF p. 243), Section 6.2.4, first paragraph, last sentence on the page. -/
theorem conditional_kernel_propensity_range {E : Type*} (κ : E → Measure Bool) (hκ : ∀ x,IsProbabilityMeasure (κ x)) :
   ∀ x,kernelPropensity κ x∈Set.Icc (0 : ℝ) 1 := by
  intro x
  letI := hκ x
  exact ⟨ENNReal.toReal_nonneg,measureReal_le_one⟩

/-- Convergence in probability to v is equivalent to convergence of the centered statistic to zero, as in footnote 23.
Target P001-T55: Definition 3.2.32 (Consistency of Sampling Variance and Standard Error Estimators) and footnote 23, with the estimator's hat restored in four places.
Location: pp. 113–114 (PDF pp. 131–132), Definition 3.2.32; footnote 23, p. 114 (PDF p. 132). -/
theorem probability_convergence_centering_equivalence_supporting {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
   (V : ℕ → Ω → ℝ) (v : ℝ) :
   CP μ V v ↔ CP μ (fun n ω => V n ω-v) 0 := by
  simp only [CP,Real.dist_eq,sub_zero]


/-- The fair-die CDF at minus one, one, one and a half, two, six and seven is respectively zero, one sixth, one sixth, one third, one and one.
Target P001-T28: Example 1.2.13, first sentence, corrected: the CDF of a discrete random variable as a sum of jumps, and its step shape when the range is finite.
Location: p. 23 (PDF p. 41), Example 1.2.13, first sentence; the analogy on p. 116 (PDF p. 134). -/
theorem fair_die_cdf_examples : fprob fairDieLaw (fun i => fairDieValue i ≤  -1)=0 ∧
   fprob fairDieLaw (fun i => fairDieValue i ≤ 1)=1/6 ∧
   fprob fairDieLaw (fun i => fairDieValue i ≤ 3/2)=1/6 ∧
   fprob fairDieLaw (fun i => fairDieValue i ≤ 2)=1/3 ∧
   fprob fairDieLaw (fun i => fairDieValue i ≤ 6)=1 ∧
   fprob fairDieLaw (fun i => fairDieValue i ≤ 7)=1 := by
  norm_num [fprob,fairDieLaw,fairDieValue,Fin.sum_univ_succ]

/-- The printed six-unit MCAR respondent-mean estimate is three quarters, and its binary-covariate MAR post-stratified estimate is seven ninths.
Target P001-T111: Theorem 6.1.6 (Expected Value under MCAR), Theorem 6.1.9 (Expected Value under MAR) and Theorem 6.1.10 (CEF under MAR); with the estimates of Examples 6.1.7 and 6.2.1.
Location: Definition 6.1.5 and Theorem 6.1.6: p. 213 (PDF p. 231). Example 6.1.7: p. 214 (PDF p. 232). Definition 6.1.8: p. 215 (PDF p. 233). Theorem 6.1.9: p. 216 (PDF p. 234). Theorem 6.1.10: p. 217 (PDF p. 235). Section 6.2.1 and Example 6.2.1: pp. 219–220 (PDF pp. 237–238). -/
theorem missing_mcar_mar_sample_estimates : respondentMean stableExampleYstar stableExampleR=3/4 ∧
   poststratifiedMissingMean stableExampleYstar stableExampleR stableExampleX=7/9 := by
  simp only [respondentMean,poststratifiedMissingMean,Fin.sum_univ_succ]
  norm_num [stableExampleYstar,stableExampleR,stableExampleX]


/-- The six-unit binary causal example gives estimated lower ATE bound minus two sixths and upper bound four sixths.
Target P001-T114: Theorem 7.1.7 (Sharp Bounds for the ATE) and the width of the bounds; with the estimates of Example 7.1.6.
Location: Theorem 7.1.7: p. 241 (PDF p. 259); proof on pp. 241–242 (PDF pp. 259–260). Width: pp. 242–243 (PDF pp. 260–261). Example 7.1.6: p. 240 (PDF p. 258). -/
theorem binary_causal_sample_bound_estimates : (∑ i : Fin 6,ateLower (binaryCausalExampleY i) (stableExampleR i) 0 1)/6= -2/6 ∧
   (∑ i : Fin 6,ateUpper (binaryCausalExampleY i) (stableExampleR i) 0 1)/6=4/6 := by
  norm_num [ateLower,ateUpper,binaryCausalExampleY,stableExampleR,Fin.sum_univ_succ]

/-- For every positive number of iid clusters and positive fixed cluster size, the sampling variance equals the double within-cluster covariance sum divided by l*m².
Target P001-T63: Section 3.5.1, the sentence before Theorem 3.5.6 (mean of the cluster averages), corrected; with Theorems 3.5.3, 3.5.4, 3.5.5 and 3.5.6 for the cluster sample mean.
Location: Sentence: p. 138 (PDF p. 156). Definitions 3.5.1, 3.5.2: p. 136 (PDF p. 154). Theorems 3.5.3–3.5.5: p. 137 (PDF p. 155). Theorem 3.5.6: p. 138 (PDF p. 156). -/
theorem cluster_variance_double_covariance_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {m : ℕ} (hm : 0 < m) (X : ℕ → Ω → Fin m → ℝ) (hiid : IID μ X)
   (h2 : ∀ j,MemLp (fun ω => X 0 ω j) 2 μ) (l : ℕ) (hl : 0 < l) :
   var μ (clusterMean X l)=
     (∑ j,∑ k,covariance (fun ω => X 0 ω j) (fun ω => X 0 ω k) μ)/
       ((l : ℝ)*(m : ℝ)^2) := by
  rw [((cluster_mean_properties μ hm X hiid h2).1 l hl).2.2]
  have hv : var μ (clusterAverage X 0)=
      (m : ℝ)⁻¹^2*(∑ j,∑ k,covariance (fun ω => X 0 ω j) (fun ω => X 0 ω k) μ) := by
    unfold var clusterAverage
    simp_rw [div_eq_mul_inv]
    rw [variance_mul_const, variance_fun_sum h2]
    ring
  rw [hv]
  ring

/-- The exact finite-mixture parameter box is compact and contains both true vectors; every sample likelihood is continuous on it and has a maximum.
Target P001-T11: Section 5.2.5, the sentence 'If any subset of the models ... jointly characterize the conditional distribution of $Y$, then this estimator is consistent and asymptotically efficient', as printed.
Location: p. 199 (PDF p. 217), second paragraph; the mixture and its parameter vector: pp. 198–199 (PDF pp. 216–217). -/
theorem finite_mixture_compact_attainment : IsCompact disjointMixtureParameterSet ∧
   (![1,1/3,1/4] : Fin 3 → ℝ)∈disjointMixtureParameterSet ∧
   (![1,1/3,3/4] : Fin 3 → ℝ)∈disjointMixtureParameterSet ∧
   ∀ n (y : Fin n → Fin 4),Continuous (disjointMixtureLikelihood y) ∧
     ∃ t∈disjointMixtureParameterSet,∀ u∈disjointMixtureParameterSet,
       disjointMixtureLikelihood y u ≤ disjointMixtureLikelihood y t := by
  have hc : IsCompact disjointMixtureParameterSet := isCompact_Icc
  have ha : (![1,1/3,1/4] : Fin 3 → ℝ)∈disjointMixtureParameterSet := by
    constructor <;> intro j <;> fin_cases j <;> norm_num
  have hb : (![1,1/3,3/4] : Fin 3 → ℝ)∈disjointMixtureParameterSet := by
    constructor <;> intro j <;> fin_cases j <;> norm_num
  refine ⟨hc,ha,hb,?_⟩
  intro n y
  have hcoord (j : Fin 4) : Continuous
      (fun t : Fin 3 → ℝ => disjointMixture (t 0) (t 1) (t 2) j) := by
    fin_cases j <;> dsimp [disjointMixture] <;> fun_prop
  have hL : Continuous (disjointMixtureLikelihood y) := by
    exact continuous_finset_prod Finset.univ (fun i hi => hcoord (y i))
  exact ⟨hL,hc.exists_isMaxOn ⟨_,ha⟩ hL.continuousOn⟩

/-- At both explicit true vectors, all finite iid sample masses are nonnegative, sum to one and are identical; the two separated b-estimation events have probabilities summing to at most one.
Target P001-T11: Section 5.2.5, the sentence 'If any subset of the models ... jointly characterize the conditional distribution of $Y$, then this estimator is consistent and asymptotically efficient', as printed.
Location: p. 199 (PDF p. 217), second paragraph; the mixture and its parameter vector: pp. 198–199 (PDF pp. 216–217). -/
theorem finite_mixture_iid_probabilities (n : ℕ) (T : (Fin n → Fin 4) → Fin 3 → ℝ) :
   (∑ y : Fin n → Fin 4,disjointMixtureLikelihood y ![1,1/3,1/4])=1 ∧
   (∀ y : Fin n → Fin 4,0 ≤ disjointMixtureLikelihood y ![1,1/3,1/4]) ∧
   (∀ y : Fin n → Fin 4,disjointMixtureLikelihood y ![1,1/3,1/4]=
     disjointMixtureLikelihood y ![1,1/3,3/4]) ∧
   finiteMixtureSampleProb (![1,1/3,1/4]) (fun y => |T y 2-1/4| < 1/8)+
     finiteMixtureSampleProb (![1,1/3,3/4]) (fun y => |T y 2-3/4| < 1/8) ≤ 1 := by
  
  rcases unused_component_nonidentification_supporting with ⟨he,hn,hp,hs,hdisjoint⟩
  have htotal : (∑ y : Fin n → Fin 4,disjointMixtureLikelihood y ![1,1/3,1/4])=1 := by
    unfold disjointMixtureLikelihood
    rw [← Fintype.prod_sum]
    change (∏ i : Fin n,(∑ j : Fin 4,disjointMixture 1 (1/3) (1/4) j))=1
    rw [hn]
    simp
  have hnonneg (y : Fin n → Fin 4) : 0 ≤ disjointMixtureLikelihood y ![1,1/3,1/4] := by
    exact Finset.prod_nonneg (fun i hi => hp (y i))
  have heq (y : Fin n → Fin 4) : disjointMixtureLikelihood y ![1,1/3,1/4]=
      disjointMixtureLikelihood y ![1,1/3,3/4] := hs n y
  refine ⟨htotal,hnonneg,heq,?_⟩
  unfold finiteMixtureSampleProb
  simp_rw [← heq]
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ y : Fin n → Fin 4,disjointMixtureLikelihood y ![1,1/3,1/4] := by
      apply Finset.sum_le_sum
      intro y hy
      have hd : ¬ (|T y 2-(4 : ℝ)⁻¹| < (8 : ℝ)⁻¹ ∧ |T y 2-3/4| < (8 : ℝ)⁻¹) := by
        simpa only [one_div] using hdisjoint (T y 2)
      simp only [one_div]
      by_cases ha : |T y 2-(4 : ℝ)⁻¹| < (8 : ℝ)⁻¹
      · have hb : ¬ |T y 2-3/4| < (8 : ℝ)⁻¹ := fun h => hd ⟨ha,h⟩
        simp only [if_pos ha,if_neg hb,add_zero,le_refl]
      · by_cases hb : |T y 2-3/4| < (8 : ℝ)⁻¹
        · simp only [if_neg ha,if_pos hb,zero_add,le_refl]
        · simp only [if_neg ha,if_neg hb,zero_add]
          simpa only [one_div] using hnonneg y
    _=1 := htotal

/-- The exact compact finite mixture has an attained sample likelihood maximum, but its two true full vectors give identical normalized laws and cannot both be consistency targets of any estimator.
Target P001-T11: Section 5.2.5, the sentence 'If any subset of the models ... jointly characterize the conditional distribution of $Y$, then this estimator is consistent and asymptotically efficient', as printed.
Location: p. 199 (PDF p. 217), second paragraph; the mixture and its parameter vector: pp. 198–199 (PDF pp. 216–217). -/
theorem finite_mixture_counterexample_with_attainment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (that : ℕ → Ω → Fin 3 → ℝ) (hm : ∀ n,Measurable (that n)) :
   IsCompact disjointMixtureParameterSet ∧
   (![1,1/3,1/4] : Fin 3 → ℝ)∈disjointMixtureParameterSet ∧
   (![1,1/3,3/4] : Fin 3 → ℝ)∈disjointMixtureParameterSet ∧
   (∀ n (y : Fin n → Fin 4),∃ t∈disjointMixtureParameterSet,
     ∀ u∈disjointMixtureParameterSet,disjointMixtureLikelihood y u ≤ disjointMixtureLikelihood y t) ∧
   disjointMixture 1 (1/3) (1/4)=disjointMixture 1 (1/3) (3/4) ∧
   (∑ i : Fin 4,disjointMixture 1 (1/3) (1/4) i)=1 ∧
   (∀ i : Fin 4,0 ≤ disjointMixture 1 (1/3) (1/4) i) ∧
   (∀ n (y : Fin n → Fin 4),disjointMixtureLikelihood y ![1,1/3,1/4]=
     disjointMixtureLikelihood y ![1,1/3,3/4]) ∧
   (∀ n (T : (Fin n → Fin 4) → Fin 3 → ℝ),
     (∑ y : Fin n → Fin 4,disjointMixtureLikelihood y ![1,1/3,1/4])=1 ∧
     (∀ y : Fin n → Fin 4,0 ≤ disjointMixtureLikelihood y ![1,1/3,1/4]) ∧
     (∀ y : Fin n → Fin 4,disjointMixtureLikelihood y ![1,1/3,1/4]=
       disjointMixtureLikelihood y ![1,1/3,3/4]) ∧
     finiteMixtureSampleProb (![1,1/3,1/4]) (fun y => |T y 2-1/4| < 1/8)+
       finiteMixtureSampleProb (![1,1/3,3/4]) (fun y => |T y 2-3/4| < 1/8) ≤ 1) ∧
   ¬ (CP μ that (![1,1/3,1/4] : Fin 3 → ℝ) ∧ CP μ that (![1,1/3,3/4] : Fin 3 → ℝ)) := by
  rcases finite_mixture_compact_attainment with ⟨hc,ha,hb,hmax⟩
  rcases unused_component_counterexample_full_supporting μ that hm with ⟨he,hn,hp,hs,hbad⟩
  exact ⟨hc,ha,hb,(fun n y => (hmax n y).2),he,hn,hp,hs,(fun n T => finite_mixture_iid_probabilities n T),hbad⟩

/-- For every positive fixed sample size, integrating the identity under the uniform empirical distribution equals the sample mean exactly.
Target P001-T2: Section 3.3.1, the example offered for the 'usual plug-in regularity conditions', corrected: asymptotic normality of the sample mean from the Central Limit Theorem, not from Hadamard differentiability of the mean.
Location: p. 120 (PDF p. 138), paragraph after Theorem 3.3.6. Theorem 3.2.24: p. 109 (PDF p. 127). Example 3.3.4: p. 119 (PDF p. 137). -/
theorem empirical_mean_fixed_sample {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 0 < n) (ω : Ω) :
   mean (empirical X n ω) id=sampleMean X n ω := by
  unfold mean empirical
  rw [integral_smul_measure]
  rw [integral_finsetSum_measure (fun i hi => integrable_dirac (by simp))]
  simp [sampleMean,ENNReal.toReal_inv,div_eq_mul_inv,mul_comm]

/-- For an infinite iid sequence with finite positive variance, the empirical mean functional is the sample mean and its centered root-n limit is the Gaussian law with that variance.
Target P001-T2: Section 3.3.1, the example offered for the 'usual plug-in regularity conditions', corrected: asymptotic normality of the sample mean from the Central Limit Theorem, not from Hadamard differentiability of the mean.
Location: p. 120 (PDF p. 138), paragraph after Theorem 3.3.6. Theorem 3.2.24: p. 109 (PDF p. 127). Example 3.3.4: p. 119 (PDF p. 137). -/
theorem sample_mean_clt_correction {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ)
   (hv : 0  <  var μ (X 0)) :
   (∀ n, 0  <  n → ∀ ω, mean (empirical X n ω) id = sampleMean X n ω) ∧
   CD μ (fun n ω => Real.sqrt n * (sampleMean X n ω - mean μ (X 0)))
     (gaussianReal 0 ⟨var μ (X 0), le_of_lt hv⟩) := by
  
  exact ⟨(fun n hn ω => empirical_mean_fixed_sample X n hn ω),
    central_limit_finite_variance μ X hiid h2 hv⟩

/-- For iid observations with a finite first moment, the expectation of every positive-size sample mean equals the population mean.
Target P001-T108: Theorem 3.2.3 (The Expected Value of the Sample Mean Is the Population Mean), Theorem 3.2.4 (Sampling Variance of the Sample Mean) and Theorem 3.2.5 (Chebyshev's Inequality for the Sample Mean).
Location: Theorem 3.2.3: p. 97 (PDF p. 115). Theorems 3.2.4 and 3.2.5: p. 98 (PDF p. 116), proof of 3.2.5 continuing on p. 99 (PDF p. 117). -/
theorem iid_sample_mean_expectation_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h1 : Integrable (X 0) μ)
   (n : ℕ) (hn : 0 < n) : mean μ (sampleMean X n)=mean μ (X 0) := by
  have hi : ∀ i,Integrable (X i) μ := fun i => (hiid.2.2 i).symm.integrable_snd h1
  have he : ∀ i,(∫ ω,X i ω ∂μ)=(∫ ω,X 0 ω ∂μ) := fun i => (hiid.2.2 i).integral_eq
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  have hs : sampleMean X n=(fun ω => (n : ℝ)⁻¹*(∑ i∈Finset.range n,X i ω)) := by
    funext ω
    simp [sampleMean,div_eq_mul_inv,mul_comm]
  rw [hs]
  unfold mean
  rw [integral_const_mul,integral_finsetSum (Finset.range n) (fun i hi' => hi i)]
  simp only [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  field_simp [hn0]

/-- The plug-in sample variance has expectation (n−1)/n times population variance and is consistent under finite second moments, without a fourth-moment assumption.
Target P001-T54: Theorem 3.2.19 (Properties of the Plug-In Sample Variance), with the consistency step of its proof corrected (WLLN for i.i.d. integrable variables).
Location: Theorem 3.2.19: p. 106 (PDF p. 124). Proof: pp. 106–107 (PDF pp. 124–125). Definition 3.2.18: p. 106. -/
theorem sample_variance_unbiased_factor_and_consistency_supporting {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ) :
   (∀ n, 0 < n → mean μ (sampleVariance X n)=((n : ℝ)-1)/n*var μ (X 0)) ∧
   CP μ (sampleVariance X) (var μ (X 0)) := by
  let XS : ℕ → Ω → ℝ := fun i ω => (X i ω)^2
  have hXS : IID μ XS := by
    refine ⟨?_,?_,?_⟩
    · intro i; exact (hiid.1 i).pow_const 2
    · exact hiid.2.1.comp (fun (_ : ℕ) (x : ℝ) => x^2) (fun _ => by fun_prop)
    · intro i; exact (hiid.2.2 i).comp (u := fun x : ℝ => x^2) (by fun_prop)
  have hXS1 : Integrable (XS 0) μ := h2.integrable_sq
  constructor
  · intro n hn
    have h2n := sample_mean_memLp μ X hiid h2 n
    have hSn : Integrable (sampleMean XS n) μ := by
      unfold sampleMean
      exact (integrable_finsetSum (Finset.range n)
        (fun i _ => (hXS.2.2 i).symm.integrable_snd hXS1)).div_const (n : ℝ)
    have heS := iid_sample_mean_expectation_integrable μ XS hXS hXS1 n hn
    rcases iid_sample_mean_finite_moments μ X hiid h2 n hn with ⟨he,hv⟩
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    change mean μ (fun ω => sampleMean XS n ω-(sampleMean X n ω)^2)=_
    unfold mean
    rw [integral_sub hSn h2n.integrable_sq]
    change mean μ (sampleMean XS n)-mean μ (fun ω => (sampleMean X n ω)^2)=_
    have hsecond : mean μ (fun ω => (sampleMean X n ω)^2)=
        var μ (sampleMean X n)+(mean μ (sampleMean X n))^2 := by
      have h := variance_eq_sub h2n
      change var μ (sampleMean X n)=
        mean μ (fun ω => (sampleMean X n ω)^2)-(mean μ (sampleMean X n))^2 at h
      linarith
    rw [heS,hsecond,hv,he]
    have hp := variance_eq_sub h2
    change var μ (X 0)=mean μ (XS 0)-(mean μ (X 0))^2 at hp
    rw [hp]
    field_simp [hn0]
    ring
  · have hAS := strong_law_ae_real X (h2.integrable one_le_two)
      (fun i j hij => hiid.2.1.indepFun hij) hiid.2.2
    have hSS := strong_law_ae_real XS hXS1
      (fun i j hij => hXS.2.1.indepFun hij) hXS.2.2
    have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => sampleVariance X n ω)
        atTop (nhds (var μ (X 0))) := by
      filter_upwards [hAS,hSS] with ω hω hωS
      have h := hωS.sub (hω.pow 2)
      simpa only [sampleVariance,sampleMean,XS,var,variance_eq_sub h2,mean,Pi.pow_apply] using h
    have hXi : ∀ i, Measurable (X i) := hiid.1
    have hm (n : ℕ) : Measurable (sampleVariance X n) := by
      unfold sampleVariance sampleMean
      fun_prop
    have hmeasure := tendstoInMeasure_of_tendsto_ae
      (fun n => (hm n).aestronglyMeasurable) hlim
    intro ε hε
    simpa only [prob,Measure.real] using
      (tendstoInMeasure_iff_measureReal_dist.mp hmeasure) ε hε


/-- The occupancy constants A and B are below three and three halves, and the bootstrap variance limit is below the true limit.
Target P001-T13: Footnote 15 (hot deck imputation: 'the bootstrap standard errors are likely to adequately characterize sampling variability', with the bootstrap's failure attributed to slowly converging bias), as printed.
Location: p. 233 (PDF p. 251), footnote 15, attached to the hot deck estimate; Table 6.3.1, row 'Hot Deck Imputation'. Hot deck imputation: Section 6.2.3, pp. 224–225 (PDF pp. 242–243). The bootstrap: Section 3.4.3, p. 131 (PDF p. 149). -/
theorem hot_deck_bootstrap_constant_inequalities : 0 < matchS ∧ matchS < 1 ∧ matchA < 3 ∧ matchB < 3/2 ∧ matchVB < matchV := by
  have hexp : (5/2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hexp0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hexp1 : Real.exp (-1) < 2/5 := by
    rw [Real.exp_neg, inv_lt_iff_one_lt_mul₀ (Real.exp_pos 1)]
    linarith
  have hslo : (3/5 : ℝ) < matchS := by unfold matchS; linarith
  have hshi : matchS < 1 := by unfold matchS; linarith
  have hs0 : 0 < matchS := by linarith
  have hd : 0 < 2-matchS := by linarith
  have ha : matchA < 3 := by
    unfold matchA
    apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ hs0).mpr
    have hm := (div_mul_cancel₀ matchS (ne_of_gt hd))
    have hb : matchS^2 < 1 := by nlinarith
    field_simp
    nlinarith
  have hb : matchB < 3/2 := by
    unfold matchB
    field_simp
    nlinarith
  have hlog : 1 < Real.log 3 := by
    exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  refine ⟨hs0,hshi,ha,hb,?_⟩
  unfold matchVB matchV
  have hm : 0 < 2*Real.log 3-3/2 := by linarith
  nlinarith [(mul_lt_mul_of_pos_right hb hm)]

/-- A finite distribution with increasing indexed values has CDF zero before the first value, its partial mass sum between consecutive values, and one from the final value onward.
Target P001-T28: Example 1.2.13, first sentence, corrected: the CDF of a discrete random variable as a sum of jumps, and its step shape when the range is finite.
Location: p. 23 (PDF p. 41), Example 1.2.13, first sentence; the analogy on p. 116 (PDF p. 134). -/
theorem ordered_finite_cdf_formula {m : ℕ} (P : FiniteLaw (m+1)) (X : Fin (m+1) → ℝ) (hX : StrictMono X) :
   ∀ x : ℝ,(x < X 0 → fprob P (fun i => X i ≤ x)=0) ∧
   (∀ l : Fin m,X l.castSucc ≤ x → x < X l.succ →
     fprob P (fun i => X i ≤ x)=∑ i : Fin (m+1),if i ≤ l.castSucc then P.weight i else 0) ∧
   (X (Fin.last m) ≤ x → fprob P (fun i => X i ≤ x)=1) := by
  intro x
  refine ⟨?_,?_,?_⟩
  · intro hx
    unfold fprob
    apply Finset.sum_eq_zero
    intro i hi
    have hlow : X 0 ≤ X i := hX.monotone (Fin.zero_le i)
    have hn : ¬ X i ≤ x := by linarith
    simp only [if_neg hn]
  · intro l hl hu
    have he (i : Fin (m+1)) : X i ≤ x ↔ i ≤ l.castSucc := by
      constructor
      · intro hix
        by_contra hn
        have hli : l.succ ≤ i := by
          change l.val+1 ≤ i.val
          have hn' : ¬ i.val ≤ l.val := hn
          omega
        have hXi := hX.monotone hli
        linarith
      · intro hi
        exact (hX.monotone hi).trans hl
    unfold fprob
    apply Finset.sum_congr rfl
    intro i hi
    change (if X i ≤ x then P.weight i else 0)=_
    simp only [he i]
  · intro hx
    have hall (i : Fin (m+1)) : X i ≤ x :=
      (hX.monotone (Fin.le_last i)).trans hx
    unfold fprob
    simp only [hall,if_true]
    exact P.total


/-- The conditional-variance version of Y is also that of its CEF deviation, and the deviation variance equals the mean conditional variance.
Target P001-T74: Section 5.1.1, the comparison of the classical linear model's errors with deviations from the CEF, corrected ('uncorrelated with' for 'independent of'); with Theorem 2.2.19 (Properties of Deviations from the CEF).
Location: p. 181 (PDF p. 199), paragraph after the display $Y = \mathbf{X}\boldsymbol\beta + \varepsilon$. Theorem 2.2.19: p. 74 (PDF p. 92), proof on pp. 74–75. -/
theorem cef_residual_conditional_variance {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y : Ω → ℝ) (hY : MemLp Y 2 μ) (m v : E → ℝ)
   (hm : IsCEF μ X Y m) (hm2 : MemLp (m ∘ X) 2 μ)
   (hv : IsCEF μ X (fun ω => (Y ω-m (X ω))^2) v) :
   IsCEF μ X (fun ω => ((Y ω-m (X ω))-0)^2) v ∧
   var μ (fun ω => Y ω-m (X ω))=mean μ (v ∘ X) := by
  refine ⟨by simpa using hv, ?_⟩
  have he := iterated_expectation μ X Y hm.2.1 m hm
  have hmi : Integrable (fun ω => m (X ω)) μ := hm.2.2.1
  have hr2 : MemLp (fun ω => Y ω-m (X ω)) 2 μ := hY.sub hm2
  have hr : (∫ ω, Y ω-m (X ω) ∂μ)=0 := by
    rw [integral_sub hm.2.1 hmi]
    exact sub_eq_zero.mpr he
  have hv' := iterated_expectation μ X (fun ω => (Y ω-m (X ω))^2) hv.2.1 v hv
  rw [var, variance_eq_integral hr2.aemeasurable, hr]
  simpa [mean] using hv'


/- The two square-integral norm/Minkowski lemmas adapt the StatLean modules
`QMDAnalytic` and `ZEstimatorModelShift` (Apache-2.0;
see NOTICE at the repository root). -/
theorem sqrt_integral_sq_eq_lpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Real.sqrt (∫ ω, f ω^2 ∂μ) = (eLpNorm f 2 μ).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hi : (fun ω => ‖f ω‖ ^ (2 : ℝ≥0∞).toReal) = fun ω => f ω^2 := by
    funext ω
    rw [h2,Real.rpow_two,Real.norm_eq_abs,sq_abs]
  rw [hi]
  have hnn : 0 ≤ ∫ ω,f ω^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _),h2,Real.sqrt_eq_rpow]
  norm_num

theorem sqrt_integral_sq_add_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Real.sqrt (∫ ω,(f ω+g ω)^2 ∂μ) ≤
      Real.sqrt (∫ ω,f ω^2 ∂μ)+Real.sqrt (∫ ω,g ω^2 ∂μ) := by
  change Real.sqrt (∫ ω,(f+g) ω^2 ∂μ) ≤ _
  rw [sqrt_integral_sq_eq_lpNorm (hf.add hg),sqrt_integral_sq_eq_lpNorm hf,
    sqrt_integral_sq_eq_lpNorm hg]
  have hle := eLpNorm_add_le (f := f) (g := g) (μ := μ) (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have htop : eLpNorm f 2 μ+eLpNorm g 2 μ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hf.ne,hg.ne⟩
  have hreal := ENNReal.toReal_mono htop hle
  rw [ENNReal.toReal_add hf.ne hg.ne] at hreal
  exact hreal

theorem gram_quadratic_form {n K : ℕ} (P : Matrix (Fin n) (Fin K) ℝ) (v : Fin K → ℝ) :
    dotProduct v ((P.transpose*P).mulVec v) = ∑ i,(P.mulVec v i)^2 := by
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,
    Matrix.transpose_transpose]
  simp only [dotProduct,pow_two]

theorem gram_unit_of_lower_bound {n K : ℕ} (hn : 0 < n)
    (P : Matrix (Fin n) (Fin K) ℝ) (c : ℝ) (hc : 0 < c)
    (hgram : ∀ v : Fin K → ℝ,c*(∑ k,(v k)^2) ≤ (∑ i,(P.mulVec v i)^2)/(n:ℝ)) :
    IsUnit (P.transpose*P).det := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hH : (P.transpose*P).PosDef := by
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    refine ⟨?_,?_⟩
    · have he : P.conjTranspose=P.transpose := by ext i j; simp
      simpa only [he] using (Matrix.posSemidef_conjTranspose_mul_self P).isHermitian
    · intro v hv
      have hex : ∃ k,v k≠0 := by
        by_contra h
        push_neg at h
        exact hv (funext h)
      obtain ⟨k,hk⟩ := hex
      have hsum : 0 < ∑ j,(v j)^2 := lt_of_lt_of_le (sq_pos_of_ne_zero hk)
        (Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ k))
      have hp : 0 < (∑ i,(P.mulVec v i)^2)/(n:ℝ) := (mul_pos hc hsum).trans_le (hgram v)
      have hnum : 0 < ∑ i,(P.mulVec v i)^2 := (div_pos_iff_of_pos_right hnR).mp hp
      simpa only [star_trivial,gram_quadratic_form] using hnum
  exact (Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit

theorem orthonormal_polynomial_lp {K : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (p : Fin K → Polynomial ℝ)
    (horth : ∀ j k,mean ν (fun x => (p j).eval x*(p k).eval x)=if j=k then 1 else 0) :
    ∀ j, MemLp (fun x => (p j).eval x) 2 ν := by
  intro j
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  by_contra h
  have hj : (∫ x,(p j).eval x*(p j).eval x ∂ν)=1 := by
    simpa only [mean,ite_true] using horth j j
  have he : (fun x => (p j).eval x*(p j).eval x) = fun x => ((p j).eval x)^2 := by
    funext x
    ring
  rw [he,integral_undef h] at hj
  norm_num at hj

theorem orthonormal_polynomial_integral_sq {K : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (p : Fin K → Polynomial ℝ)
    (horth : ∀ j k,mean ν (fun x => (p j).eval x*(p k).eval x)=if j=k then 1 else 0)
    (b : Fin K → ℝ) :
    (∫ x,(∑ k,b k*(p k).eval x)^2 ∂ν) = ∑ k,(b k)^2 := by
  have hp := orthonormal_polynomial_lp ν p horth
  have hi (j k : Fin K) : Integrable (fun x => b j*b k*((p j).eval x*(p k).eval x)) ν :=
    ((hp j).integrable_mul (hp k)).const_mul _
  have he : (fun x => (∑ k,b k*(p k).eval x)^2) =
      fun x => ∑ j,∑ k,b j*b k*((p j).eval x*(p k).eval x) := by
    funext x
    rw [pow_two,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he,integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi j k))]
  have hinner (j k : Fin K) : (∫ x,(p j).eval x*(p k).eval x ∂ν)=if j=k then 1 else 0 := horth j k
  calc
    (∑ j,∫ x,∑ k,b j*b k*((p j).eval x*(p k).eval x) ∂ν) =
        ∑ j,∑ k,b j*b k*(∫ x,(p j).eval x*(p k).eval x ∂ν) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum _ (fun k _ => hi j k)]
      simp_rw [integral_const_mul]
    _ = _ := by simp [hinner,pow_two]

/-- The six-point latent vector is independent of treatment, the true effect is zero, and conditioning on the observed post-treatment covariate destroys potential-outcome ignorability.
Target P001-T89: Example 7.1.17 (Conditioning on Post-Treatment Variables), the distribution of observables, corrected (the cell $(Y_i, X_i, D_i) = (1, 1, 1)$ once, with probability $\frac{1}{3}$); the adjusted contrast $-\frac{1}{4}$.
Location: pp. 253–254 (PDF pp. 271–272). -/
theorem post_treatment_latent_random_assignment : FCondIndep postTreatmentLaw
     (fun i => (postY i,postY i,postPotentialX1 i,postPotentialX0 i)) postD (fun _ => ()) ∧
   fprob postTreatmentLaw (fun i => postD i=1)=1/2 ∧
   (∀ i,observedOutcome (postPotentialX0 i) (postPotentialX1 i) (postD i)=postX i) ∧
   fmean postTreatmentLaw (fun i => postY i-postY i)=0 ∧
   ¬ FCondIndep postTreatmentLaw (fun i => (postY i,postY i)) postD postX := by
  classical
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x y z hx
    cases x
    norm_num [fprob,postTreatmentLaw,postY,postPotentialX0,postPotentialX1,postD,Fin.sum_univ_succ]
    by_cases hy0 : y=((0:ℝ),0,0,0) <;> by_cases hy1 : y=((1:ℝ),1,1,0) <;>
      by_cases hy2 : y=((1:ℝ),1,1,1) <;> by_cases hz0 : z=(0:ℝ) <;> by_cases hz1 : z=(1:ℝ) <;>
      norm_num [hy0,hy1,hy2,hz0,hz1,eq_comm]
  · norm_num [fprob,postTreatmentLaw,postD,Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> norm_num [observedOutcome,postPotentialX0,postPotentialX1,postX,postD]
  · simp [fmean]
  · intro hind
    have hh := hind 0 ((1:ℝ),1) 0 (by
      norm_num [fprob,postTreatmentLaw,postX,Fin.sum_univ_succ])
    norm_num [fprob,postTreatmentLaw,postY,postD,postX,Fin.sum_univ_succ] at hh


/-- The printed plug-in formula takes the coordinate derivative of the chosen estimated CEF at the componentwise sample covariate mean.
Target P001-T102: Definition 4.3.7 (Partial Derivative at the Average) and the plug-in estimate that follows it, as printed.
Location: p. 167 (PDF p. 185); footnote 13, p. 166 (PDF p. 184); the remark on p. 168 (PDF p. 186). -/
theorem printed_pda_plugin_formula {Ω : Type*} {K : ℕ} (X : ℕ → Ω → Fin K → ℝ)
   (mhat : ℕ → Ω → (Fin K → ℝ) → ℝ) (n : ℕ) (ω : Ω) (k : Fin K) :
   pluginPDA X mhat n ω k=partialAt (mhat n ω)
     (fun j => sampleMean (fun i z => X i z j) n ω) k := by
  rfl

/-- For positive n, the sample-mean standard deviation is sigma over square-root n, the two standardizations agree, and the standardized mean has mean zero, variance one and standard deviation one.
Target P001-T126: Theorem 3.2.24 (Central Limit Theorem).
Location: p. 109 (PDF p. 127). Definition 3.2.23: p. 109. Definition 3.2.22: p. 108 (PDF p. 126). -/
theorem standardized_mean_fixed_sample_moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ)
   (hv : 0 < var μ (X 0)) (n : ℕ) (hn : 0 < n) :
   Real.sqrt (var μ (sampleMean X n))=Real.sqrt (var μ (X 0))/Real.sqrt n ∧
   (∀ ω,standardizedMean μ X n ω=
     Real.sqrt n*(sampleMean X n ω-mean μ (X 0))/Real.sqrt (var μ (X 0))) ∧
   mean μ (standardizedMean μ X n)=0 ∧ var μ (standardizedMean μ X n)=1 ∧
   Real.sqrt (var μ (standardizedMean μ X n))=1 := by
  rcases iid_sample_mean_finite_moments μ X hiid h2 n hn with ⟨hm,hvar⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsV : Real.sqrt (var μ (X 0)) ≠ 0 := (Real.sqrt_pos.2 hv).ne'
  have hsN : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
  have hroot : Real.sqrt (var μ (sampleMean X n))=
      Real.sqrt (var μ (X 0))/Real.sqrt n := by rw [hvar,Real.sqrt_div (le_of_lt hv)]
  have h2n := sample_mean_memLp μ X hiid h2 n
  have hz : standardizedMean μ X n=(fun ω =>
      (Real.sqrt (var μ (sampleMean X n)))⁻¹*(sampleMean X n ω-mean μ (sampleMean X n))) := by
    funext ω
    simp [standardizedMean,div_eq_mul_inv,mul_comm]
  have hmean : mean μ (standardizedMean μ X n)=0 := by
    rw [hz]
    unfold mean
    rw [integral_const_mul,integral_sub (h2n.integrable one_le_two) (integrable_const _)]
    simp
  have hnorm : var μ (standardizedMean μ X n)=1 := by
    rw [hz]
    unfold var
    rw [variance_const_mul,variance_sub_const h2n.aestronglyMeasurable,
      inv_pow,Real.sq_sqrt (variance_nonneg _ _)]
    have hnvar : variance (sampleMean X n) μ ≠ 0 := by
      change var μ (sampleMean X n) ≠ 0
      rw [hvar]
      exact (div_pos hv hnR).ne'
    exact inv_mul_cancel₀ hnvar
  refine ⟨hroot,?_,hmean,hnorm,?_⟩
  · intro ω
    unfold standardizedMean
    rw [hm,hroot]
    field_simp [hsV,hsN]
  · rw [hnorm]; norm_num

/-- The printed standardized iid sample mean converges in the CDF sense to N(0,1).
Target P001-T126: Theorem 3.2.24 (Central Limit Theorem).
Location: p. 109 (PDF p. 127). Definition 3.2.23: p. 109. Definition 3.2.22: p. 108 (PDF p. 126). -/
theorem central_limit_standardized_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ)
   (hv : 0 < var μ (X 0)) : CD μ (standardizedMean μ X) (gaussianReal 0 1) := by
  let s := Real.sqrt (var μ (X 0))
  have hs : s ≠ 0 := (Real.sqrt_pos.2 hv).ne'
  let W : ℕ → Ω → ℝ := fun i ω => (X i ω-mean μ (X 0))/s
  have hW : IID μ W := by
    refine ⟨?_,?_,?_⟩
    · intro i
      exact ((hiid.1 i).sub measurable_const).div_const s
    · exact hiid.2.1.comp (fun _ x => (x-mean μ (X 0))/s) (fun _ => by fun_prop)
    · intro i
      exact (hiid.2.2 i).comp (u := fun x => (x-mean μ (X 0))/s) (by fun_prop)
  have hW2 : MemLp (W 0) 2 μ := by
    have h := (h2.sub (memLp_const (mean μ (X 0)))).const_mul s⁻¹
    simpa [W,div_eq_mul_inv,mul_comm] using h
  have hW0 : mean μ (W 0)=0 := by
    unfold mean
    dsimp [W]
    rw [integral_div,integral_sub (h2.integrable one_le_two) (integrable_const _)]
    simp [mean]
  have hWv : var μ (W 0)=1 := by
    have he : W 0=(fun ω => s⁻¹*(X 0 ω-mean μ (X 0))) := by
      funext ω; simp [W,div_eq_mul_inv,mul_comm]
    rw [he]
    unfold var
    rw [variance_const_mul,variance_sub_const h2.aestronglyMeasurable,inv_pow]
    change (s^2)⁻¹*var μ (X 0)=1
    rw [show s^2=var μ (X 0) from Real.sq_sqrt (le_of_lt hv)]
    exact inv_mul_cancel₀ hv.ne'
  have hclt := central_limit_finite_variance μ W hW hW2 (by rw [hWv]; norm_num)
  have hvsub : (⟨var μ (W 0),by rw [hWv]; norm_num⟩ : ℝ≥0)=1 := by
    apply Subtype.ext; exact hWv
  rw [hvsub] at hclt
  have hstat (n : ℕ) (hn : 0 < n) (ω : Ω) :
      Real.sqrt n*(sampleMean W n ω-mean μ (W 0))=standardizedMean μ X n ω := by
    have hsm : sampleMean W n ω=(sampleMean X n ω-mean μ (X 0))/s := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      unfold sampleMean
      simp only [W,← Finset.sum_div,Finset.sum_sub_distrib,
        Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      field_simp [hn0,hs]
    rw [hW0,hsm,(standardized_mean_fixed_sample_moments μ X hiid h2 hv n hn).2.1 ω]
    dsimp [s]
    ring
  intro x hx
  apply (hclt x hx).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  unfold cdf prob
  congr 2
  ext ω
  simp only [Set.mem_setOf_eq,hstat n hn ω]

/-- For each fixed full-rank polynomial design, fitting its approximation plus remainder plus noise gives the sum of the approximation coefficients and the two OLS remainder/noise coefficient vectors.
Target P001-T6: Definition 4.3.9 (Polynomial Least Squares Sieve Estimator) and the consistency claim after it, corrected with a sufficient degree-growth condition.
Location: pp. 168–169 (PDF pp. 186–187). -/
theorem sieve_finite_coefficient_decomposition {n K : ℕ} (P : Matrix (Fin n) (Fin K) ℝ)
   (hP : IsUnit (P.transpose*P).det) (b : Fin K → ℝ) (r u : Fin n → ℝ) :
   olsCoef P (P.mulVec b+r+u)=b+olsCoef P r+olsCoef P u := by
  have hb : (P.transpose*P)⁻¹.mulVec (P.transpose.mulVec (P.mulVec b))=b := by
    rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hP,Matrix.one_mulVec]
  simp only [olsCoef,Matrix.mulVec_add]
  rw [hb]

/-- On a Gram lower-bound event, the approximation-remainder coefficient vector has squared norm at most the empirical remainder squared norm divided by c.
Target P001-T6: Definition 4.3.9 (Polynomial Least Squares Sieve Estimator) and the consistency claim after it, corrected with a sufficient degree-growth condition.
Location: pp. 168–169 (PDF pp. 186–187). -/
theorem sieve_finite_approximation_coefficient_bound {n K : ℕ} (hn : 0 < n) (P : Matrix (Fin n) (Fin K) ℝ) (r : Fin n → ℝ)
   (c : ℝ) (hc : 0 < c)
   (hgram : ∀ v : Fin K → ℝ,c*(∑ k,(v k)^2) ≤ (∑ i,(P.mulVec v i)^2)/(n : ℝ)) :
   c*(∑ k,(olsCoef P r k)^2) ≤ (∑ i,(P.mulVec (olsCoef P r) i)^2)/(n : ℝ) ∧
   (∑ i,(P.mulVec (olsCoef P r) i)^2)/(n : ℝ) ≤ (∑ i,(r i)^2)/(n : ℝ) := by
  exact ⟨hgram _,div_le_div_of_nonneg_right (ols_fitted_sum_squares_le P r) (Nat.cast_nonneg n)⟩


/-- The exact twelve-point placebo null has positivity and potential-outcome ignorability, yet the unique population augmented BLP has W slope 4/17 and strictly smaller risk than the restricted BLP.
Target P001-T17: Section 7.2.8 (Placebo Testing): the $F$-test comparing a regression of $D_i$ on $\mathbf{W}_i$ and $\mathbf{X}_i$ with a regression of $D_i$ on $\mathbf{X}_i$ alone, as a test of $\mathbf{W}_i \perp\!\!\!\perp D_i|\mathbf{X}_i$, as printed.
Location: p. 270 (PDF p. 288), Section 7.2.8. -/
theorem placebo_full_finite_counterexample : FCondIndep placeboLaw placeboW placeboD placeboX ∧
   FCondIndep placeboLaw (fun i => (2+placeboZ i,3+placeboZ i)) placeboD placeboX ∧
   (∀ i : Fin 12,(1/8 : ℝ) < fcond placeboLaw placeboD placeboX (placeboX i) ∧
     fcond placeboLaw placeboD placeboX (placeboX i) < 1-1/8) ∧
   (∀ i : Fin 12,fcond placeboLaw
     (fun j => (placeboW j-fcond placeboLaw placeboW placeboX (placeboX i))^2)
     placeboX (placeboX i)=1/4) ∧
   placeboMoment.det=17/54 ∧
   (∀ a b c : ℝ,placeboRisk (29/68) 0 (4/17) ≤ placeboRisk a b c ∧
     (placeboRisk a b c=placeboRisk (29/68) 0 (4/17) ↔ a=29/68 ∧ b=0 ∧ c=4/17)) ∧
   (∀ a b : ℝ,placeboRisk (7/12) 0 0 ≤ placeboRisk a b 0 ∧
     (placeboRisk a b 0=placeboRisk (7/12) 0 0 ↔ a=7/12 ∧ b=0)) ∧
   placeboRisk (7/12) 0 0=35/144 ∧ placeboRisk (29/68) 0 (4/17)=59/272 ∧
   placeboRisk (29/68) 0 (4/17) < placeboRisk (7/12) 0 0 ∧ (4/17 : ℝ)≠0 := by
  classical
  have hpotential : FCondIndep placeboLaw (fun i => (2+placeboZ i,3+placeboZ i)) placeboD placeboX := by
    intro x y z hx
    have hxs : x=(-1:ℝ) ∨ x=0 ∨ x=1 := by
      by_contra h
      push_neg at h
      norm_num [fprob,placeboLaw,placeboX,Fin.sum_univ_succ,h.1,h.2.1,h.2.2,eq_comm] at hx
    rcases hxs with rfl | rfl | rfl <;>
      norm_num [fprob,placeboLaw,placeboX,placeboZ,placeboD,Fin.sum_univ_succ] <;>
      by_cases hy1 : y=((1:ℝ),2) <;> by_cases hy2 : y=((3:ℝ),4) <;>
      by_cases hz1 : z=(0:ℝ) <;> by_cases hz2 : z=(1:ℝ) <;>
      norm_num at hy1 hy2 hz1 hz2 <;>
      norm_num [hy1,hy2,hz1,hz2,eq_comm]
  have hfull (a b c : ℝ) : placeboRisk a b c =
      59/272+(a-29/68+(2/3)*(c-4/17))^2+(2/3)*b^2+(17/36)*(c-4/17)^2 := by
    norm_num [placeboRisk,fmean,placeboLaw,placeboD,placeboX,placeboW,placeboZ,Fin.sum_univ_succ]
    ring
  have hrestricted (a b : ℝ) : placeboRisk a b 0=35/144+(a-7/12)^2+(2/3)*b^2 := by
    rw [hfull]
    ring
  refine ⟨placebo_linear_test_counterexample_supporting.1,hpotential,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    fin_cases i <;>
      norm_num [fcond,fprob,placeboLaw,placeboD,placeboX,Fin.sum_univ_succ]
  · intro i
    fin_cases i <;>
      norm_num [fcond,fprob,placeboLaw,placeboD,placeboX,placeboW,placeboZ,Fin.sum_univ_succ]
  · norm_num [placeboMoment,Matrix.det_fin_three,fmean,placeboRegressor,placeboLaw,placeboX,placeboW,placeboZ,Fin.sum_univ_succ]
  · intro a b c
    rw [hfull,hfull]
    constructor
    · nlinarith [sq_nonneg (a-29/68+(2/3)*(c-4/17)),sq_nonneg b,sq_nonneg (c-4/17)]
    · constructor
      · intro he
        have hc : (c-4/17)^2=0 := by
          nlinarith [sq_nonneg (a-29/68+(2/3)*(c-4/17)),sq_nonneg b,sq_nonneg (c-4/17)]
        have hb : b^2=0 := by
          nlinarith [sq_nonneg (a-29/68+(2/3)*(c-4/17)),sq_nonneg b,sq_nonneg (c-4/17)]
        have hc' : c=4/17 := sub_eq_zero.mp (sq_eq_zero_iff.mp hc)
        have hb' : b=0 := sq_eq_zero_iff.mp hb
        subst c
        subst b
        norm_num at he
        exact ⟨by nlinarith [sq_nonneg (a-29/68)],rfl,rfl⟩
      · rintro ⟨rfl,rfl,rfl⟩
        rfl
  · intro a b
    rw [hrestricted,hrestricted]
    constructor
    · nlinarith [sq_nonneg (a-7/12),sq_nonneg b]
    · constructor
      · intro he
        have hb2 : b^2=0 := by nlinarith [sq_nonneg (a-7/12),sq_nonneg b]
        have hb : b=0 := sq_eq_zero_iff.mp hb2
        subst b
        exact ⟨by nlinarith [sq_nonneg (a-7/12)],rfl⟩
      · rintro ⟨rfl,rfl⟩
        rfl
  · rw [hrestricted]
    norm_num
  · rw [hfull]
    norm_num
  · rw [hfull,hrestricted]
    norm_num
  · norm_num


theorem iid_positive_at_parameter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (θ : Fin τ → ℝ)
    (hg : Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 θ))
    (hp : ∀ᵐ ω ∂μ, 0 < g (Y 0 ω) (X 0 ω) θ) :
    ∀ᵐ ω ∂μ, ∀ i, 0 < g (Y i ω) (X i ω) θ := by
  apply ae_all_iff.mpr
  intro i
  have hset : MeasurableSet {xy : (Fin K → ℝ) × ℝ | 0 < g xy.2 xy.1 θ} :=
    measurableSet_lt measurable_const hg
  have hbase : ∀ᵐ xy ∂μ.map (fun ω => (X 0 ω,Y 0 ω)),0 < g xy.2 xy.1 θ :=
    (ae_map_iff (hiid.1 0).aemeasurable hset).mpr hp
  rw [← (hiid.2.2 i).map_eq] at hbase
  exact (ae_map_iff (hiid.1 i).aemeasurable hset).mp hbase

theorem product_mle_consistency_core {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (Θ : Set (Fin τ → ℝ)) (hc : IsCompact Θ) (θ : Fin τ → ℝ) (hθ : θ ∈ Θ)
    (hM : ContinuousOn (expectedLogLikelihood μ (X 0) (Y 0) g) Θ)
    (hu : ∀ t ∈ Θ, expectedLogLikelihood μ (X 0) (Y 0) g t ≤
        expectedLogLikelihood μ (X 0) (Y 0) g θ ∧
      (expectedLogLikelihood μ (X 0) (Y 0) g t =
        expectedLogLikelihood μ (X 0) (Y 0) g θ → t=θ))
    (that : ℕ → Ω → Fin τ → ℝ) (hthat : ∀ n ω,that n ω ∈ Θ)
    (hp : ∀ᵐ ω ∂μ,∀ i,0 < g (Y i ω) (X i ω) θ)
    (hmax : ∀ n ω, sampleLikelihood X Y g n ω θ ≤ sampleLikelihood X Y g n ω (that n ω))
    (Δ : ℕ → Ω → ℝ) (hΔ : ∀ n ω t,t ∈ Θ →
      |sampleLogLikelihood X Y g n ω t-expectedLogLikelihood μ (X 0) (Y 0) g t| ≤ Δ n ω)
    (hlim : CP μ Δ 0) : CP μ that θ := by
  let M := expectedLogLikelihood μ (X 0) (Y 0) g
  have hopt (n : ℕ) : ∀ᵐ ω ∂μ,
      sampleLogLikelihood X Y g n ω θ ≤ sampleLogLikelihood X Y g n ω (that n ω) := by
    filter_upwards [hp] with ω hω
    have htruth : 0 < sampleLikelihood X Y g n ω θ :=
      Finset.prod_pos (fun i _ => hω i)
    have hfit : 0 < sampleLikelihood X Y g n ω (that n ω) := lt_of_lt_of_le htruth (hmax n ω)
    have hfitFactors : ∀ i ∈ Finset.range n,g (Y i ω) (X i ω) (that n ω) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hfit.ne'
    have hl := Real.log_le_log htruth (hmax n ω)
    unfold sampleLikelihood at hl
    rw [Real.log_prod (fun i _ => (hω i).ne'),Real.log_prod hfitFactors] at hl
    exact div_le_div_of_nonneg_right hl (Nat.cast_nonneg n)
  intro ε hε
  obtain ⟨δ,hδ,hsep⟩ := compact_unique_maximum_separated Θ hc θ hθ M hM hu ε hε
  have hbound (n : ℕ) : prob μ {ω | ε ≤ dist (that n ω) θ} ≤
      prob μ {ω | δ/2 ≤ dist (Δ n ω) 0} := by
    apply ENNReal.toReal_mono (measure_ne_top μ _)
    apply measure_mono_ae
    filter_upwards [hopt n] with ω hop
    intro hω
    have hgap := hsep (that n ω) (hthat n ω) hω
    have hnear := argmax_finite_gap M (sampleLogLikelihood X Y g n ω)
      (that n ω) θ (Δ n ω) 0 (hΔ n ω _ (hthat n ω)) (hΔ n ω θ hθ)
      (by simpa using hop)
    change δ/2 ≤ dist (Δ n ω) 0
    rw [Real.dist_eq,sub_zero]
    have ha := le_abs_self (Δ n ω)
    linarith
  exact squeeze_zero' (Eventually.of_forall (fun n => ENNReal.toReal_nonneg))
    (Eventually.of_forall hbound) (hlim (δ/2) (by linarith))

/-- For iid correctly specified conditional models, actual product-likelihood maximizers are consistent under the compactness, unique population expected-log maximum and uniform-log regularity conditions.
Target P001-T129: Theorem 5.2.6 (Consistency of the Maximum Likelihood Estimator) and the lemma in its proof sketch.
Location: Theorem 5.2.6: p. 193 (PDF p. 211). Proof sketch: pp. 193–194 (PDF pp. 211–212). -/
theorem product_maximum_likelihood_consistency {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (Θ : Set (Fin τ → ℝ))
   (hc : IsCompact Θ) (θ : Fin τ → ℝ) (hθ : θ∈Θ)
   (hg : ∀ t∈Θ,Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
   (hnonneg : ∀ t∈Θ,∀ y x,0 ≤ g y x t)
   (hnorm : ∀ t∈Θ,∀ x,(∫⁻ y,ENNReal.ofReal (g y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=conditionalModelLaw νX κ g θ)
   (hlog : ∀ t∈Θ,Integrable (fun ω => Real.log (g (Y 0 ω) (X 0 ω) t)) μ)
   (hpos : ∀ t∈Θ,∀ᵐ ω ∂μ,0 < g (Y 0 ω) (X 0 ω) t)
   (hM : ContinuousOn (expectedLogLikelihood μ (X 0) (Y 0) g) Θ)
   (hunique : ∀ t∈Θ,expectedLogLikelihood μ (X 0) (Y 0) g t ≤ expectedLogLikelihood μ (X 0) (Y 0) g θ ∧
     (expectedLogLikelihood μ (X 0) (Y 0) g t=expectedLogLikelihood μ (X 0) (Y 0) g θ → t=θ))
   (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n,Measurable (that n))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → sampleLikelihood X Y g n ω t ≤ sampleLikelihood X Y g n ω (that n ω))
   (Δ : ℕ → Ω → ℝ) (hΔ : ∀ n ω t,t∈Θ →
     |sampleLogLikelihood X Y g n ω t-expectedLogLikelihood μ (X 0) (Y 0) g t| ≤ Δ n ω)
   (hlim : CP μ Δ 0) : CP μ that θ := by
  have hgm := hg θ hθ
  have hp := iid_positive_at_parameter μ X Y hiid g θ hgm (hpos θ hθ)
  exact product_mle_consistency_core μ X Y g Θ hc θ hθ hM hunique that hthat hp
    (fun n ω => hmax n ω θ hθ) Δ hΔ hlim


/-- For an identified correctly specified conditional mixture, maximizers of the actual product likelihood consistently estimate the full parameter vector under the explicit compact uniform-log regularities.
Target P001-T12: Section 5.2.5, the 'any subset' sentence, corrected: consistency and efficiency of the mixture ML estimator under identification of the full parameter vector.
Location: p. 199 (PDF p. 217), second paragraph. -/
theorem product_identified_mixture_ml_consistency {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {M K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (p : (Fin τ → ℝ) → Fin M → ℝ) (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (Θ : Set (Fin τ → ℝ)) (hc : IsCompact Θ) (θ : Fin τ → ℝ) (hθ : θ∈Θ)
   (hp : ∀ t∈Θ,(∀ m,0 ≤ p t m) ∧ (∑ m,p t m)=1)
   (hg : ∀ t∈Θ,∀ m,Measurable (fun xy : (Fin K → ℝ) × ℝ => g m xy.2 xy.1 t))
   (hnonneg : ∀ t∈Θ,∀ m y x,0 ≤ g m y x t)
   (hnorm : ∀ t∈Θ,∀ m x,(∫⁻ y,ENNReal.ofReal (g m y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=conditionalModelLaw νX κ (mixtureFamily p g) θ)
   (hlog : ∀ t∈Θ,Integrable
     (fun ω => Real.log (mixtureFamily p g (Y 0 ω) (X 0 ω) t)) μ)
   (hpositiveModel : ∀ t∈Θ,∀ᵐ ω ∂μ,0 < mixtureFamily p g (Y 0 ω) (X 0 ω) t)
   (hM : ContinuousOn (expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g)) Θ)
   (hunique : ∀ t∈Θ,expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t ≤ 
     expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) θ ∧
     (expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t=
       expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) θ → t=θ))
   (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n,Measurable (that n))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → sampleLikelihood X Y (mixtureFamily p g) n ω t ≤ 
     sampleLikelihood X Y (mixtureFamily p g) n ω (that n ω))
   (Δ : ℕ → Ω → ℝ) (hΔ : ∀ n ω t,t∈Θ →
     |sampleLogLikelihood X Y (mixtureFamily p g) n ω t-
       expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t| ≤ Δ n ω)
   (hlim : CP μ Δ 0) : CP μ that θ := by
  have hgm : Measurable (fun xy : (Fin K → ℝ) × ℝ => mixtureFamily p g xy.2 xy.1 θ) := by
    unfold mixtureFamily
    apply Finset.measurable_sum
    intro m _
    exact (hg θ hθ m).const_mul (p θ m)
  have hp := iid_positive_at_parameter μ X Y hiid (mixtureFamily p g) θ hgm (hpositiveModel θ hθ)
  exact product_mle_consistency_core μ X Y (mixtureFamily p g) Θ hc θ hθ hM hunique that hthat hp
    (fun n ω => hmax n ω θ hθ) Δ hΔ hlim


/-- With unit scales and zero means, both printed correlation endpoints force a zero denominator; Lean’s totalized endpoint formula is identically zero and integrates to zero rather than one.
Target P001-T38: The sentence after Theorem 2.1.21 ('any linear combination of any number of mutually independent normal random variables must itself be normal') and the parameter range of the bivariate normal PDF in footnote 13, as printed.
Location: p. 56 (PDF p. 74), sentence after Theorem 2.1.21; p. 66 (PDF p. 84), footnote 13. Definition 2.1.19: p. 55 (PDF p. 73). -/
theorem bivariate_normal_endpoint_counterexample : (1 : ℝ)∈Set.Icc (-1) 1 ∧ (-1 : ℝ)∈Set.Icc (-1) 1 ∧
   (2*Real.pi*Real.sqrt (1-(1 : ℝ)^2)=0) ∧
   (2*Real.pi*Real.sqrt (1-(-1 : ℝ)^2)=0) ∧
   (∀ xy : ℝ × ℝ,bivariateNormalPDF 0 0 1 1 1 xy=0 ∧
     bivariateNormalPDF 0 0 1 1 (-1) xy=0) ∧
   (∫ xy : ℝ × ℝ,bivariateNormalPDF 0 0 1 1 1 xy)=0 ∧
   (∫ xy : ℝ × ℝ,bivariateNormalPDF 0 0 1 1 (-1) xy)=0 ∧ (0 : ℝ)≠1 := by
  have hf (xy : ℝ × ℝ) : bivariateNormalPDF 0 0 1 1 1 xy=0 ∧
      bivariateNormalPDF 0 0 1 1 (-1) xy=0 := by
    constructor <;> norm_num [bivariateNormalPDF]
  refine ⟨by norm_num,by norm_num,by norm_num,by norm_num,hf,?_,?_,by norm_num⟩
  · simp_rw [(hf _).1]
    simp
  · simp_rw [(hf _).2]
    simp


end


noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- "Jointly continuous random variables ... with joint PDF f" (the
marginal/conditional PDF discussion on p. 42), represented by the actual
vector law with respect to Lebesgue measure. -/
def HasVectorPDF {K : ℕ} (ν : Measure (Fin K → ℝ)) (f : (Fin K → ℝ) → ℝ) : Prop :=
  AEMeasurable f volume ∧ (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
  ν = volume.withDensity (fun x => ENNReal.ofReal (f x))


/-- For a continuous covariate vector with finite mean and a PDF positive on an open neighborhood of that mean, continuous CEF versions agree there and transfer an existing coordinate derivative.
Target P001-T4: Definition 4.3.7 (Partial Derivative at the Average), corrected with a support condition at the covariate mean.
Location: p. 167 (PDF p. 185), Definition 4.3.7; p. 168 (PDF p. 186), first paragraph. -/
theorem pda_unique_on_open_support {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
  (X : Ω → Fin K → ℝ) (Y : Ω → ℝ) (hX : Measurable X)
  (hXi : ∀ k, Integrable (fun ω => X ω k) μ) (hY : Integrable Y μ)
  (f : (Fin K → ℝ) → ℝ) (hf : HasVectorPDF (μ.map X) f)
  (U : Set (Fin K → ℝ)) (hU : IsOpen U)
  (hmean : (fun k => mean μ (fun ω => X ω k)) ∈ U)
  (hpositive : ∀ x ∈ U, 0 < f x)
  (m m' : (Fin K → ℝ) → ℝ) (hm : IsCEF μ X Y m) (hm' : IsCEF μ X Y m')
  (hc : ContinuousOn m U) (hc' : ContinuousOn m' U)
  (k : Fin K) (a : ℝ)
  (hd : HasDerivAt (fun t => m (Function.update
    (fun j => mean μ (fun ω => X ω j)) k (mean μ (fun ω => X ω k)+t))) a 0) :
  Set.EqOn m m' U ∧
  HasDerivAt (fun t => m' (Function.update
    (fun j => mean μ (fun ω => X ω j)) k (mean μ (fun ω => X ω k)+t))) a 0 ∧
  partialAt m (fun j => mean μ (fun ω => X ω j)) k =
    partialAt m' (fun j => mean μ (fun ω => X ω j)) k := by
  have hcomp : m ∘ X =ᵐ[μ] m' ∘ X :=
    (isCEF_condExp μ X hX Y m hm).trans (isCEF_condExp μ X hX Y m' hm').symm
  have hmap : m =ᵐ[μ.map X] m' := by
    exact (ae_map_iff hX.aemeasurable (measurableSet_eq_fun hm.1 hm'.1)).mpr hcomp
  rw [hf.2.2.2] at hmap
  have hvol := (ae_withDensity_iff' hf.1.ennreal_ofReal).mp hmap
  have hrestrict : m =ᵐ[volume.restrict U] m' := by
    apply (ae_restrict_iff' hU.measurableSet).mpr
    filter_upwards [hvol] with x hx
    intro hxU
    exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (hpositive x hxU)))
  have he := pda_unique_on_open_support_supporting U hU _ hmean m m' hc hc' hrestrict k
  have hd' := pda_derivative_transfers_on_open_support U hU _ hmean m m' hc hc' hrestrict k a hd
  exact ⟨he.1,hd',he.2⟩


/-- "Pr_theta of the n iid observations" (Section 5.2.5, p. 199; T11).
Coordinatewise probability convergence is equivalent to vector convergence in
probability in this finite parameter dimension. -/
def FiniteMixtureConsistent
  (T : (n : ℕ) → (Fin n → Fin 4) → Fin 3 → ℝ) (θ : Fin 3 → ℝ) : Prop :=
  ∀ k : Fin 3, ∀ ε : ℝ, 0 < ε → Tendsto
    (fun n => finiteMixtureSampleProb θ (fun y => |T n y k-θ k| < ε))
    atTop (nhds 1)

/-- No estimator based on the actual iid disjoint-mixture sample laws can be consistent at both full vectors (1,1/3,1/4) and (1,1/3,3/4).
Target P001-T11: Section 5.2.5, the sentence 'If any subset of the models ... jointly characterize the conditional distribution of $Y$, then this estimator is consistent and asymptotically efficient', as printed.
Location: p. 199 (PDF p. 217), second paragraph; the mixture and its parameter vector: pp. 198–199 (PDF pp. 216–217). -/
theorem finite_mixture_statistical_impossibility
  (T : (n : ℕ) → (Fin n → Fin 4) → Fin 3 → ℝ) :
  ¬ (FiniteMixtureConsistent T (![1,1/3,1/4] : Fin 3 → ℝ) ∧
     FiniteMixtureConsistent T (![1,1/3,3/4] : Fin 3 → ℝ)) := by
  rintro ⟨ha,hb⟩
  have ha' := ha 2 (1/8) (by norm_num)
  have hb' := hb 2 (1/8) (by norm_num)
  have ea := ha'.eventually (Ioi_mem_nhds (by norm_num : (3/4 : ℝ) < 1))
  have eb := hb'.eventually (Ioi_mem_nhds (by norm_num : (3/4 : ℝ) < 1))
  have bad : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [ea,eb] with n han hbn
    have h := (finite_mixture_iid_probabilities n (T n)).2.2.2
    change (3/4 : ℝ) < finiteMixtureSampleProb (![1,1/3,1/4])
      (fun y => |T n y 2-1/4| < 1/8) at han
    change (3/4 : ℝ) < finiteMixtureSampleProb (![1,1/3,3/4])
      (fun y => |T n y 2-3/4| < 1/8) at hbn
    linarith
  obtain ⟨n,hn⟩ := Filter.Eventually.exists bad
  exact hn

/-- The compact four-point mixture counterexample, including attained MLEs
and the actual two sampling experiments (p. 199, T11). -/
def UnusedMixtureWitness : Prop :=
  IsCompact disjointMixtureParameterSet ∧
  (![1,1/3,1/4] : Fin 3 → ℝ) ∈ disjointMixtureParameterSet ∧
  (![1,1/3,3/4] : Fin 3 → ℝ) ∈ disjointMixtureParameterSet ∧
  disjointMixture 1 (1/3) (1/4) = ![2/3,1/3,0,0] ∧
  disjointMixture 1 (1/3) (3/4) = ![2/3,1/3,0,0] ∧
  (∀ n (y : Fin n → Fin 4), ∃ t ∈ disjointMixtureParameterSet,
    ∀ u ∈ disjointMixtureParameterSet, disjointMixtureLikelihood y u ≤
      disjointMixtureLikelihood y t) ∧
  (∀ n (T : (Fin n → Fin 4) → Fin 3 → ℝ),
    (∑ y : Fin n → Fin 4, disjointMixtureLikelihood y ![1,1/3,1/4]) = 1 ∧
    (∀ y : Fin n → Fin 4, 0 ≤ disjointMixtureLikelihood y ![1,1/3,1/4]) ∧
    (∀ y : Fin n → Fin 4, disjointMixtureLikelihood y ![1,1/3,1/4] =
      disjointMixtureLikelihood y ![1,1/3,3/4]) ∧
    finiteMixtureSampleProb (![1,1/3,1/4]) (fun y => |T y 2-1/4| < 1/8) +
      finiteMixtureSampleProb (![1,1/3,3/4]) (fun y => |T y 2-3/4| < 1/8) ≤ 1) ∧
  (∀ T : (n : ℕ) → (Fin n → Fin 4) → Fin 3 → ℝ,
    ¬ (FiniteMixtureConsistent T (![1,1/3,1/4]) ∧
       FiniteMixtureConsistent T (![1,1/3,3/4])))

/-- The exact compact mixture has attained sample likelihood maxima and identical normalized iid sample laws at two distinct true full parameters; no estimator is consistent at both.
Target P001-T11: Section 5.2.5, the sentence 'If any subset of the models ... jointly characterize the conditional distribution of $Y$, then this estimator is consistent and asymptotically efficient', as printed.
Location: p. 199 (PDF p. 217), second paragraph; the mixture and its parameter vector: pp. 198–199 (PDF pp. 216–217). -/
theorem unused_component_nonidentification : UnusedMixtureWitness := by
  rcases finite_mixture_compact_attainment with ⟨hc,ha,hb,hmax⟩
  refine ⟨hc,ha,hb,?_,?_,(fun n y => (hmax n y).2),
    finite_mixture_iid_probabilities,finite_mixture_statistical_impossibility⟩
  all_goals ext i; fin_cases i <;> norm_num [disjointMixture]

/-- The compact disjoint-mixture counterexample includes attained ML fits, the exact same iid sample laws and impossibility of full-vector consistency at both specified truths.
Target P001-T11: Section 5.2.5, the sentence 'If any subset of the models ... jointly characterize the conditional distribution of $Y$, then this estimator is consistent and asymptotically efficient', as printed.
Location: p. 199 (PDF p. 217), second paragraph; the mixture and its parameter vector: pp. 198–199 (PDF pp. 216–217). -/
theorem nonidentification_no_two_consistent_targets : UnusedMixtureWitness := by
  exact unused_component_nonidentification

/-- The compact disjoint-mixture counterexample includes attained ML fits, the exact same iid sample laws and impossibility of full-vector consistency at both specified truths.
Target P001-T11: Section 5.2.5, the sentence 'If any subset of the models ... jointly characterize the conditional distribution of $Y$, then this estimator is consistent and asymptotically efficient', as printed.
Location: p. 199 (PDF p. 217), second paragraph; the mixture and its parameter vector: pp. 198–199 (PDF pp. 216–217). -/
theorem unused_component_counterexample_full : UnusedMixtureWitness := by
  exact unused_component_nonidentification

/-- "The full applicant information shown to voters is (X,D); there is no
additional applicant information or personal acquaintance" (T21; application
p. 278). This structure enumerates applicant information. -/
structure LeafletInformation where
  nonGender : ℝ
  gender : Bool
  personallyKnown : Bool
  deriving DecidableEq

/-- "X=0; D is the gender shown on the leaflet" (T21). -/
def electorateLeaflet (d : Bool) : LeafletInformation := ⟨0,d,false⟩

/-- "Voter k votes no exactly when k ≤ 20+40u+5d" (T21).
Its arguments are the voter's preference type, voter index and the displayed
information; it has no additional applicant input. -/
def electorateVote (u : ℝ) (k : Fin 100) (info : LeafletInformation) : Prop :=
  (k.val+1 : ℝ) ≤ 20+40*u+5*(if info.gender then 1 else 0)

/-- Percentage voting no among exactly 100 voters (T21).
For 100 voters, the count is numerically the percentage. -/
def electorateVoteShare (i : Fin 4) (d : Bool) : ℝ :=
  ((Finset.univ.filter (fun k : Fin 100 =>
    electorateVote (electorateU i) k (electorateLeaflet d))).card : ℝ)

/-- The information premise, voting rule, potential-outcomes model,
positivity and explicit conditional-independence failure in T21 (p. 278). -/
def ElectorateWitness : Prop :=
  (∀ d, (electorateLeaflet d).nonGender = 0 ∧
    (electorateLeaflet d).gender = d ∧
    (electorateLeaflet d).personallyKnown = false) ∧
  (∀ u k info info', info.gender = info'.gender →
    (electorateVote u k info ↔ electorateVote u k info')) ∧
  (∀ i d, electorateVoteShare i d = electorateOutcome (if d then 1 else 0) i) ∧
  (∀ i, electorateOutcome (electorateD i) i =
    observedOutcome (electorateOutcome 0 i) (electorateOutcome 1 i) (electorateD i)) ∧
  (∀ i, electorateOutcome 0 i ∈ Set.Icc (0 : ℝ) 100 ∧
    electorateOutcome 1 i ∈ Set.Icc (0 : ℝ) 100) ∧
  (∀ i, electorateOutcome 1 i-electorateOutcome 0 i = 5) ∧
  fprob binaryJoint (fun i => electorateD i=1) = 1/2 ∧
  fcond binaryJoint (fun i => electorateOutcome (electorateD i) i) electorateD 1 = 55 ∧
  fcond binaryJoint (fun i => electorateOutcome (electorateD i) i) electorateD 0 = 30 ∧
  ¬ FCondIndep binaryJoint (fun i => (electorateOutcome 0 i,electorateOutcome 1 i))
      electorateD (fun _ => (0 : ℝ))

/-- The 100-voter rule using only displayed gender and own preferences produces precisely the stated potential no-vote percentages.
Target P001-T21: Section 7.5, the claim that if the coded applicant descriptions account for all the information presented to voters then 'by definition, $D_i$ must be conditionally independent of potential outcomes', as printed.
Location: p. 278 (PDF p. 296), paragraph beginning 'The fact that random assignment is unlikely to hold'; the application's setting: pp. 276–278 (PDF pp. 294–296). -/
theorem electorate_votes_count (i : Fin 4) (d : Bool) :
  electorateVoteShare i d = electorateOutcome (if d then 1 else 0) i := by
  let t : ℕ := 20+40*(if i.val < 2 then 0 else 1)+5*(if d then 1 else 0)
  have ht : t ≤ 100 := by dsimp [t]; split_ifs <;> omega
  have hv (k : Fin 100) :
      electorateVote (electorateU i) k (electorateLeaflet d) ↔ k.val < t := by
    fin_cases i <;> cases d <;>
      norm_num [electorateVote,electorateU,electorateLeaflet,t] <;> norm_cast <;> omega
  have he : Finset.univ.filter (fun k : Fin 100 =>
      electorateVote (electorateU i) k (electorateLeaflet d)) =
      Finset.univ.filter (fun k : Fin 100 => k.val < t) := by
    ext k; simp [hv]
  have hcard : (Finset.univ.filter (fun k : Fin 100 => k.val < t)).card = t := by
    have he' : (Finset.univ.filter (fun k : Fin 100 => k.val < t)).map
        (Fin.valEmbedding) = Finset.range t := by
      ext k
      simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,
        Fin.valEmbedding_apply,Finset.mem_range]
      constructor
      · rintro ⟨j,hj,rfl⟩; exact hj
      · intro hk; exact ⟨⟨k,lt_of_lt_of_le hk ht⟩,hk,rfl⟩
    have hc := congrArg Finset.card he'
    simpa using hc
  unfold electorateVoteShare
  rw [he,hcard]
  fin_cases i <;> cases d <;> norm_num [t,electorateOutcome,electorateU]

/-- Fully recorded leaflets with no personal acquaintance and the explicit voter rule satisfy the potential-outcomes model and overlap, but the potential outcomes are not conditionally independent of gender.
Target P001-T21: Section 7.5, the claim that if the coded applicant descriptions account for all the information presented to voters then 'by definition, $D_i$ must be conditionally independent of potential outcomes', as printed.
Location: p. 278 (PDF p. 296), paragraph beginning 'The fact that random assignment is unlikely to hold'; the application's setting: pp. 276–278 (PDF pp. 294–296). -/
theorem complete_coding_not_ignorability : ElectorateWitness := by
  refine ⟨?_,?_,electorate_votes_count,?_,?_,?_,?_,?_,?_,
    electorate_potential_outcomes_not_cia_supporting.2⟩
  · intro d; exact ⟨rfl,rfl,rfl⟩
  · intro u k info info' h; simp only [electorateVote,h]
  · intro i; fin_cases i <;>
      norm_num [electorateD,electorateU,electorateOutcome,observedOutcome]
  · intro i; fin_cases i <;> norm_num [electorateU,electorateOutcome,Set.mem_Icc]
  · exact complete_coding_not_ignorability_supporting.1
  · exact complete_coding_not_ignorability_supporting.2.1
  · exact complete_coding_not_ignorability_supporting.2.2.2.2.1
  · exact complete_coding_not_ignorability_supporting.2.2.2.2.2.1

/-- The entire admissible electorate counterexample, including its information-completeness premise and voting rule, violates ignorability.
Target P001-T21: Section 7.5, the claim that if the coded applicant descriptions account for all the information presented to voters then 'by definition, $D_i$ must be conditionally independent of potential outcomes', as printed.
Location: p. 278 (PDF p. 296), paragraph beginning 'The fact that random assignment is unlikely to hold'; the application's setting: pp. 276–278 (PDF pp. 294–296). -/
theorem electorate_potential_outcomes_not_cia : ElectorateWitness := by
  exact complete_coding_not_ignorability

/-- Every finite or countably infinite nonempty measurable partition satisfies total probability; the conditional form requires strictly positive cell probabilities.
Target P001-T24: Theorem 1.1.13 (Law of Total Probability): the positivity condition in its proof and the partition remark after the proof, corrected.
Location: Theorem 1.1.13: p. 12 (PDF p. 30). Proof and the remark after it: p. 13 (PDF p. 31). Definition 1.1.12: p. 12 (PDF p. 30). Definition 1.1.8 and Theorem 1.1.9: p. 10 (PDF p. 28). -/
theorem total_probability_partition {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {ι : Type*} [Countable ι] (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (hne : ∀ i, (A i).Nonempty)
   (hdis : Pairwise (fun i j => Disjoint (A i) (A j))) (hcover : (⋃ i, A i)=Set.univ)
   (B : Set Ω) (hB : MeasurableSet B) :
   prob μ B = ∑' i, prob μ (B ∩ A i) ∧
   ((∀ i, 0  <  prob μ (A i)) → prob μ B = ∑' i,
     (prob μ (B ∩ A i)/prob μ (A i))*prob μ (A i)) := by
  have hdis' : Pairwise (fun i j => Disjoint (B ∩ A i) (B ∩ A j)) := by
    intro i j hij
    exact (hdis hij).mono Set.inter_subset_right Set.inter_subset_right
  have hcover' : (⋃ i, B ∩ A i)=B := by
    rw [← Set.inter_iUnion,hcover,Set.inter_univ]
  have hμ : μ B=∑' i, μ (B ∩ A i) := by
    calc
      μ B=μ (⋃ i, B ∩ A i) := by rw [hcover']
      _=∑' i, μ (B ∩ A i) := measure_iUnion hdis' (fun i => hB.inter (hA i))
  have hr : prob μ B=∑' i, prob μ (B ∩ A i) := by
    unfold prob
    rw [hμ,ENNReal.tsum_toReal_eq (fun i => measure_ne_top μ _)]
  refine ⟨hr,?_⟩
  intro hp
  rw [hr]
  apply tsum_congr
  intro i
  exact (div_mul_cancel₀ _ (ne_of_gt (hp i))).symm

/-- For iid variables with finite strictly positive variance, the n-denominator plug-in variance has expectation (n−1)/n times population variance and is consistent.
Target P001-T54: Theorem 3.2.19 (Properties of the Plug-In Sample Variance), with the consistency step of its proof corrected (WLLN for i.i.d. integrable variables).
Location: Theorem 3.2.19: p. 106 (PDF p. 124). Proof: pp. 106–107 (PDF pp. 124–125). Definition 3.2.18: p. 106. -/
theorem sample_variance_unbiased_factor_and_consistency {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ) (hv : 0 < var μ (X 0)) :
   (∀ n, 0 < n → mean μ (sampleVariance X n)=((n : ℝ)-1)/n*var μ (X 0)) ∧
   CP μ (sampleVariance X) (var μ (X 0)) := by
  exact sample_variance_unbiased_factor_and_consistency_supporting μ X hiid h2

/-- For a sequence of real random variables on a probability space, convergence in probability to c is equivalent to convergence of the centered sequence to zero.
Target P001-T55: Definition 3.2.32 (Consistency of Sampling Variance and Standard Error Estimators) and footnote 23, with the estimator's hat restored in four places.
Location: pp. 113–114 (PDF pp. 131–132), Definition 3.2.32; footnote 23, p. 114 (PDF p. 132). -/
theorem probability_convergence_centering_equivalence {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (V : ℕ → Ω → ℝ) (hT : ∀ n, Measurable (V n)) (v : ℝ) :
   CP μ V v ↔ CP μ (fun n ω => V n ω-v) 0 := by
  exact probability_convergence_centering_equivalence_supporting μ V v

/-- The corrected variance and standard-error consistency definitions have the equivalent centered convergence forms of footnote 23.
Target P001-T55: Definition 3.2.32 (Consistency of Sampling Variance and Standard Error Estimators) and footnote 23, with the estimator's hat restored in four places.
Location: pp. 113–114 (PDF pp. 131–132), Definition 3.2.32; footnote 23, p. 114 (PDF p. 132). -/
theorem sample_mean_variance_estimate_scale {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (vhat : ℕ → Ω → ℝ)
  (hm : ∀ n, Measurable (vhat n)) (v : ℝ) :
  (VarianceConsistent μ vhat v ↔
    CP μ (fun n ω => (n : ℝ)*vhat n ω-v) 0) ∧
  (SEConsistent μ vhat v ↔
    CP μ (fun n ω => Real.sqrt n*Real.sqrt (vhat n ω)-Real.sqrt v) 0) := by
  constructor
  · exact probability_convergence_centering_equivalence_supporting μ
      (fun n ω => (n : ℝ)*vhat n ω) v
  · exact probability_convergence_centering_equivalence_supporting μ
      (fun n ω => Real.sqrt n*Real.sqrt (vhat n ω)) (Real.sqrt v)

/-- "D(t)=E_X[KL(f(Y|X) || g(Y,X;t))]" (T8 correction to Definition
5.2.7, p. 195). This extended nonnegative integral retains infinite KL and
assigns infinity when the model excludes positive true mass. The real integral
averageKL is used only in finite-entropy identities. -/
def averageKLExt {K τ : ℕ} (νX : Measure (Fin K → ℝ)) (κ : Measure ℝ)
    (f : ℝ → (Fin K → ℝ) → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, InformationTheory.klDiv
    (κ.withDensity (fun y => ENNReal.ofReal (f y x)))
    (κ.withDensity (fun y => ENNReal.ofReal (g y x t))) ∂νX


theorem four_atom_integral (f : ℝ × ℝ → ℝ) (a b c d : ℝ≥0∞)
    (ha : a ≠ ∞) (hb : b ≠ ∞) (hc : c ≠ ∞) (hd : d ≠ ∞) :
    (∫ z, f z ∂(a • Measure.dirac (0,0) + b • Measure.dirac (0,1) +
      c • Measure.dirac (1,0) + d • Measure.dirac (1,1))) =
      a.toReal*f (0,0)+b.toReal*f (0,1)+c.toReal*f (1,0)+d.toReal*f (1,1) := by
  have h0 : Integrable f (a • Measure.dirac (0,0)) :=
    (integrable_dirac (by simp)).smul_measure ha
  have h1 : Integrable f (b • Measure.dirac (0,1)) :=
    (integrable_dirac (by simp)).smul_measure hb
  have h2 : Integrable f (c • Measure.dirac (1,0)) :=
    (integrable_dirac (by simp)).smul_measure hc
  have h3 : Integrable f (d • Measure.dirac (1,1)) :=
    (integrable_dirac (by simp)).smul_measure hd
  rw [integral_add_measure ((h0.add_measure h1).add_measure h2) h3,
    integral_add_measure (h0.add_measure h1) h2,integral_add_measure h0 h1]
  simp [integral_smul_measure,smul_eq_mul]

theorem iid_snd {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : ℕ → Ω → ℝ) (h : IID μ (fun i ω => (X i ω,Y i ω))) : IID μ Y := by
  exact ⟨fun i => measurable_snd.comp (h.1 i),
    h.2.1.comp (fun _ => Prod.snd) (fun _ => measurable_snd),
    fun i => (h.2.2 i).comp measurable_snd⟩

theorem four_atom_snd_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hm : Measurable (fun ω => (X ω,Y ω))) (a b c d : ℝ≥0∞)
    (hlaw : μ.map (fun ω => (X ω,Y ω)) = a • Measure.dirac (0,0) +
      b • Measure.dirac (0,1) + c • Measure.dirac (1,0) + d • Measure.dirac (1,1)) :
    MemLp Y 2 μ := by
  have hbin : ∀ᵐ ω ∂μ, Y ω=0 ∨ Y ω=1 := by
    apply (ae_map_iff (μ := μ) hm.aemeasurable
      (show MeasurableSet {z : ℝ×ℝ | z.2=0 ∨ z.2=1} from
        (measurable_snd (measurableSet_singleton _)).union
        (measurable_snd (measurableSet_singleton _)))).mp
    rw [hlaw]
    simp only [ae_add_measure_iff]
    have hh (z : ℝ×ℝ) (hz : z.2=0 ∨ z.2=1) (e : ℝ≥0∞) :
        ∀ᵐ z' ∂e • Measure.dirac z, z'.2=0 ∨ z'.2=1 := by
      apply Measure.ae_smul_measure _ e
      simpa using hz
    exact ⟨⟨⟨hh _ (Or.inl rfl) a,hh _ (Or.inr rfl) b⟩,
      hh _ (Or.inl rfl) c⟩,hh _ (Or.inr rfl) d⟩
  exact MemLp.of_bound (measurable_snd.comp hm).aestronglyMeasurable 1
    (hbin.mono (by intro ω h; rcases h with h|h <;> simp [h]))

theorem four_atom_snd_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hm : Measurable (fun ω => (X ω,Y ω))) (a b c d : ℝ≥0∞)
    (ha : a ≠ ∞) (hb : b ≠ ∞) (hc : c ≠ ∞) (hd : d ≠ ∞)
    (hlaw : μ.map (fun ω => (X ω,Y ω)) = a • Measure.dirac (0,0) +
      b • Measure.dirac (0,1) + c • Measure.dirac (1,0) + d • Measure.dirac (1,1)) :
    mean μ Y=b.toReal+d.toReal ∧
    var μ Y=b.toReal+d.toReal-(b.toReal+d.toReal)^2 := by
  have hm1 := integral_map (μ := μ) hm.aemeasurable
    (show AEStronglyMeasurable (fun z : ℝ×ℝ => z.2) _ from measurable_snd.aestronglyMeasurable)
  have hm2 := integral_map (μ := μ) hm.aemeasurable
    (show AEStronglyMeasurable (fun z : ℝ×ℝ => z.2^2) _ from
      (measurable_snd.pow_const 2).aestronglyMeasurable)
  rw [hlaw,four_atom_integral _ a b c d ha hb hc hd] at hm1 hm2
  simp only [zero_pow (by decide : 2≠0),one_pow,mul_zero,mul_one,zero_add,add_zero] at hm1 hm2
  refine ⟨hm1.symm,?_⟩
  dsimp [var]
  rw [variance_eq_sub (four_atom_snd_memLp μ X Y hm a b c d hlaw)]
  simpa only [Pi.pow_apply,hm1.symm,hm2.symm]

theorem clipped_distance_half (z : ℝ) :
    |clip (1/10) (9/10) z-1/2|≤|z-1/2| := by
  have hL : LipschitzWith 1 (clip (1/10) (9/10)) :=
    (LipschitzWith.id.const_min _).const_max _
  have hh := hL.dist_le_mul z (1/2)
  norm_num [clip,Real.dist_eq] at hh ⊢
  exact hh

theorem clipped_bernoulli_chebyshev {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hiid : IID μ Y) (h2 : MemLp (Y 0) 2 μ)
    (hm : mean μ (Y 0)=1/2) (hv : var μ (Y 0)=1/4)
    (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
    prob μ {ω | ε≤|clip (1/10) (9/10) (sampleMean Y n ω)-1/2|}≤
      1/(4*(n:ℝ)*ε^2) := by
  have hb := iid_sample_mean_chebyshev μ Y hiid h2 n hn ε hε
  rw [hm,hv] at hb
  calc
    _ ≤ prob μ {ω | ε≤|sampleMean Y n ω-1/2|} := by
      apply measureReal_mono _ (measure_ne_top μ _)
      exact fun ω hω => hω.trans (clipped_distance_half _)
    _ ≤ (1/4)/(ε^2*(n:ℝ)) := hb
    _ = _ := by ring

theorem clipped_bernoulli_far_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : Measurable Z)
    (n : ℕ) (hb : prob μ {ω | (1/8:ℝ)≤|Z ω-1/2|}≤16/(n:ℝ))
    (θ : ℝ) (hθ : θ=1/4 ∨ θ=3/4) :
    1-16/(n:ℝ)≤prob μ {ω | (1/8:ℝ)< |Z ω - θ| } := by
  have hset : {ω | (1/8:ℝ)< |Z ω - θ| }ᶜ ⊆ {ω | (1/8:ℝ)≤|Z ω-1/2|} := by
    intro ω hω
    have hω' : |Z ω-θ|≤1/8 := by simpa using hω
    have ht : |θ-1/2|≤|Z ω-θ|+|Z ω-1/2| := by
      calc
        _ = |(θ-Z ω)+(Z ω-1/2)| := by congr 1; ring
        _ ≤ |θ-Z ω|+|Z ω-1/2| := abs_add_le _ _
        _ = _ := by rw [abs_sub_comm θ (Z ω)]
    rcases hθ with rfl|rfl <;> norm_num at ht <;> change (1/8:ℝ)≤|Z ω-1/2| <;> linarith
  have hm : MeasurableSet {ω | (1/8:ℝ)< |Z ω - θ| } :=
    by simpa only [Real.norm_eq_abs] using
      measurableSet_lt measurable_const ((hZ.sub_const θ).norm)
  have he : prob μ {ω | (1/8:ℝ)< |Z ω - θ| }ᶜ=
      1-prob μ {ω | (1/8:ℝ)< |Z ω - θ| } := probReal_compl_eq_one_sub hm
  have hh := (measureReal_mono hset (measure_ne_top μ _)).trans hb
  change prob μ {ω | (1/8:ℝ)< |Z ω-θ|}ᶜ≤16/(n:ℝ) at hh
  rw [he] at hh
  linarith

theorem bernoulli_kl_minimum (p t : ℝ) (hp0 : 0<p) (hp1 : p<1)
    (ht0 : 0<t) (ht1 : t<1) :
    0≤bernoulliKL p t ∧ (bernoulliKL p t=0 ↔ t=p) := by
  have hid : bernoulliKL p t=
      (p*Real.log p+(1-p)*Real.log (1-p))-
      (p*Real.log t+(1-p)*Real.log (1-t)) := by
    rw [bernoulliKL,Real.log_div hp0.ne' ht0.ne',
      Real.log_div (sub_pos.mpr hp1).ne' (sub_pos.mpr ht1).ne']
    ring
  by_cases htp : t=p
  · subst t
    rw [hid]
    simp
  · have hh := bernoulli_log_strict_max p p t hp0.le hp1.le hp0 hp1 ht0 ht1
      (by simp) htp
    have hk : 0<bernoulliKL p t := by rw [hid]; linarith
    exact ⟨hk.le,iff_of_false hk.ne' htp⟩

theorem averaged_binary_kl_half (t : ℝ) (ht0 : 0<t) (ht1 : t<1) :
    (bernoulliKL (1/4) t+bernoulliKL (3/4) t)/2-
      (bernoulliKL (1/4) (1/2)+bernoulliKL (3/4) (1/2))/2=
      bernoulliKL (1/2) t := by
  dsimp [bernoulliKL]
  rw [Real.log_div (by norm_num : (1/4:ℝ)≠0) ht0.ne',
    Real.log_div (by norm_num : (1-1/4:ℝ)≠0) (sub_pos.mpr ht1).ne',
    Real.log_div (by norm_num : (3/4:ℝ)≠0) ht0.ne',
    Real.log_div (by norm_num : (1-3/4:ℝ)≠0) (sub_pos.mpr ht1).ne',
    Real.log_div (by norm_num : (1/4:ℝ)≠0) (by norm_num : (1/2:ℝ)≠0),
    Real.log_div (by norm_num : (1-1/4:ℝ)≠0) (by norm_num : (1-1/2:ℝ)≠0),
    Real.log_div (by norm_num : (3/4:ℝ)≠0) (by norm_num : (1/2:ℝ)≠0),
    Real.log_div (by norm_num : (1-3/4:ℝ)≠0) (by norm_num : (1-1/2:ℝ)≠0),
    Real.log_div (by norm_num : (1/2:ℝ)≠0) ht0.ne',
    Real.log_div (by norm_num : (1-1/2:ℝ)≠0) (sub_pos.mpr ht1).ne']
  norm_num
  <;> ring

/-- The binary joint law has unique fixed-covariate KL targets 1/4 and 3/4, but its unique pooled MLE is the clipped sample mean and converges to 1/2, with the stated finite Chebyshev bounds.
Target P001-T7: Theorem 5.2.8 (The ML Estimator Is Consistent for the Minimum KL Divergence Predictor), with the target defined by the KL divergence at a fixed $\mathbf{x}$, as printed.
Location: p. 195 (PDF p. 213), Theorem 5.2.8 and Definition 5.2.7. -/
theorem conditional_kl_counterexample_finite {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → ℝ)
  (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
  (hlaw : μ.map (fun ω => (X 0 ω,Y 0 ω)) =
    (3/8 : ℝ≥0∞) • Measure.dirac (0,0) + (1/8 : ℝ≥0∞) • Measure.dirac (0,1) +
    (1/8 : ℝ≥0∞) • Measure.dirac (1,0) + (3/8 : ℝ≥0∞) • Measure.dirac (1,1)) :
  (∀ p ∈ ({(1/4 : ℝ),3/4} : Set ℝ), ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
    0 ≤ bernoulliKL p t ∧ (bernoulliKL p t=0 ↔ t=p)) ∧
  (∀ n : ℕ, 0 < n → ∀ y : Fin n → ℝ, (∀ i, y i=0 ∨ y i=1) →
    ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
      (∏ i, if y i=1 then t else 1-t) ≤
        ∏ i, if y i=1 then clip (1/10) (9/10) (finiteSampleMean y)
          else 1-clip (1/10) (9/10) (finiteSampleMean y)) ∧
  (∀ n : ℕ, 0 < n → ∀ y : Fin n → ℝ, (∀ i, y i=0 ∨ y i=1) →
    ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
      ((∏ i, if y i=1 then t else 1-t) =
        ∏ i, if y i=1 then clip (1/10) (9/10) (finiteSampleMean y)
          else 1-clip (1/10) (9/10) (finiteSampleMean y)) ↔
      t=clip (1/10) (9/10) (finiteSampleMean y)) ∧
  mean μ (Y 0)=1/2 ∧ var μ (Y 0)=1/4 ∧
  (∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε →
    prob μ {ω | ε ≤ |clip (1/10) (9/10) (sampleMean Y n ω)-1/2|} ≤
      1/(4*(n : ℝ)*ε^2)) ∧
  (∀ n : ℕ, 0 < n →
    1-16/(n : ℝ) ≤ prob μ {ω | 1/8 < |clip (1/10) (9/10) (sampleMean Y n ω)-1/4|} ∧
    1-16/(n : ℝ) ≤ prob μ {ω | 1/8 < |clip (1/10) (9/10) (sampleMean Y n ω)-3/4|}) ∧
  CP μ (fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)) (1/2) ∧
  ¬ CP μ (fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)) (1/4) ∧
  ¬ CP μ (fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)) (3/4) ∧
  (∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
    (bernoulliKL (1/4) (1/2)+bernoulliKL (3/4) (1/2))/2 ≤
      (bernoulliKL (1/4) t+bernoulliKL (3/4) t)/2 ∧
    ((bernoulliKL (1/4) t+bernoulliKL (3/4) t)/2 =
      (bernoulliKL (1/4) (1/2)+bernoulliKL (3/4) (1/2))/2 ↔ t=1/2)) := by
  have hYi := iid_snd μ X Y hiid
  have h2 := four_atom_snd_memLp μ (X 0) (Y 0) (hiid.1 0) _ _ _ _ hlaw
  have hmom := four_atom_snd_moments μ (X 0) (Y 0) (hiid.1 0) _ _ _ _
    (by finiteness) (by finiteness) (by finiteness) (by finiteness) hlaw
  norm_num at hmom
  have hm : mean μ (Y 0)=1/2 := hmom.1
  have hv : var μ (Y 0)=1/4 := hmom.2
  have hkl : ∀ p ∈ ({(1/4 : ℝ),3/4} : Set ℝ), ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
      0≤bernoulliKL p t ∧ (bernoulliKL p t=0 ↔ t=p) := by
    intro p hp t ht
    rcases hp with rfl|hp
    · exact bernoulli_kl_minimum _ _ (by norm_num) (by norm_num)
        (by linarith [ht.1]) (by linarith [ht.2])
    · have he : p=3/4 := hp
      subst p
      exact bernoulli_kl_minimum _ _ (by norm_num) (by norm_num)
        (by linarith [ht.1]) (by linarith [ht.2])
  have hcheb : ∀ n : ℕ, 0<n → ∀ ε : ℝ, 0<ε →
      prob μ {ω | ε≤|clip (1/10) (9/10) (sampleMean Y n ω)-1/2|}≤
        1/(4*(n:ℝ)*ε^2) := clipped_bernoulli_chebyshev μ Y hYi h2 hm hv
  have hZm : ∀ n, Measurable (fun ω => clip (1/10) (9/10) (sampleMean Y n ω)) := by
    intro n
    have hYm : ∀ i, Measurable (Y i) := hYi.1
    unfold sampleMean clip
    fun_prop
  have hfar : ∀ n : ℕ, 0<n →
      1-16/(n:ℝ)≤prob μ {ω | (1/8:ℝ)< |clip (1/10) (9/10) (sampleMean Y n ω)-1/4|} ∧
      1-16/(n:ℝ)≤prob μ {ω | (1/8:ℝ)< |clip (1/10) (9/10) (sampleMean Y n ω)-3/4|} := by
    intro n hn
    have hb := hcheb n hn (1/8) (by norm_num)
    have hbr : 1/(4*(n:ℝ)*(1/8)^2)=16/(n:ℝ) := by ring
    rw [hbr] at hb
    exact ⟨clipped_bernoulli_far_bound μ _ (hZm n) n hb _ (Or.inl rfl),
      clipped_bernoulli_far_bound μ _ (hZm n) n hb _ (Or.inr rfl)⟩
  have hclip : Continuous (clip (1/10) (9/10)) :=
    continuous_const.max (continuous_const.min continuous_id)
  have hcp : CP μ (fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)) (1/2) := by
    have hh := probability_convergence_continuous_at μ (sampleMean Y) (mean μ (Y 0))
      (clip (1/10) (9/10)) (weak_law_finite_variance μ Y hYi h2) hclip.continuousAt
    simpa only [hm,clip,min_eq_right (by norm_num : (1/2:ℝ)≤9/10),
      max_eq_right (by norm_num : (1/10:ℝ)≤1/2)] using hh
  refine ⟨hkl,?_,?_,hm,hv,hcheb,hfar,hcp,?_,?_,?_⟩
  · intro n hn y hy t ht
    simpa only [finiteSampleMean] using (clipped_bernoulli_mle hn y hy).2 t ht |>.1
  · intro n hn y hy t ht
    simpa only [finiteSampleMean] using (clipped_bernoulli_mle hn y hy).2 t ht |>.2
  · intro hh
    have he := probability_limit_unique μ _ (1/2:ℝ) (1/4) hcp hh
    norm_num at he
  · intro hh
    have he := probability_limit_unique μ _ (1/2:ℝ) (3/4) hcp hh
    norm_num at he
  · intro t ht
    have hk := bernoulli_kl_minimum (1/2) t (by norm_num) (by norm_num)
      (by linarith [ht.1]) (by linarith [ht.2])
    have he := averaged_binary_kl_half t (by linarith [ht.1]) (by linarith [ht.2])
    constructor
    · linarith [hk.1]
    · constructor
      · intro hh
        exact hk.2.mp (by linarith)
      · intro hh
        subst t
        rfl

/-- The specified unique pooled Bernoulli MLE satisfies the complete finite and asymptotic counterexample to the fixed-covariate KL target.
Target P001-T7: Theorem 5.2.8 (The ML Estimator Is Consistent for the Minimum KL Divergence Predictor), with the target defined by the KL divergence at a fixed $\mathbf{x}$, as printed.
Location: p. 195 (PDF p. 213), Theorem 5.2.8 and Definition 5.2.7. -/
theorem conditional_kl_mle_wrong_target {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → ℝ)
  (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
  (hlaw : μ.map (fun ω => (X 0 ω,Y 0 ω)) =
    (3/8 : ℝ≥0∞) • Measure.dirac (0,0) + (1/8 : ℝ≥0∞) • Measure.dirac (0,1) +
    (1/8 : ℝ≥0∞) • Measure.dirac (1,0) + (3/8 : ℝ≥0∞) • Measure.dirac (1,1)) :
  (∀ p ∈ ({(1/4 : ℝ),3/4} : Set ℝ), ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
    0 ≤ bernoulliKL p t ∧ (bernoulliKL p t=0 ↔ t=p)) ∧
  (∀ n : ℕ, 0 < n → ∀ y : Fin n → ℝ, (∀ i, y i=0 ∨ y i=1) →
    ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
      (∏ i, if y i=1 then t else 1-t) ≤
        ∏ i, if y i=1 then clip (1/10) (9/10) (finiteSampleMean y)
          else 1-clip (1/10) (9/10) (finiteSampleMean y)) ∧
  (∀ n : ℕ, 0 < n → ∀ y : Fin n → ℝ, (∀ i, y i=0 ∨ y i=1) →
    ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
      ((∏ i, if y i=1 then t else 1-t) =
        ∏ i, if y i=1 then clip (1/10) (9/10) (finiteSampleMean y)
          else 1-clip (1/10) (9/10) (finiteSampleMean y)) ↔
      t=clip (1/10) (9/10) (finiteSampleMean y)) ∧
  mean μ (Y 0)=1/2 ∧ var μ (Y 0)=1/4 ∧
  (∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε →
    prob μ {ω | ε ≤ |clip (1/10) (9/10) (sampleMean Y n ω)-1/2|} ≤
      1/(4*(n : ℝ)*ε^2)) ∧
  (∀ n : ℕ, 0 < n →
    1-16/(n : ℝ) ≤ prob μ {ω | 1/8 < |clip (1/10) (9/10) (sampleMean Y n ω)-1/4|} ∧
    1-16/(n : ℝ) ≤ prob μ {ω | 1/8 < |clip (1/10) (9/10) (sampleMean Y n ω)-3/4|}) ∧
  CP μ (fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)) (1/2) ∧
  ¬ CP μ (fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)) (1/4) ∧
  ¬ CP μ (fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)) (3/4) ∧
  (∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
    (bernoulliKL (1/4) (1/2)+bernoulliKL (3/4) (1/2))/2 ≤
      (bernoulliKL (1/4) t+bernoulliKL (3/4) t)/2 ∧
    ((bernoulliKL (1/4) t+bernoulliKL (3/4) t)/2 =
      (bernoulliKL (1/4) (1/2)+bernoulliKL (3/4) (1/2))/2 ↔ t=1/2)) := by
  exact conditional_kl_counterexample_finite μ X Y hiid hlaw

/-- Keeping the conditional Bernoulli laws fixed but changing Pr[X=1] to q changes the pooled clipped MLE probability limit to 1/4+q/2.
Target P001-T7: Theorem 5.2.8 (The ML Estimator Is Consistent for the Minimum KL Divergence Predictor), with the target defined by the KL divergence at a fixed $\mathbf{x}$, as printed.
Location: p. 195 (PDF p. 213), Theorem 5.2.8 and Definition 5.2.7. -/
theorem changed_covariate_marginal_mle_limit {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → ℝ)
  (hiid : IID μ (fun i ω => (X i ω,Y i ω))) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
  (hlaw : μ.map (fun ω => (X 0 ω,Y 0 ω)) =
    ENNReal.ofReal ((1-q)*3/4) • Measure.dirac (0,0) +
    ENNReal.ofReal ((1-q)/4) • Measure.dirac (0,1) +
    ENNReal.ofReal (q/4) • Measure.dirac (1,0) +
    ENNReal.ofReal (q*3/4) • Measure.dirac (1,1)) :
  CP μ (fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)) (1/4+q/2) := by
  have hYi := iid_snd μ X Y hiid
  have h2 := four_atom_snd_memLp μ (X 0) (Y 0) (hiid.1 0) _ _ _ _ hlaw
  have hm := (four_atom_snd_moments μ (X 0) (Y 0) (hiid.1 0) _ _ _ _
    (by simp) (by simp) (by simp) (by simp) hlaw).1
  rw [ENNReal.toReal_ofReal (by nlinarith [hq.1,hq.2]),ENNReal.toReal_ofReal (by nlinarith [hq.1,hq.2])] at hm
  have hmean : mean μ (Y 0)=1/4+q/2 := by nlinarith [hm]
  have hclip : Continuous (clip (1/10) (9/10)) :=
    continuous_const.max (continuous_const.min continuous_id)
  have hcp := probability_convergence_continuous_at μ (sampleMean Y) (mean μ (Y 0))
    (clip (1/10) (9/10)) (weak_law_finite_variance μ Y hYi h2) hclip.continuousAt
  have he : clip (1/10) (9/10) (mean μ (Y 0))=1/4+q/2 := by
    rw [hmean]
    dsimp [clip]
    rw [min_eq_right (by linarith [hq.2]),max_eq_right (by linarith [hq.1])]
  simpa only [he] using hcp


/-- For a normalized nonnegative conditional model true at θ, averaged KL at θ is zero; a unique averaged-KL minimizer is θ.
Target P001-T8: Theorem 5.2.8 (The ML Estimator Is Consistent for the Minimum KL Divergence Predictor), corrected: the KL divergence averaged over the distribution of $\mathbf{X}$.
Location: p. 195 (PDF p. 213), Theorem 5.2.8; the explanatory paragraphs on p. 196 (PDF p. 214). -/
theorem true_model_averaged_kl_zero {K τ : ℕ}
  (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX]
  (κ : Measure ℝ) [SFinite κ]
  (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
  (Θ : Set (Fin τ → ℝ)) (θ tstar : Fin τ → ℝ) (hθ : θ ∈ Θ) (ht : tstar ∈ Θ)
  (hg : ∀ t ∈ Θ, Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
  (hgn : ∀ t ∈ Θ, ∀ y x, 0 ≤ g y x t)
  (hnorm : ∀ t ∈ Θ, ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ)=1)
  (hunique : ∀ t ∈ Θ,
    averageKLExt νX κ (fun y x => g y x θ) g tstar ≤
      averageKLExt νX κ (fun y x => g y x θ) g t ∧
    (averageKLExt νX κ (fun y x => g y x θ) g t =
      averageKLExt νX κ (fun y x => g y x θ) g tstar → t=tstar)) :
  averageKLExt νX κ (fun y x => g y x θ) g θ=0 ∧ tstar=θ := by
  have hz : averageKLExt νX κ (fun y x => g y x θ) g θ=0 := by
    unfold averageKLExt
    have hx (x : Fin K → ℝ) : IsProbabilityMeasure
        (κ.withDensity (fun y => ENNReal.ofReal (g y x θ))) := by
      constructor
      rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
      exact hnorm θ hθ x
    have hd (x : Fin K → ℝ) : InformationTheory.klDiv
        (κ.withDensity (fun y => ENNReal.ofReal (g y x θ)))
        (κ.withDensity (fun y => ENNReal.ofReal (g y x θ)))=0 := by
      letI := hx x
      exact InformationTheory.klDiv_self _
    simp only [hd,lintegral_zero]
  refine ⟨hz,?_⟩
  have ht0 := (hunique θ hθ).1
  have he : averageKLExt νX κ (fun y x => g y x θ) g tstar=0 := by
    simpa only [hz,le_zero_iff] using ht0
  exact ((hunique θ hθ).2 (by rw [hz,he])).symm

/-- Under correct specification, full-parameter identification, compactness, continuity and uniform log convergence, the actual product-likelihood mixture MLE is consistent.
Target P001-T12: Section 5.2.5, the 'any subset' sentence, corrected: consistency and efficiency of the mixture ML estimator under identification of the full parameter vector.
Location: p. 199 (PDF p. 217), second paragraph. -/
theorem identified_mixture_ml_consistency {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {M K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (p : (Fin τ → ℝ) → Fin M → ℝ) (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (Θ : Set (Fin τ → ℝ)) (hc : IsCompact Θ) (θ : Fin τ → ℝ) (hθ : θ∈Θ)
   (hp : ∀ t∈Θ,(∀ m,0 ≤ p t m) ∧ (∑ m,p t m)=1)
   (hg : ∀ t∈Θ,∀ m,Measurable (fun xy : (Fin K → ℝ) × ℝ => g m xy.2 xy.1 t))
   (hnonneg : ∀ t∈Θ,∀ m y x,0 ≤ g m y x t)
   (hnorm : ∀ t∈Θ,∀ m x,(∫⁻ y,ENNReal.ofReal (g m y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=conditionalModelLaw νX κ (mixtureFamily p g) θ)
   (hlog : ∀ t∈Θ,Integrable
     (fun ω => Real.log (mixtureFamily p g (Y 0 ω) (X 0 ω) t)) μ)
   (hpositiveModel : ∀ᵐ ω ∂μ,∀ t∈Θ,0 < mixtureFamily p g (Y 0 ω) (X 0 ω) t)
   (hM : ContinuousOn (expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g)) Θ)
   (hunique : ∀ t∈Θ,expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t ≤ 
     expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) θ ∧
     (expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t=
       expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) θ → t=θ))
   (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n,Measurable (that n))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → sampleLikelihood X Y (mixtureFamily p g) n ω t ≤ 
     sampleLikelihood X Y (mixtureFamily p g) n ω (that n ω))
   (Δ : ℕ → Ω → ℝ) (hΔ : ∀ n ω t,t∈Θ →
     |sampleLogLikelihood X Y (mixtureFamily p g) n ω t-
       expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t| ≤ Δ n ω)
   (hlim : CP μ Δ 0) : CP μ that θ := by
  have hgm : Measurable (fun xy : (Fin K → ℝ) × ℝ => mixtureFamily p g xy.2 xy.1 θ) := by
    unfold mixtureFamily
    apply Finset.measurable_sum
    intro m _
    exact (hg θ hθ m).const_mul (p θ m)
  have hp := iid_positive_at_parameter μ X Y hiid (mixtureFamily p g) θ hgm (by filter_upwards [hpositiveModel] with ω hω; exact hω θ hθ)
  exact product_mle_consistency_core μ X Y (mixtureFamily p g) Θ hc θ hθ hM hunique that hthat hp
    (fun n ω => hmax n ω θ hθ) Δ hΔ hlim


/-- With X uniform on (0,1) and independent standard normal noise, Y=10X²+W has CEF 10X² and BLP intercept −5/3 and slope 10.
Target P001-T46: Example 2.2.24 (BLP under Nonlinearity), the CEF formula, corrected; with the CEF and BLP of Example 2.2.23.
Location: Example 2.2.24: p. 82 (PDF p. 100), second sentence. Example 2.2.23: pp. 79–81 (PDF pp. 97–99). -/
theorem quadratic_cef_factor_ten {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X W : Ω → ℝ) (hX : Measurable X) (hW : Measurable W)
   (hi : IndepFun X W μ) (hx : μ.map X=uniformLaw 0 1) (hw : μ.map W=gaussianReal 0 1) :
   let Y := fun ω => 10*(X ω)^2+W ω
   IsCEF μ X Y (fun x => 10*x^2) ∧
   mean μ X=1/2 ∧ mean μ (fun ω => (X ω)^2)=1/3 ∧ mean μ (fun ω => (X ω)^3)=1/4 ∧
   var μ X=1/12 ∧ mean μ Y=10/3 ∧ covariance X Y μ=5/6 ∧
   blpSlope μ X Y=10 ∧ blpIntercept μ X Y= -5/3 := by
  exact uniform_quadratic_cef_and_blp μ X W hX hW hi hx hw


/-- "A unit selected with equal probabilities" (Definition 3.1.2 and
Example 3.1.3, pp. 93–94). The law is on unit indices, allowing repeated outcomes. -/
def uniformFiniteLaw (N : ℕ) (hN : 0 < N) : FiniteLaw N where
  weight _ := (N : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg N)
  total := by
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp [hn]

/-- Under an equal-probability draw of a unit, the finite-population PMF counts repeated responses, expectation is the population mean and variance is the average squared deviation; the example has mean 5 and variance 17/2.
Target P001-T50: Three misprinted displays, corrected: the variance in Example 3.1.3 (p. 94); the variance functional $T_{\mathrm{V}}(F)$ (p. 118, repeated in Example 3.3.5, p. 119); the last line of Example 3.3.4 (p. 119).
Location: (a) p. 94 (PDF p. 112), Example 3.1.3 (continued), second bullet. (b) p. 118 (PDF p. 136), display for $\mathrm{V}[X] = T_{\mathrm{V}}(F)$, last line; p. 119 (PDF p. 137), first display of Example 3.3.5. (c) p. 119 (PDF p. 137), Example 3.3.4, last line of the display. Definition 3.1.2 and Example 3.1.3: p. 93 (PDF p. 111). -/
theorem finite_population_example_moments :
  (∀ N : ℕ, ∀ hN : 0 < N, ∀ x : Fin N → ℝ,
    (∀ t : ℝ, fprob (uniformFiniteLaw N hN) (fun i => x i=t) =
      ((Finset.univ.filter (fun i => x i=t)).card : ℝ)/(N : ℝ)) ∧
    fmean (uniformFiniteLaw N hN) x = (∑ i, x i)/(N : ℝ) ∧
    fvar (uniformFiniteLaw N hN) x =
      (∑ i, (x i-(∑ j, x j)/(N : ℝ))^2)/(N : ℝ)) ∧
  fprob (uniformFiniteLaw 4 (by norm_num)) (fun i => (![3,4,3,10] : Fin 4 → ℝ) i=3)=1/2 ∧
  fprob (uniformFiniteLaw 4 (by norm_num)) (fun i => (![3,4,3,10] : Fin 4 → ℝ) i=4)=1/4 ∧
  fprob (uniformFiniteLaw 4 (by norm_num)) (fun i => (![3,4,3,10] : Fin 4 → ℝ) i=10)=1/4 ∧
  fmean (uniformFiniteLaw 4 (by norm_num)) ![3,4,3,10]=5 ∧
  fvar (uniformFiniteLaw 4 (by norm_num)) ![3,4,3,10]=17/2 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro N hN x
    have hm : fmean (uniformFiniteLaw N hN) x=(∑ i,x i)/(N : ℝ) := by
      unfold fmean
      change (∑ i, (N : ℝ)⁻¹*x i) = (∑ i, x i)/(N : ℝ)
      rw [← Finset.mul_sum]
      ring
    refine ⟨?_,hm,?_⟩
    · intro t
      simp [fprob,uniformFiniteLaw,← Finset.sum_filter,div_eq_mul_inv,mul_comm]
    · unfold fvar
      rw [hm]
      unfold fmean
      change (∑ i, (N : ℝ)⁻¹*(x i-(∑ j,x j)/(N : ℝ))^2) = _
      rw [← Finset.mul_sum]
      ring
  all_goals norm_num [fprob,fmean,fvar,uniformFiniteLaw,Fin.sum_univ_succ]

/-- The empirical-CDF Brownian bridge has covariance F(min(x,y))−F(x)F(y)
(corrected Theorem 3.3.6, p. 120; T57 empirical-process ingredient).
The tangent paths are uniformly continuous in the CDF semimetric and vanish
where the CDF is 0 or 1, so arbitrary nonseparable modifications are excluded. -/
def CDFTangent (F : ℝ → ℝ) : Set KolmogorovSpace :=
  {h | (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ,
    |F x-F y| < δ → |h x-h y| < ε) ∧
    (∀ x, F x=0 ∨ F x=1 → h x=0)}

/-- "B_F is the Gaussian limit of sqrt(n)(Fhat−F)" (T57 correction).
All finite linear combinations have the specified centered Gaussian laws. -/
def IsCDFBridge [MeasurableSpace KolmogorovSpace] (F : ℝ → ℝ) (ν : Measure KolmogorovSpace) : Prop :=
  ν (CDFTangent F)ᶜ=0 ∧ ∀ r : ℕ, ∀ x a : Fin r → ℝ,
    let v := ∑ j, ∑ k, a j*(min (F (x j)) (F (x k))-F (x j)*F (x k))*a k
    0 ≤ v ∧ ν.map (fun h => ∑ j, a j*h (x j)) =
      gaussianReal 0 ⟨max v 0, le_max_right _ _⟩


/-- A block bootstrap draws exactly l independent uniform cluster indices with replacement, retains every cluster’s m observations, and contains exactly lm observations.
Target P001-T64: Example 3.5.8 (Consequences of Clustering for the Sample Mean), the common-correlation condition, corrected to pairs $j \ne j'$; and step 1 of the block bootstrap, corrected to $l$ clusters.
Location: Example 3.5.8: pp. 140–141 (PDF pp. 158–159). Block bootstrap steps: p. 141 (PDF p. 159). Theorem 3.5.5: p. 137 (PDF p. 155). -/
theorem block_bootstrap_draw_count {Ω E : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {l m : ℕ} (hl : 0 < l)
  (X : Fin l → Fin m → E) (draw : Fin l → Ω → Fin l)
  (hmeas : ∀ i, Measurable (draw i)) (hind : iIndepFun draw μ)
  (hunif : ∀ i j, prob μ {ω | draw i ω=j}=1/(l : ℝ)) :
  Fintype.card (Fin l × Fin m)=l*m ∧
  (∀ ω i j, blockResample X (fun k => draw k ω) i j=X (draw i ω) j) ∧
  (∀ a : Fin l → Fin l,
    prob μ {ω | ∀ i, draw i ω=a i}=(1/(l : ℝ))^l) := by
  refine ⟨by simp,by intros; rfl,?_⟩
  intro a
  have hj := hind.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i => ({a i} : Set (Fin l))) (fun i hi => measurableSet_singleton (a i))
  have he : μ {ω | ∀ i, draw i ω=a i}=∏ i : Fin l, μ {ω | draw i ω=a i} := by
    calc
      μ {ω | ∀ i, draw i ω=a i}=μ (⋂ i ∈ Finset.univ, draw i ⁻¹' {a i}) := by
        congr 1
        ext ω
        simp
      _=∏ i : Fin l, μ {ω | draw i ω=a i} := hj
  unfold prob
  rw [he,ENNReal.toReal_prod]
  change (∏ i : Fin l, prob μ {ω | draw i ω=a i})=(1/(l : ℝ))^l
  simp only [hunif,Finset.prod_const,Finset.card_univ,Fintype.card_fin]


/-- For the paper’s independent uniform covariates, the piecewise CEF has APD in coordinate one equal to 1, covariate mean (1/2,1/2), and PDA equal to −1.
Target P001-T69: Example 4.3.8 (Differences between the Average Partial Derivative and the Partial Derivative at the Average), with the subscripts of the two displays corrected; and the label in the sentence after Definition 4.3.6.
Location: Example 4.3.8: p. 167 (PDF p. 185). Sentence after Definition 4.3.6: p. 166 (PDF p. 184). Definitions 4.3.6 and 4.3.7: pp. 166–167. -/
theorem apd_pda_different_correct_coordinate {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X1 X2 Y : Ω → ℝ)
  (hX1 : Measurable X1) (hX2 : Measurable X2) (hY : Integrable Y μ)
  (hind : IndepFun X1 X2 μ)
  (hlaw1 : μ.map X1=uniformLaw 0 1) (hlaw2 : μ.map X2=uniformLaw 0 1)
  (hcef : IsCEF μ (fun ω => (X1 ω,X2 ω)) Y (fun xy => apdExample xy.1 xy.2)) :
  (∀ x y : ℝ, deriv (fun t => apdExample t y) x=if y ≤ 4/5 then -1 else 9) ∧
  mean μ X1=1/2 ∧ mean μ X2=1/2 ∧
  mean μ (fun ω => deriv (fun t => apdExample t (X2 ω)) (X1 ω))=1 ∧
  deriv (fun t => apdExample t (mean μ X2)) (mean μ X1)= -1 ∧
  mean μ (fun ω => deriv (fun t => apdExample t (X2 ω)) (X1 ω)) ≠
    deriv (fun t => apdExample t (mean μ X2)) (mean μ X1) := by
  classical
  have hd (x y : ℝ) : deriv (fun t => apdExample t y) x=if y≤4/5 then -1 else 9 := by
    by_cases hy : y≤4/5
    · simp only [apdExample,if_pos hy]
      exact (hasDerivAt_neg x).deriv
    · simp only [apdExample,if_neg hy]
      simpa using ((hasDerivAt_id x).const_mul 9).deriv
  have hm1 : mean μ X1=1/2 := by
    have hh := integral_map (μ := μ) hX1.aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ => x) (μ.map X1) from
        measurable_id.aestronglyMeasurable)
    rw [hlaw1] at hh
    have hh' : (∫ x : ℝ,x ∂uniformLaw 0 1)=1/2 := by
      have hmoment := integral_pow_uniformLaw_zero_one 1
      norm_num at hmoment
      exact hmoment
    exact hh.symm.trans hh'
  have hm2 : mean μ X2=1/2 := by
    have hh := integral_map (μ := μ) hX2.aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ => x) (μ.map X2) from
        measurable_id.aestronglyMeasurable)
    rw [hlaw2] at hh
    have hh' : (∫ x : ℝ,x ∂uniformLaw 0 1)=1/2 := by
      have hmoment := integral_pow_uniformLaw_zero_one 1
      norm_num at hmoment
      exact hmoment
    exact hh.symm.trans hh'
  have hp : prob μ {ω | X2 ω≤4/5}=(4/5:ℝ) := by
    have hs : Set.Iic (4/5:ℝ) ∩ Set.Icc (0:ℝ) 1=Set.Icc 0 (4/5:ℝ) := by
      ext x
      simp only [Set.mem_inter_iff,Set.mem_Iic,Set.mem_Icc]
      constructor
      · rintro ⟨hx,h0,h1⟩
        exact ⟨h0,hx⟩
      · rintro ⟨h0,hx⟩
        exact ⟨hx,h0,by linarith⟩
    change (μ (X2 ⁻¹' Set.Iic (4/5:ℝ))).toReal=4/5
    rw [← Measure.map_apply hX2 measurableSet_Iic,hlaw2,uniformLaw_zero_one_eq_restrict,
      Measure.restrict_apply measurableSet_Iic,hs,Real.volume_Icc]
    norm_num
  have hA : MeasurableSet {ω | X2 ω≤4/5} := hX2 measurableSet_Iic
  have hpc : prob μ {ω | X2 ω≤4/5}ᶜ=(1/5:ℝ) := by
    rw [show prob μ {ω | X2 ω≤4/5}ᶜ=1-prob μ {ω | X2 ω≤4/5} from
      probReal_compl_eq_one_sub hA,hp]
    norm_num
  have hapd : mean μ (fun ω => deriv (fun t => apdExample t (X2 ω)) (X1 ω))=1 := by
    simp_rw [hd]
    change (∫ ω, {ω | X2 ω≤4/5}.piecewise (fun _ => (-1:ℝ)) (fun _ => (9:ℝ)) ω ∂μ)=1
    rw [integral_piecewise hA (integrable_const _).integrableOn
      (integrable_const _).integrableOn]
    simp only [integral_const,measureReal_def,Measure.restrict_apply_univ,smul_eq_mul]
    change prob μ {ω | X2 ω≤4/5}*(-1)+prob μ {ω | X2 ω≤4/5}ᶜ*9=1
    rw [hp,hpc]
    norm_num
  refine ⟨hd,hm1,hm2,hapd,?_,?_⟩
  · rw [hd,hm2]
    norm_num
  · rw [hapd,hd,hm2]
    norm_num

/-- A normalized conditional binary response law gives E[R|X=x]=Pr[R=1|X=x] in [0,1], and impossible propensity values are exactly those above one or below zero.
Target P001-T82: Section 6.2.4, the range of the response propensity and the description of impossible estimates, corrected.
Location: p. 225 (PDF p. 243), Section 6.2.4, first paragraph, last sentence on the page. -/
theorem propensity_range_correction {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (R : Ω → Bool)
  (hX : Measurable X) (hR : Measurable R) (κ : E → Measure Bool)
  (hκ : ∀ x, IsProbabilityMeasure (κ x))
  (hkm : ∀ B : Set Bool, MeasurableSet B → Measurable (fun x => κ x B))
  (hcond : ∀ A : Set E, MeasurableSet A → ∀ B : Set Bool, MeasurableSet B →
    μ {ω | X ω ∈ A ∧ R ω ∈ B} = ∫⁻ x in A, κ x B ∂(μ.map X)) :
  (∀ x, mean (κ x) (fun r => if r then (1 : ℝ) else 0)=kernelPropensity κ x ∧
    kernelPropensity κ x ∈ Set.Icc (0 : ℝ) 1) ∧
  IsCEF μ X (fun ω => if R ω then (1 : ℝ) else 0) (kernelPropensity κ) ∧
  (∀ q : ℝ, q ∉ Set.Icc (0 : ℝ) 1 ↔ 1 < q ∨ q < 0) := by
  classical
  have hrange := conditional_kernel_propensity_range κ hκ
  have hqm : Measurable (kernelPropensity κ) := by
    exact (hkm {true} (measurableSet_singleton true)).ennreal_toReal
  have hnum : (fun r : Bool => if r then (1 : ℝ) else 0)=
      ({true} : Set Bool).indicator (fun _ => (1 : ℝ)) := by
    funext r
    cases r <;> simp [Set.indicator]
  have hRm : Measurable (fun ω => if R ω then (1 : ℝ) else 0) := by
    change Measurable ((fun r : Bool => if r then (1 : ℝ) else 0) ∘ R)
    rw [hnum]
    exact (measurable_const.indicator (measurableSet_singleton true)).comp hR
  have hRi : Integrable (fun ω => if R ω then (1 : ℝ) else 0) μ := by
    apply Integrable.of_bound hRm.aestronglyMeasurable 1
    exact ae_of_all _ (fun ω => by cases R ω <;> norm_num)
  have hqi : Integrable (kernelPropensity κ) (μ.map X) := by
    apply Integrable.of_bound hqm.aestronglyMeasurable 1
    exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hrange x).1]; exact (hrange x).2)
  have hqXi : Integrable ((kernelPropensity κ) ∘ X) μ := by
    apply Integrable.of_bound (hqm.comp hX).aestronglyMeasurable 1
    exact ae_of_all _ (fun ω => by change |kernelPropensity κ (X ω)|≤1; rw [abs_of_nonneg (hrange (X ω)).1]; exact (hrange (X ω)).2)
  refine ⟨?_,⟨hqm,hRi,hqXi,?_⟩,?_⟩
  · intro x
    letI := hκ x
    refine ⟨?_,hrange x⟩
    unfold mean
    rw [hnum]
    simpa [kernelPropensity,prob,Measure.real] using
      integral_indicator_const (μ := κ x) (1 : ℝ) (measurableSet_singleton true)
  · intro A hA
    have hpre : MeasurableSet (R ⁻¹' ({true} : Set Bool)) := (measurableSet_singleton true).preimage hR
    have hleft : (∫ ω in X ⁻¹' A, (if R ω then (1 : ℝ) else 0) ∂μ)=
        (μ {ω | X ω∈A ∧ R ω∈({true} : Set Bool)}).toReal := by
      have he : (fun ω => if R ω then (1 : ℝ) else 0)=
          (R ⁻¹' ({true} : Set Bool)).indicator (fun _ => (1 : ℝ)) := by
        funext ω
        cases h : R ω <;> simp [Set.indicator,h]
      rw [he]
      have hset : R ⁻¹' ({true} : Set Bool) ∩ X ⁻¹' A={ω | X ω∈A ∧ R ω∈({true} : Set Bool)} := by
        ext ω; simp [and_comm]
      simpa only [measureReal_def,Measure.restrict_apply hpre,smul_eq_mul,mul_one,hset] using
        integral_indicator_const (μ := μ.restrict (X ⁻¹' A)) (1 : ℝ) hpre
    have hright : (∫ x in A,kernelPropensity κ x ∂(μ.map X))=
        (∫⁻ x in A,κ x {true} ∂(μ.map X)).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ (fun x => (hrange x).1)) hqi.integrableOn.aestronglyMeasurable]
      congr 1
      apply lintegral_congr
      intro x
      letI := hκ x
      exact ENNReal.ofReal_toReal (measure_ne_top (κ x) {true})
    rw [hleft,←setIntegral_map hA hqm.aestronglyMeasurable hX.aemeasurable,hright]
    exact congrArg ENNReal.toReal (hcond A hA {true} (measurableSet_singleton true))
  · intro q
    simp only [Set.mem_Icc,not_and_or,not_le,or_comm]

/-- The actual twelve-unit grouped logistic maximum-likelihood fit yields IPW 3/7 and post-stratification 5/12, so the claimed equality fails.
Target P001-T84: Section 6.2.5, the sentence 'In the case where there is a discrete and finite number of values for $\mathbf{X}_i$, the IPW estimator is logically equivalent to the plug-in estimator from Section 6.2.1', as printed.
Location: p. 228 (PDF p. 246), first paragraph. Definition 6.2.7: p. 227 (PDF p. 245). Section 6.2.1 plug-in estimator: p. 219 (PDF p. 237). Section 6.2.4: pp. 225–226 (PDF pp. 243–244). -/
theorem missing_ipw_not_poststratified : (∀ a b : ℝ,
    groupedLogitLikelihood missingCellSize missingCellResponse a b ≤ 
      groupedLogitLikelihood missingCellSize missingCellResponse (Real.log (7/5)) 0 ∧
    (groupedLogitLikelihood missingCellSize missingCellResponse a b=
      groupedLogitLikelihood missingCellSize missingCellResponse (Real.log (7/5)) 0 ↔
      a=Real.log (7/5) ∧ b=0)) ∧
   (∀ j : Fin 3,0 < missingCellResponse j ∧ missingCellResponse j < missingCellSize j ∧
      logitProbability (Real.log (7/5)) 0 ((![-1,0,1] : Fin 3 → ℝ) j)=7/12) ∧
   (∑ j,missingCellOutcomeSum j/
      logitProbability (Real.log (7/5)) 0 ((![-1,0,1] : Fin 3 → ℝ) j))/12=3/7 ∧
   (∑ j,missingCellSize j*missingCellOutcomeSum j/missingCellResponse j)/12=5/12 ∧
   (3/7 : ℝ)≠5/12 := by
  exact missing_ipw_logit_ml_counterexample


/-- For iid data from a true normalized conditional model, its actual product-likelihood ML estimator is consistent under compactness, population uniqueness and uniform expected-log convergence.
Target P001-T129: Theorem 5.2.6 (Consistency of the Maximum Likelihood Estimator) and the lemma in its proof sketch.
Location: Theorem 5.2.6: p. 193 (PDF p. 211). Proof sketch: pp. 193–194 (PDF pp. 211–212). -/
theorem ml_consistency_explicit_uniform_regularities {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (Θ : Set (Fin τ → ℝ))
   (hc : IsCompact Θ) (θ : Fin τ → ℝ) (hθ : θ∈Θ)
   (hg : ∀ t∈Θ,Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
   (hnonneg : ∀ t∈Θ,∀ y x,0 ≤ g y x t)
   (hnorm : ∀ t∈Θ,∀ x,(∫⁻ y,ENNReal.ofReal (g y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=conditionalModelLaw νX κ g θ)
   (hlog : ∀ t∈Θ,Integrable (fun ω => Real.log (g (Y 0 ω) (X 0 ω) t)) μ)
   (hpos : ∀ᵐ ω ∂μ,∀ t∈Θ,0 < g (Y 0 ω) (X 0 ω) t)
   (hM : ContinuousOn (expectedLogLikelihood μ (X 0) (Y 0) g) Θ)
   (hunique : ∀ t∈Θ,expectedLogLikelihood μ (X 0) (Y 0) g t ≤ expectedLogLikelihood μ (X 0) (Y 0) g θ ∧
     (expectedLogLikelihood μ (X 0) (Y 0) g t=expectedLogLikelihood μ (X 0) (Y 0) g θ → t=θ))
   (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n,Measurable (that n))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → sampleLikelihood X Y g n ω t ≤ sampleLikelihood X Y g n ω (that n ω))
   (Δ : ℕ → Ω → ℝ) (hΔ : ∀ n ω t,t∈Θ →
     |sampleLogLikelihood X Y g n ω t-expectedLogLikelihood μ (X 0) (Y 0) g t| ≤ Δ n ω)
   (hlim : CP μ Δ 0) : CP μ that θ := by
  have hgm := hg θ hθ
  have hp := iid_positive_at_parameter μ X Y hiid g θ hgm (by filter_upwards [hpos] with ω hω; exact hω θ hθ)
  exact product_mle_consistency_core μ X Y g Θ hc θ hθ hM hunique that hthat hp
    (fun n ω => hmax n ω θ hθ) Δ hΔ hlim

/-- The law of n iid observations from the conditional model (Definitions
3.1.1 and 5.1.1, pp. 92 and 178–179). -/
def iidObservationLaw {E : Type*} [MeasurableSpace E] (ν : Measure E) (n : ℕ) :
    Measure (Fin n → E) := Measure.pi (fun _ : Fin n => ν)

/-- Convergence in probability in the actual n-observation experiments
(Definition 3.2.6, p. 99); this avoids an unrelated ambient sampling measure. -/
def SampleCP {E : Type*} [MeasurableSpace E] {τ : ℕ}
    (ν : Measure E) (T : (n : ℕ) → (Fin n → E) → Fin τ → ℝ) (θ : Fin τ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun n => prob (iidObservationLaw ν n) {s | ε ≤ dist (T n s) θ}) atTop (nhds 0)

/-- Weak convergence under a sequence of iid experiments, including local
alternatives θ+h/sqrt(n) (T12 regular information-bound conditions). -/
def SampleWeakLimit {E : Type*} [MeasurableSpace E] {τ : ℕ}
    (ν : ℕ → Measure E) (Z : (n : ℕ) → (Fin n → E) → Fin τ → ℝ)
    (γ : Measure (Fin τ → ℝ)) : Prop :=
  ∀ f : (Fin τ → ℝ) → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Tendsto (fun n => mean (iidObservationLaw (ν n) n) (fun s => f (Z n s)))
      atTop (nhds (mean γ f))

/-- A regular asymptotically linear estimator has an L² influence ψ at θ
and the same centered limit under every fixed root-n local alternative
(the regularity qualification in the T12 correction, p. 199).
The parameter law is a function of the full independent parameter coordinates. -/
def RegularAL {E : Type*} [MeasurableSpace E] {τ : ℕ}
    (ν : (Fin τ → ℝ) → Measure E) (θ : Fin τ → ℝ)
    (T : (n : ℕ) → (Fin n → E) → Fin τ → ℝ) (ψ : E → Fin τ → ℝ) : Prop :=
  (∀ n, Measurable (T n)) ∧ Measurable ψ ∧
  (∀ j, MemLp (fun z => ψ z j) 2 (ν θ)) ∧
  (∀ j, mean (ν θ) (fun z => ψ z j)=0) ∧
  (∀ ε : ℝ, 0 < ε → Tendsto (fun n => prob (iidObservationLaw (ν θ) n)
    {s | ε ≤ dist (Real.sqrt n • (T n s-θ))
      ((Real.sqrt n)⁻¹ • (fun j => ∑ i, ψ (s i) j))}) atTop (nhds 0)) ∧
  (∀ h : Fin τ → ℝ, SampleWeakLimit (fun n => ν (θ+(Real.sqrt n)⁻¹ • h))
    (fun n s => Real.sqrt n • (T n s-(θ+(Real.sqrt n)⁻¹ • h)))
    (normalVectorLaw (covarianceMatrix (ν θ) ψ)))

/-- Real-integral quadratic-mean remainder condition used together with the
separately stated local density normalization, measurability and
square-integrable-score assumptions. This predicate alone does not assert
integrability of the residual or quadratic-mean differentiability. -/
def QuadraticMeanModel {K τ : ℕ} (νX : Measure (Fin K → ℝ)) (κ : Measure ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (θ : Fin τ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : Fin τ → ℝ,
    dist t θ < δ →
    (∫ xy : (Fin K → ℝ) × ℝ,
      (Real.sqrt (g xy.2 xy.1 t)-Real.sqrt (g xy.2 xy.1 θ)-
       (∑ j, (t j-θ j)*modelScore g xy.2 xy.1 θ j)*
         Real.sqrt (g xy.2 xy.1 θ)/2)^2 ∂(νX.prod κ)) ≤ ε*(dist t θ)^2


theorem conditional_model_probability {K τ : ℕ}
    (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (θ : Fin τ → ℝ)
    (hg : Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 θ))
    (hnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (g y x θ) ∂κ)=1) :
    IsProbabilityMeasure (conditionalModelLaw νX κ g θ) := by
  constructor
  simp only [conditionalModelLaw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [lintegral_prod _ hg.ennreal_ofReal.aemeasurable]
  simp [hnorm]

theorem sample_probability_limit_unique {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] {F : Type*} [MetricSpace F]
    (T : (n : ℕ) → (Fin n → E) → F) (a b : F)
    (ha : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => prob (iidObservationLaw ν n)
      {s | ε ≤ dist (T n s) a}) atTop (nhds 0))
    (hb : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => prob (iidObservationLaw ν n)
      {s | ε ≤ dist (T n s) b}) atTop (nhds 0)) : a=b := by
  by_contra hab
  have hd : 0 < dist a b := dist_pos.mpr hab
  have hδ : 0 < dist a b/3 := by positivity
  have hlim : Tendsto (fun n =>
      prob (iidObservationLaw ν n) {s | dist a b/3 ≤ dist (T n s) a}+
      prob (iidObservationLaw ν n) {s | dist a b/3 ≤ dist (T n s) b}) atTop (nhds 0) := by
    simpa only [zero_add] using (ha _ hδ).add (hb _ hδ)
  have hbound (n : ℕ) : (1 : ℝ) ≤
      prob (iidObservationLaw ν n) {s | dist a b/3 ≤ dist (T n s) a}+
      prob (iidObservationLaw ν n) {s | dist a b/3 ≤ dist (T n s) b} := by
    have hs : (Set.univ : Set (Fin n → E)) ⊆
        {s | dist a b/3 ≤ dist (T n s) a} ∪ {s | dist a b/3 ≤ dist (T n s) b} := by
      intro s _
      by_contra h
      simp only [Set.mem_union,Set.mem_setOf_eq,not_or,not_le] at h
      have ht : dist a b ≤ dist (T n s) a+dist (T n s) b := by
        simpa only [dist_comm a (T n s)] using dist_triangle a (T n s) b
      linarith
    haveI : IsProbabilityMeasure (iidObservationLaw ν n) := by
      dsimp [iidObservationLaw]
      infer_instance
    have h := (measureReal_mono (μ := iidObservationLaw ν n) hs).trans (measureReal_union_le _ _)
    simpa [Measure.real,AronowAudit.P001.prob] using h
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hbound)
  norm_num at hbad

/-- Distinct full mixture parameters that differ only in a zero-weight component have the same conditional law, every iid sample law and expected log likelihood, so no estimator is consistent at both.
Target P001-T12: Section 5.2.5, the 'any subset' sentence, corrected: consistency and efficiency of the mixture ML estimator under identification of the full parameter vector.
Location: p. 199 (PDF p. 217), second paragraph. -/
theorem zero_weight_component_irrelevant {M K τ : ℕ}
  (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
  (p : (Fin τ → ℝ) → Fin M → ℝ)
  (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
  (θ θ' : Fin τ → ℝ) (hθ : θ ≠ θ') (j : Fin M)
  (hp : p θ=p θ') (hpzero : p θ j=0)
  (hweight : (∀ k, 0 ≤ p θ k) ∧ (∑ k, p θ k)=1)
  (heq : ∀ k, k ≠ j → ∀ y x, g k y x θ=g k y x θ')
  (hg : ∀ t ∈ ({θ,θ'} : Set (Fin τ → ℝ)), ∀ k,
    Measurable (fun xy : (Fin K → ℝ) × ℝ => g k xy.2 xy.1 t))
  (hnonneg : ∀ t ∈ ({θ,θ'} : Set (Fin τ → ℝ)), ∀ k y x, 0 ≤ g k y x t)
  (hnorm : ∀ t ∈ ({θ,θ'} : Set (Fin τ → ℝ)), ∀ k x,
    (∫⁻ y, ENNReal.ofReal (g k y x t) ∂κ)=1)
  (hlog : Integrable (fun xy : (Fin K → ℝ) × ℝ =>
    Real.log (mixtureFamily p g xy.2 xy.1 θ))
    (conditionalModelLaw νX κ (mixtureFamily p g) θ)) :
  (∀ y x, mixtureFamily p g y x θ=mixtureFamily p g y x θ') ∧
  conditionalModelLaw νX κ (mixtureFamily p g) θ=
    conditionalModelLaw νX κ (mixtureFamily p g) θ' ∧
  (∀ n, iidObservationLaw (conditionalModelLaw νX κ (mixtureFamily p g) θ) n=
    iidObservationLaw (conditionalModelLaw νX κ (mixtureFamily p g) θ') n) ∧
  mean (conditionalModelLaw νX κ (mixtureFamily p g) θ)
    (fun xy => Real.log (mixtureFamily p g xy.2 xy.1 θ)) =
  mean (conditionalModelLaw νX κ (mixtureFamily p g) θ')
    (fun xy => Real.log (mixtureFamily p g xy.2 xy.1 θ')) ∧
  (∀ T : (n : ℕ) → (Fin n → (Fin K → ℝ) × ℝ) → Fin τ → ℝ,
    (∀ n, Measurable (T n)) →
    ¬ (SampleCP (conditionalModelLaw νX κ (mixtureFamily p g) θ) T θ ∧
       SampleCP (conditionalModelLaw νX κ (mixtureFamily p g) θ') T θ')) := by
  classical
  have he (y : ℝ) (x : Fin K → ℝ) : mixtureFamily p g y x θ=mixtureFamily p g y x θ' := by
    unfold mixtureFamily
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k=j
    · subst k
      simp [← hp,hpzero]
    · rw [heq k hk, hp]
  have hlaw : conditionalModelLaw νX κ (mixtureFamily p g) θ =
      conditionalModelLaw νX κ (mixtureFamily p g) θ' := by
    unfold conditionalModelLaw
    congr 1
    funext xy
    rw [he]
  have hgm : Measurable (fun xy : (Fin K → ℝ) × ℝ => mixtureFamily p g xy.2 xy.1 θ) := by
    unfold mixtureFamily
    exact Finset.measurable_sum _ (fun k _ => (hg θ (by simp) k).const_mul _)
  have hnormmix (x : Fin K → ℝ) :
      (∫⁻ y, ENNReal.ofReal (mixtureFamily p g y x θ) ∂κ)=1 := by
    have hnn (y : ℝ) (k : Fin M) : 0 ≤ p θ k*g k y x θ :=
      mul_nonneg (hweight.1 k) (hnonneg θ (by simp) k y x)
    simp_rw [mixtureFamily, ENNReal.ofReal_sum_of_nonneg (fun k _ => hnn _ k),
      ENNReal.ofReal_mul (hweight.1 _)]
    have hmeas (k : Fin M) : Measurable (fun y : ℝ => ENNReal.ofReal (g k y x θ)) :=
      ((hg θ (by simp) k).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
    rw [lintegral_finsetSum Finset.univ
      (f := fun k (y : ℝ) => ENNReal.ofReal (p θ k)*ENNReal.ofReal (g k y x θ))
      (fun k _ => (hmeas k).const_mul _)]
    simp_rw [lintegral_const_mul _ (hmeas _), hnorm θ (by simp), mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hweight.1 k), hweight.2]
    norm_num
  haveI := conditional_model_probability νX κ (mixtureFamily p g) θ hgm hnormmix
  refine ⟨he,hlaw,?_,?_,?_⟩
  · intro n
    rw [hlaw]
  · unfold mean
    rw [hlaw]
    congr 1
    funext xy
    dsimp only
    rw [he]
  · intro T _ hboth
    have hother : SampleCP (conditionalModelLaw νX κ (mixtureFamily p g) θ) T θ' := by
      rw [hlaw]
      exact hboth.2
    exact hθ (sample_probability_limit_unique _ T θ θ' hboth.1 hother)


/-- For each fixed sample on the good Gram event, a uniformly ε-close polynomial approximation gives population L² error at most ε(1+c^(−1/2)) plus the Euclidean sampling-noise coefficient norm.
Target P001-T6: Definition 4.3.9 (Polynomial Least Squares Sieve Estimator) and the consistency claim after it, corrected with a sufficient degree-growth condition.
Location: pp. 168–169 (PDF pp. 186–187). -/
theorem sieve_finite_l2_approximation_error_bound {n K : ℕ} (hn : 0 < n)
  (ν : Measure ℝ) [IsProbabilityMeasure ν] (a b : ℝ) (hab : a < b)
  (hsupp : ∀ᵐ x ∂ν, x ∈ Set.Icc a b)
  (p : Fin K → Polynomial ℝ)
  (horth : ∀ j k, mean ν (fun x => (p j).eval x*(p k).eval x)=if j=k then 1 else 0)
  (m : ℝ → ℝ) (hm : ContinuousOn m (Set.Icc a b))
  (x u : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Icc a b)
  (P : Matrix (Fin n) (Fin K) ℝ) (hP : ∀ i k, P i k=(p k).eval (x i))
  (bApprox : Fin K → ℝ) (ε c : ℝ) (hε : 0 ≤ ε) (hc : 0 < c)
  (happrox : ∀ t ∈ Set.Icc a b, |m t-∑ k, bApprox k*(p k).eval t| ≤ ε)
  (hgram : ∀ v : Fin K → ℝ, c*(∑ k, (v k)^2) ≤ (∑ i, (P.mulVec v i)^2)/(n : ℝ)) :
  Real.sqrt (∫ t, ((∑ k, olsCoef P (fun i => m (x i)+u i) k*(p k).eval t)-m t)^2 ∂ν) ≤
    ε*(1+(Real.sqrt c)⁻¹)+Real.sqrt (∑ k, (olsCoef P u k)^2) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  let r : Fin n → ℝ := fun i => m (x i)-P.mulVec bApprox i
  have hunit := gram_unit_of_lower_bound hn P c hc hgram
  have hcoeff : olsCoef P (fun i => m (x i)+u i) = bApprox+olsCoef P r+olsCoef P u := by
    have he : (fun i => m (x i)+u i) = P.mulVec bApprox+r+u := by
      funext i
      dsimp [r]
      ring
    rw [he]
    exact sieve_finite_coefficient_decomposition P hunit bApprox r u
  let fr : ℝ → ℝ := fun t => ∑ k,olsCoef P r k*(p k).eval t
  let fu : ℝ → ℝ := fun t => ∑ k,olsCoef P u k*(p k).eval t
  let R : ℝ → ℝ := fun t => (∑ k,bApprox k*(p k).eval t)-m t
  have hp := orthonormal_polynomial_lp ν p horth
  have hfr : MemLp fr 2 ν := memLp_finsetSum Finset.univ (fun k _ => (hp k).const_mul _)
  have hfu : MemLp fu 2 ν := memLp_finsetSum Finset.univ (fun k _ => (hp k).const_mul _)
  have hRae : ∀ᵐ t ∂ν, |R t| ≤ ε := by
    filter_upwards [hsupp] with t ht
    dsimp [R]
    rw [abs_sub_comm]
    exact happrox t ht
  have hRasm : AEStronglyMeasurable R ν := by
    have hbcont : Continuous (fun t => ∑ k,bApprox k*(p k).eval t) := by fun_prop
    have hRc : ContinuousOn R (Set.Icc a b) := hbcont.continuousOn.sub hm
    have ha : AEStronglyMeasurable R (ν.restrict (Set.Icc a b)) :=
      hRc.aestronglyMeasurable measurableSet_Icc
    rwa [Measure.restrict_eq_self_of_ae_mem hsupp] at ha
  have hR2 : MemLp R 2 ν := MemLp.of_bound hRasm ε (by simpa only [Real.norm_eq_abs] using hRae)
  have hRnorm : Real.sqrt (∫ t,(R t)^2 ∂ν) ≤ ε := by
    have hi : (∫ t,(R t)^2 ∂ν) ≤ ε^2 := by
      have ha : ∀ᵐ t ∂ν,(R t)^2 ≤ ε^2 := by
        filter_upwards [hRae] with t ht
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (R t)) hε).mpr ht
      simpa using integral_mono_ae hR2.integrable_sq (integrable_const (ε^2)) ha
    simpa only [Real.sqrt_sq hε] using Real.sqrt_le_sqrt hi
  have hrbound (i : Fin n) : |r i| ≤ ε := by
    have hh := happrox (x i) (hx i)
    simpa only [r,Matrix.mulVec,dotProduct,hP,mul_comm] using hh
  have hrsum : (∑ i,(r i)^2) ≤ (n:ℝ)*ε^2 := by
    have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin n))) =>
      (show (r i)^2 ≤ ε^2 by simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (r i)) hε).mpr (hrbound i)))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have hrav : (∑ i,(r i)^2)/(n:ℝ) ≤ ε^2 := (div_le_iff₀ hnR).mpr (by nlinarith [hrsum])
  have hcoef := sieve_finite_approximation_coefficient_bound hn P r c hc hgram
  have hb : c*(∑ k,(olsCoef P r k)^2) ≤ ε^2 := hcoef.1.trans (hcoef.2.trans hrav)
  have hbrnorm : Real.sqrt (∑ k,(olsCoef P r k)^2) ≤ ε*(Real.sqrt c)⁻¹ := by
    have ha : (∑ k,(olsCoef P r k)^2) ≤ ε^2/c := (le_div_iff₀ hc).mpr (by nlinarith [hb])
    calc
      Real.sqrt (∑ k,(olsCoef P r k)^2) ≤ Real.sqrt (ε^2/c) := Real.sqrt_le_sqrt ha
      _ = ε*(Real.sqrt c)⁻¹ := by rw [Real.sqrt_div (sq_nonneg ε),Real.sqrt_sq hε,div_eq_mul_inv]
  have he (t : ℝ) :
      (∑ k,olsCoef P (fun i => m (x i)+u i) k*(p k).eval t)-m t=(fr t+fu t)+R t := by
    rw [hcoeff]
    simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
    dsimp [fr,fu,R]
    ring
  simp_rw [he]
  calc
    Real.sqrt (∫ t,((fr t+fu t)+R t)^2 ∂ν) ≤
        Real.sqrt (∫ t,(fr t+fu t)^2 ∂ν)+Real.sqrt (∫ t,(R t)^2 ∂ν) :=
      sqrt_integral_sq_add_le (hfr.add hfu) hR2
    _ ≤ (Real.sqrt (∫ t,(fr t)^2 ∂ν)+Real.sqrt (∫ t,(fu t)^2 ∂ν))+ε :=
      add_le_add (sqrt_integral_sq_add_le hfr hfu) hRnorm
    _ = (Real.sqrt (∑ k,(olsCoef P r k)^2)+Real.sqrt (∑ k,(olsCoef P u k)^2))+ε := by
      dsimp [fr,fu]
      rw [orthonormal_polynomial_integral_sq ν p horth,orthonormal_polynomial_integral_sq ν p horth]
    _ ≤ ε*(1+(Real.sqrt c)⁻¹)+Real.sqrt (∑ k,(olsCoef P u k)^2) := by
      nlinarith [hbrnorm]

/-- In a bootstrap resample, aggregate a donor's reuse count over copies of
each original observation (T14 finite two-bootstrap-draw identity). -/
def bootstrapOriginalReuse {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (a : Fin n → Fin n) (j : Fin n) : ℝ :=
  ∑ i, if a i=j then donorReuseWeight (p ∘ a) (r ∘ a) i else 0


/-- A finite PMF induces the actual atomic probability law (Definition 1.2.5,
p. 18); used for iid repetitions of the twelve-atom placebo design. -/
def finiteLawMeasure {n : ℕ} (P : FiniteLaw n) : Measure (Fin n) :=
  ∑ i, ENNReal.ofReal (P.weight i) • Measure.dirac i

/-- The ordinary nested-regression F statistic for the exact placebo design
(Section 7.2.8, p. 270; T17). -/
def placeboSampleF {Ω : Type*} (Z : ℕ → Ω → Fin 12) (n : ℕ) (ω : Ω) : ℝ :=
  placeboFStatistic (fun i : Fin n => fun _ : Fin 1 => placeboX (Z i.val ω))
    (fun i : Fin n => fun _ : Fin 1 => placeboW (Z i.val ω))
    (fun i : Fin n => placeboD (Z i.val ω))

/-- The heteroskedasticity-robust Wald statistic for the added W coefficient
(Section 7.2.8, p. 270; T17). -/
def placeboSampleWald {Ω : Type*} (Z : ℕ → Ω → Fin 12) (n : ℕ) (ω : Ω) : ℝ :=
  let P : Matrix (Fin n) (Fin 3) ℝ := fun i =>
    ![1,placeboX (Z i.val ω),placeboW (Z i.val ω)]
  let D : Fin n → ℝ := fun i => placeboD (Z i.val ω)
  let β := olsCoef P D
  (β 2)^2/(robustCov P (D-P.mulVec β) 2 2)


/-- For each positive n, the bounded-variation linear functional of the actual empirical law is the sample mean of a(X), and its centered root-n statistic has variance Var[a(X)].
Target P001-T57: Theorem 3.3.6 (Asymptotic Normality of Plug-In Estimators), corrected with the non-degeneracy condition.
Location: p. 120 (PDF p. 138), Theorem 3.3.6 and footnote 31; Definition 3.2.28, p. 112 (PDF p. 130). -/
theorem bounded_linear_functional_empirical_identity {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X)
  (a : ℝ → ℝ) (ha : Measurable a) (hbound : ∃ C : ℝ, ∀ x, |a x| ≤ C)
  (hvariation : BoundedVariationOn a Set.univ) (n : ℕ) (hn : 0 < n) :
  (∀ ω, mean (empirical X n ω) a=sampleMean (fun i ω => a (X i ω)) n ω ∧
    Real.sqrt n*(mean (empirical X n ω) a-mean μ (fun ω => a (X 0 ω))) =
      (∑ i ∈ Finset.range n, (a (X i ω)-mean μ (fun ω => a (X 0 ω))))/Real.sqrt n) ∧
  var μ (fun ω => Real.sqrt n*(mean (empirical X n ω) a-
    mean μ (fun ω => a (X 0 ω))))=var μ (fun ω => a (X 0 ω)) := by
  let A : ℕ → Ω → ℝ := fun i ω => a (X i ω)
  have hA : IID μ A := by
    refine ⟨(fun i => ha.comp (hiid.1 i)),?_,?_⟩
    · exact hiid.2.1.comp (fun _ => a) (fun _ => ha)
    · intro i; exact (hiid.2.2 i).comp ha
  rcases hbound with ⟨C,hC⟩
  have hA2 : MemLp (A 0) 2 μ := by
    apply MemLp.of_bound (hA.1 0).aestronglyMeasurable C
    exact ae_of_all μ (fun ω => by simpa only [A,Real.norm_eq_abs] using hC (X 0 ω))
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
  have hsq : Real.sqrt (n : ℝ)^2=(n : ℝ) := Real.sq_sqrt (le_of_lt hnR)
  have he (ω : Ω) : mean (empirical X n ω) a=sampleMean A n ω := by
    unfold mean empirical
    rw [integral_smul_measure,integral_finsetSum_measure (fun i hi => integrable_dirac (by simp))]
    simp [sampleMean,A,ENNReal.toReal_inv,div_eq_mul_inv,mul_comm]
  constructor
  · intro ω
    refine ⟨he ω,?_⟩
    rw [he ω]
    change Real.sqrt n*(sampleMean A n ω-mean μ (A 0))=
      (∑ i ∈ Finset.range n,(A i ω-mean μ (A 0)))/Real.sqrt n
    unfold sampleMean
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    field_simp [hn0,hsn]
    ring_nf
    rw [hsq]
    ring
  · have hefun : (fun ω => Real.sqrt n*(mean (empirical X n ω) a-
        mean μ (fun ω => a (X 0 ω))))=
        (fun ω => Real.sqrt n*(sampleMean A n ω-mean μ (A 0))) := by
      funext ω; rw [he ω]
    rw [hefun]
    unfold var
    rw [variance_const_mul,Real.sq_sqrt (le_of_lt hnR),
      variance_sub_const (sample_mean_memLp μ A hA hA2 n).aestronglyMeasurable]
    change (n : ℝ)*var μ (sampleMean A n)=var μ (A 0)
    rw [(iid_sample_mean_finite_moments μ A hA hA2 n hn).2]
    field_simp [hn0]


/-- Covariance-comparison predicate used for the printed mixture claim
(Section 5.2.5, p. 199; T121). It requires a Gaussian root-n limit under `μ`
whose covariance is a lower bound for the influence covariances of all
`RegularAL ν θ` competitors. It does not require the candidate estimator to
be regular, require a regular competitor to exist, or connect its sampling
law under `μ` to the experiment `ν`. Those properties require separate premises. -/
def EfficientInModel {E : Type*} [MeasurableSpace E] {Ω : Type*} [MeasurableSpace Ω]
    {τ : ℕ} (μ : Measure Ω) (that : ℕ → Ω → Fin τ → ℝ)
    (ν : (Fin τ → ℝ) → Measure E) (θ : Fin τ → ℝ) : Prop :=
  ∃ S : Matrix (Fin τ) (Fin τ) ℝ, S.PosSemidef ∧
    WeakLimit μ (fun n ω => Real.sqrt n • (that n ω-θ)) (normalVectorLaw S) ∧
    ∀ T : (n : ℕ) → (Fin n → E) → Fin τ → ℝ, ∀ ψ : E → Fin τ → ℝ,
      RegularAL ν θ T ψ → ∀ a : Fin τ → ℝ, 0 ≤ ∑ j, ∑ k,
        a j*(covarianceMatrix (ν θ) ψ j k-S j k)*a k


end
/-- In the explicit iid four-atom law the clipped Bernoulli MLE tends to 1/2, while each fixed-covariate KL minimizer is unique at 1/4 or 3/4.
Target P001-T7: Theorem 5.2.8 (The ML Estimator Is Consistent for the Minimum KL Divergence Predictor), with the target defined by the KL divergence at a fixed $\mathbf{x}$, as printed.
Location: p. 195 (PDF p. 213), Theorem 5.2.8 and Definition 5.2.7. -/
theorem conditional_kl_mle_wrong_target_supporting {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X Y : ℕ → Ω → ℝ) (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (hlaw : μ.map (fun ω => (X 0 ω,Y 0 ω)) =
     (3/8 : ℝ≥0∞) • Measure.dirac (0,0) + (1/8 : ℝ≥0∞) • Measure.dirac (0,1) +
     (1/8 : ℝ≥0∞) • Measure.dirac (1,0) + (3/8 : ℝ≥0∞) • Measure.dirac (1,1)) :
   (∀ p ∈ ({(1/4 : ℝ),3/4} : Set ℝ), ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
     0  ≤  bernoulliKL p t ∧ (bernoulliKL p t = 0 ↔ t=p)) ∧
   CP μ (fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)) (1/2) ∧
   ¬ CP μ (fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)) (1/4) ∧
   ¬ CP μ (fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)) (3/4) := by
  rcases conditional_kl_mle_wrong_target μ X Y hiid hlaw with
    ⟨hKL,_,_,_,_,_,_,hCP,hQ,hT,_⟩
  exact ⟨hKL,hCP,hQ,hT⟩


/-- Integral identity for the complete T88 observed-data bound endpoints. -/
theorem bound_endpoint_formula {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y D : Ω → ℝ)
    (hYi : Integrable Y μ) (hD : Measurable D)
    (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
    (hp0 : 0<prob μ {ω | D ω=0}) (hp1 : 0<prob μ {ω | D ω=1}) (a b : ℝ) :
    mean μ (fun ω => ateLower (Y ω) (D ω) a b)=
      conditionalMeanAt μ D Y 1*prob μ {ω | D ω=1}+a*prob μ {ω | D ω=0}-
        (conditionalMeanAt μ D Y 0*prob μ {ω | D ω=0}+b*prob μ {ω | D ω=1}) := by
  let A := {ω | D ω=1}
  let B := {ω | D ω=0}
  have hA : MeasurableSet A := hD (measurableSet_singleton 1)
  have hB : MeasurableSet B := hD (measurableSet_singleton 0)
  let u1 : Ω → ℝ := A.indicator Y
  let u0 : Ω → ℝ := B.indicator Y
  let s1 : Ω → ℝ := A.indicator (fun _ => 1)
  let s0 : Ω → ℝ := B.indicator (fun _ => 1)
  have hi1 : Integrable u1 μ := hYi.indicator hA
  have hi0 : Integrable u0 μ := hYi.indicator hB
  have hs1 : Integrable s1 μ := (integrable_const 1).indicator hA
  have hs0 : Integrable s0 μ := (integrable_const 1).indicator hB
  have he (ω : Ω) : ateLower (Y ω) (D ω) a b=u1 ω+a*s0 ω-u0 ω-b*s1 ω := by
    rcases hbinary ω with hr|hr <;> simp [ateLower,u1,u0,s1,s0,A,B,hr]
  have hmean1 : (∫ ω,s1 ω ∂μ)=prob μ {ω | D ω=1} := by
    simp [s1,integral_indicator hA,integral_const,measureReal_def,prob,A]
  have hmean0 : (∫ ω,s0 ω ∂μ)=prob μ {ω | D ω=0} := by
    simp [s0,integral_indicator hB,integral_const,measureReal_def,prob,B]
  have hiA : Integrable (fun ω => u1 ω+a*s0 ω) μ := hi1.add (hs0.const_mul a)
  have hiB : Integrable (fun ω => u1 ω+a*s0 ω-u0 ω) μ := hiA.sub hi0
  unfold mean
  simp_rw [he]
  rw [integral_sub hiB (hs1.const_mul b),
    integral_sub hiA hi0,integral_add hi1 (hs0.const_mul a),
    integral_const_mul,integral_const_mul,hmean0,hmean1]
  dsimp [conditionalMeanAt,u1,u0]
  rw [integral_indicator hA,integral_indicator hB,
    div_mul_cancel₀ _ hp1.ne',div_mul_cancel₀ _ hp0.ne']
  ring


/-- Under the bounded potential-outcomes model with both treatment values in support, the corrected lower and upper sample means are unbiased and consistent for the sharp ATE bound endpoints.
Target P001-T88: Theorem 7.1.8 (Estimating Sharp Bounds for the ATE), with two symbols in its proof corrected ($\overline{\tau_i^L}$ for $\overline{Y_i^L}$; $Y_i(1 - D_i)$ for $Y_i(x1 - D_i)$).
Location: Theorem 7.1.8 and the first part of the proof: p. 243 (PDF p. 261); rest of the proof: p. 244 (PDF p. 262). -/
theorem ate_bounds_estimators {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (Y0 Y1 D : ℕ → Ω → ℝ)
  (h0 : ∀ i, Measurable (Y0 i)) (h1 : ∀ i, Measurable (Y1 i))
  (hD : ∀ i, Measurable (D i))
  (hbinary : ∀ i ω, D i ω=0 ∨ D i ω=1)
  (hpos : 0 < prob μ {ω | D 0 ω=1} ∧ prob μ {ω | D 0 ω=1} < 1)
  (a b : ℝ) (hab : a ≤ b)
  (hbounds : ∀ i, ∀ᵐ ω ∂μ, Y0 i ω ∈ Set.Icc a b ∧ Y1 i ω ∈ Set.Icc a b)
  (hiid : IID μ (fun i ω => (observedOutcome (Y0 i ω) (Y1 i ω) (D i ω),D i ω))) :
  let Y := fun i ω => observedOutcome (Y0 i ω) (Y1 i ω) (D i ω)
  let L := fun i ω => ateLower (Y i ω) (D i ω) a b
  let U := fun i ω => ateUpper (Y i ω) (D i ω) a b
  mean μ (L 0) ≤ mean μ (fun ω => Y1 0 ω-Y0 0 ω) ∧
  mean μ (fun ω => Y1 0 ω-Y0 0 ω) ≤ mean μ (U 0) ∧
  mean μ (L 0) =
    conditionalMeanAt μ (D 0) (Y 0) 1*prob μ {ω | D 0 ω=1} +
    a*prob μ {ω | D 0 ω=0} -
    (conditionalMeanAt μ (D 0) (Y 0) 0*prob μ {ω | D 0 ω=0} + b*prob μ {ω | D 0 ω=1}) ∧
  mean μ (U 0) =
    conditionalMeanAt μ (D 0) (Y 0) 1*prob μ {ω | D 0 ω=1} +
    b*prob μ {ω | D 0 ω=0} -
    (conditionalMeanAt μ (D 0) (Y 0) 0*prob μ {ω | D 0 ω=0} + a*prob μ {ω | D 0 ω=1}) ∧
  (∃ A0 A1 : Ω → ℝ,
    Measurable A0 ∧ Measurable A1 ∧
    (∀ᵐ ω ∂μ, A0 ω ∈ Set.Icc a b ∧ A1 ω ∈ Set.Icc a b ∧
      observedOutcome (A0 ω) (A1 ω) (D 0 ω)=Y 0 ω) ∧
    mean μ (fun ω => A1 ω-A0 ω)=mean μ (L 0)) ∧
  (∃ A0 A1 : Ω → ℝ,
    Measurable A0 ∧ Measurable A1 ∧
    (∀ᵐ ω ∂μ, A0 ω ∈ Set.Icc a b ∧ A1 ω ∈ Set.Icc a b ∧
      observedOutcome (A0 ω) (A1 ω) (D 0 ω)=Y 0 ω) ∧
    mean μ (fun ω => A1 ω-A0 ω)=mean μ (U 0)) ∧
  (∀ n : ℕ, 0 < n → mean μ (sampleMean L n)=mean μ (L 0) ∧
    mean μ (sampleMean U n)=mean μ (U 0)) ∧
  CP μ (sampleMean L) (mean μ (L 0)) ∧ CP μ (sampleMean U) (mean μ (U 0)) := by
  let Y := fun i ω => observedOutcome (Y0 i ω) (Y1 i ω) (D i ω)
  let L := fun i ω => ateLower (Y i ω) (D i ω) a b
  let U := fun i ω => ateUpper (Y i ω) (D i ω) a b
  let M := max |a| |b|
  have ha : |a|≤M := le_max_left _ _
  have hb : |b|≤M := le_max_right _ _
  have hy : ∀ᵐ ω ∂μ,|Y 0 ω|≤M := by
    filter_upwards [hbounds 0] with ω hω
    rcases hbinary 0 ω with hr|hr
    · simpa [M,Y,observedOutcome,hr] using abs_le_max_abs_abs hω.1.1 hω.1.2
    · simpa [M,Y,observedOutcome,hr] using abs_le_max_abs_abs hω.2.1 hω.2.2
  have h2Y : MemLp (Y 0) 2 μ := MemLp.of_bound
    (measurable_fst.comp (hiid.1 0)).aestronglyMeasurable M
      (by simpa only [Real.norm_eq_abs] using hy)
  let gL : ℝ × ℝ → ℝ := fun yd => ateLower yd.1 yd.2 a b
  let gU : ℝ × ℝ → ℝ := fun yd => ateUpper yd.1 yd.2 a b
  have hgL : Measurable gL := by
    change Measurable (fun yd : ℝ × ℝ => yd.1*yd.2+a*(1-yd.2)-yd.1*(1-yd.2)-b*yd.2)
    fun_prop
  have hgU : Measurable gU := by
    change Measurable (fun yd : ℝ × ℝ => yd.1*yd.2+b*(1-yd.2)-yd.1*(1-yd.2)-a*yd.2)
    fun_prop
  have hLiid : IID μ L := ⟨fun i => hgL.comp (hiid.1 i),
    hiid.2.1.comp (fun _ => gL) (fun _ => hgL),fun i => (hiid.2.2 i).comp hgL⟩
  have hUiid : IID μ U := ⟨fun i => hgU.comp (hiid.1 i),
    hiid.2.1.comp (fun _ => gU) (fun _ => hgU),fun i => (hiid.2.2 i).comp hgU⟩
  have hLb : ∀ᵐ ω ∂μ,|L 0 ω|≤2*M := by
    filter_upwards [hy] with ω hω
    rcases hbinary 0 ω with hr|hr
    · simp only [L,ateLower,hr,mul_zero,mul_one,sub_zero,zero_sub,zero_add,add_zero]
      nlinarith [abs_sub a (Y 0 ω)]
    · simp only [L,ateLower,hr,mul_zero,mul_one,sub_zero,zero_sub,zero_add,add_zero,sub_self]
      nlinarith [abs_sub (Y 0 ω) b]
  have hUb : ∀ᵐ ω ∂μ,|U 0 ω|≤2*M := by
    filter_upwards [hy] with ω hω
    rcases hbinary 0 ω with hr|hr
    · simp only [U,ateUpper,hr,mul_zero,mul_one,sub_zero,zero_sub,zero_add,add_zero]
      nlinarith [abs_sub b (Y 0 ω)]
    · simp only [U,ateUpper,hr,mul_zero,mul_one,sub_zero,zero_sub,zero_add,add_zero,sub_self]
      nlinarith [abs_sub (Y 0 ω) a]
  have h2L : MemLp (L 0) 2 μ := MemLp.of_bound (hLiid.1 0).aestronglyMeasurable (2*M)
    (by simpa only [Real.norm_eq_abs] using hLb)
  have h2U : MemLp (U 0) 2 μ := MemLp.of_bound (hUiid.1 0).aestronglyMeasurable (2*M)
    (by simpa only [Real.norm_eq_abs] using hUb)
  have hB : {ω | D 0 ω=0}={ω | D 0 ω=1}ᶜ := by
    ext ω
    rcases hbinary 0 ω with hr|hr <;> simp [hr]
  have hp0 : 0<prob μ {ω | D 0 ω=0} := by
    rw [hB]
    have hcompl : μ.real {ω | D 0 ω=1}ᶜ=1-μ.real {ω | D 0 ω=1} := by
      simpa only [Set.preimage,Set.mem_singleton_iff] using
        probReal_compl_eq_one_sub (μ := μ) ((hD 0) (measurableSet_singleton 1))
    change 0<μ.real {ω | D 0 ω=1}ᶜ
    rw [hcompl]
    exact sub_pos.mpr hpos.2
  have hLF := bound_endpoint_formula μ (Y 0) (D 0) (h2Y.integrable one_le_two)
    (hD 0) (hbinary 0) hp0 hpos.1 a b
  have hUF := bound_endpoint_formula μ (Y 0) (D 0) (h2Y.integrable one_le_two)
    (hD 0) (hbinary 0) hp0 hpos.1 b a
  let C0 : Ω → ℝ := fun ω => clip a b (Y0 0 ω)
  let C1 : Ω → ℝ := fun ω => clip a b (Y1 0 ω)
  have hc_range (x : ℝ) : clip a b x∈Set.Icc a b := by
    exact ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩
  have hc_eq (x : ℝ) (hx : x∈Set.Icc a b) : clip a b x=x := by
    simp only [clip,min_eq_right hx.2,max_eq_right hx.1]
  have hC : ∀ᵐ ω ∂μ,C0 ω=Y0 0 ω ∧ C1 ω=Y1 0 ω := by
    filter_upwards [hbounds 0] with ω hω
    exact ⟨hc_eq _ hω.1,hc_eq _ hω.2⟩
  have hC0 : Measurable C0 := by
    change Measurable (fun ω => max a (min b (Y0 0 ω)))
    fun_prop
  have hC1 : Measurable C1 := by
    change Measurable (fun ω => max a (min b (Y1 0 ω)))
    fun_prop
  let CY : Ω → ℝ := fun ω => observedOutcome (C0 ω) (C1 ω) (D 0 ω)
  let CL : Ω → ℝ := fun ω => ateLower (CY ω) (D 0 ω) a b
  let CU : Ω → ℝ := fun ω => ateUpper (CY ω) (D 0 ω) a b
  have hCY : CY=ᵐ[μ] Y 0 := by
    filter_upwards [hC] with ω hω
    simp only [CY,Y,hω.1,hω.2]
  have hCL : mean μ CL=mean μ (L 0) := integral_congr_ae (by
    filter_upwards [hCY] with ω hω
    simp only [CL,L,hω])
  have hCU : mean μ CU=mean μ (U 0) := integral_congr_ae (by
    filter_upwards [hCY] with ω hω
    simp only [CU,U,hω])
  have hCτ : mean μ (fun ω => C1 ω-C0 ω)=mean μ (fun ω => Y1 0 ω-Y0 0 ω) :=
    integral_congr_ae (by
      filter_upwards [hC] with ω hω
      simp only [hω.1,hω.2])
  have hs := ate_sharp_bounds_and_width μ C0 C1 (D 0) hC0 hC1 (hD 0) a b
    (fun ω => ⟨hc_range _,hc_range _⟩) (hbinary 0)
  change mean μ (fun ω => C1 ω-C0 ω)∈Set.Icc (mean μ CL) (mean μ CU) ∧
    mean μ CU-mean μ CL=b-a ∧ _ at hs
  have hLU : mean μ CL≤mean μ CU := hs.1.1.trans hs.1.2
  have hlo := hs.2.2 (mean μ CL) ⟨le_rfl,hLU⟩
  have hup := hs.2.2 (mean μ CU) ⟨hLU,le_rfl⟩
  refine ⟨?_,?_,hLF,?_,?_,?_,?_,weak_law_finite_variance μ L hLiid h2L,
    weak_law_finite_variance μ U hUiid h2U⟩
  · simpa only [hCL,hCτ] using hs.1.1
  · simpa only [hCU,hCτ] using hs.1.2
  · simpa only [ateUpper,ateLower] using hUF
  · obtain ⟨A0,A1,hm0,hm1,hbnd,hobs,hmean⟩ := hlo
    refine ⟨A0,A1,hm0,hm1,?_,?_⟩
    · filter_upwards [hCY] with ω hω
      exact ⟨(hbnd ω).1,(hbnd ω).2,(congrFun hobs ω).trans hω⟩
    · exact hmean.trans hCL
  · obtain ⟨A0,A1,hm0,hm1,hbnd,hobs,hmean⟩ := hup
    refine ⟨A0,A1,hm0,hm1,?_,?_⟩
    · filter_upwards [hCY] with ω hω
      exact ⟨(hbnd ω).1,(hbnd ω).2,(congrFun hobs ω).trans hω⟩
    · exact hmean.trans hCU
  · intro n hn
    exact ⟨(iid_sample_mean_finite_moments μ L hLiid h2L n hn).1,
      (iid_sample_mean_finite_moments μ U hUiid h2U n hn).1⟩


end AronowAudit.P001
