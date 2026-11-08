import Mathlib
import SAP.P037a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

/-! The four-school design is the exact hypergeometric convolution already
defined in `Defs`. Zero-mass padding in `CompositionAssignment` is retained. -/

def compositionFullSupport : Prop :=
  (∀ k : Fin 13, 0 < countMass 1 k ↔ k.val ≤ 4) ∧
  (∀ k : Fin 13, 0 < countMass 3 k) ∧
  (Finset.univ.filter (fun w : CompositionAssignment => 0 < assignmentMass w)).card = 454

/-- Conditional moments on treatment: the interaction and its centered error
are zero outside treatment, so division by the treatment probability gives
the ordinary conditional first and centered second moments. -/
def compositionConditionalMoments : Prop := ∀ i : Fin 4,
  let p := compositionMean (fun w => treatment w.1 i)
  0 < p ∧
  compositionMean (fun w => compositionColumn w i) / p = eligibleFraction i ∧
  compositionMean (fun w =>
    (compositionColumn w i - treatment w.1 i * eligibleFraction i)^2) / p =
      eligibleFraction i * (1 - eligibleFraction i) / 36 ∧
  eligibleFraction i * (1 - eligibleFraction i) / 36 =
    if i.val < 2 then 1/400 else 7/1200

noncomputable def blockRegressionLoss {B : ℕ} (w : Fin B → CompositionAssignment)
    (alpha : Fin B → ℝ) (theta : Fin 3 → ℝ) : ℝ :=
  ∑ b, ∑ i : Fin 4,
    (observedOutcome (w b) i - alpha b -
      ∑ k : Fin 3, regressionColumns (w b) k i * theta k)^2

/-- Actual minimization over the B block intercepts and all three slopes. -/
def IsBlockOLS {B : ℕ} (w : Fin B → CompositionAssignment)
    (alpha : Fin B → ℝ) (theta : Fin 3 → ℝ) : Prop :=
  ∀ alpha' theta', blockRegressionLoss w alpha theta ≤ blockRegressionLoss w alpha' theta'

noncomputable def pooledCompositionGram {B : ℕ} (w : Fin B → CompositionAssignment) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun k l => ∑ b, centeredCross (regressionColumns (w b) k) (regressionColumns (w b) l)

noncomputable def pooledCompositionRhs {B : ℕ} (w : Fin B → CompositionAssignment) : Fin 3 → ℝ :=
  fun k => ∑ b, centeredCross (regressionColumns (w b) k) (observedOutcome (w b))

noncomputable def pooledCompositionCoefficient {B : ℕ}
    (w : Fin B → CompositionAssignment) : Fin 3 → ℝ :=
  (pooledCompositionGram w)⁻¹.mulVec (pooledCompositionRhs w)

noncomputable def repeatedCompositionProbability (B : ℕ)
    (event : (Fin B → CompositionAssignment) → Prop) : ℝ :=
  ∑ w, (∏ b, assignmentMass (w b)) * if event w then 1 else 0

def blockOLSExists : Prop := ∀ B (w : Fin B → CompositionAssignment),
  ∃ alpha theta, IsBlockOLS w alpha theta

def blockOLSProbabilityLimit : Prop :=
  ∀ (alpha : ∀ B, (Fin B → CompositionAssignment) → Fin B → ℝ)
    (theta : ∀ B, (Fin B → CompositionAssignment) → Fin 3 → ℝ),
    (∀ B w, IsBlockOLS w (alpha B w) (theta B w)) →
    ∀ eps : ℝ, 0 < eps →
      Tendsto (fun B => repeatedCompositionProbability B
        (fun w => eps < |theta B w 2 - (-16/31)|)) atTop (𝓝 0)

def blockSingularProbabilityLimit : Prop :=
  Tendsto (fun B => repeatedCompositionProbability B
    (fun w => (pooledCompositionGram w).det = 0)) atTop (𝓝 0)

/-- P037-T1; SI Appendix pp. 13–14, repeated pp. 15–16 and Table S7
(p. 42); main p. 568. The exact four-school hierarchical design has the
stated treatment and conditional seed moments, feasible supports and 454
positive-mass collapsed states. Composition has zero causal slope, yet the
expected regression has the displayed matrices and unique slope -16/31;
the general response schedule gives (15 b1 + 16 b2)/31. Under independent
block repetition, every selection of actual least-squares minimizers has
composition coefficient converging in probability to -16/31. Minimizers
exist, and singular pooled Gram matrices have probability tending to zero.
The usual measure-theoretic conditions are assumed. -/
def T1WholeStatement : Prop :=
  T1Statement ∧ compositionFullSupport ∧ compositionConditionalMoments ∧
  blockOLSExists ∧ blockSingularProbabilityLimit ∧ blockOLSProbabilityLimit

noncomputable def wholeNormalCDF (z : ℝ) : ℝ := cdf (gaussianReal 0 1) z

noncomputable def wholeNormalTail (z : ℝ) : ℝ := 2 * (1 - wholeNormalCDF z)

noncomputable def wholeNormalCritical : ℝ :=
  sInf {z : ℝ | 1 - (1/20:ℝ)/2 ≤ wholeNormalCDF z}

noncomputable def roundHundredth (x : ℝ) : ℝ := (round (100*x) : ℝ) / 100

def wholeWaldRounding : Prop := ∀ e s : ℝ,
  e < 0 → tableS6Bins e s → roundHundredth e = -6/100 ∧ roundHundredth s = 3/100

def wholeNormalNumbers : Prop :=
  1/20 < wholeNormalTail (19/10) ∧ wholeNormalTail 2 < 1/20 ∧
  1/20 < wholeNormalTail (195996/100000) ∧
  wholeNormalTail (195997/100000) < 1/20 ∧
  |wholeNormalTail (57/28) - 4178/100000| < 1/200000 ∧
  |wholeNormalTail (57/34) - 9365/100000| < 1/200000 ∧
  |wholeNormalTail 2 - 4550/100000| < 1/200000 ∧
  |wholeNormalTail (19/10) - 5743/100000| < 1/200000 ∧
  |wholeNormalTail (11/7) - 11608/100000| < 1/200000 ∧
  |wholeNormalTail (13/5) - 932/100000| < 1/200000

def wholeNormalQuantile : Prop :=
  wholeNormalCDF wholeNormalCritical = 39/40 ∧
  (∀ z, wholeNormalCDF z = 39/40 ↔ z = wholeNormalCritical) ∧
  19/10 < wholeNormalCritical ∧ wholeNormalCritical < 2 ∧
  195996/100000 < wholeNormalCritical ∧ wholeNormalCritical < 195997/100000 ∧
  11/7 < wholeNormalCritical ∧ wholeNormalCritical < 13/5

def wholeNormalDecisions : Prop :=
  wholeNormalTail (waldStatistic (-57/1000) (7/250)) < 1/20 ∧
  1/20 < wholeNormalTail (waldStatistic (-57/1000) (17/500)) ∧
  (∃ e s e' s' : ℝ, e < 0 ∧ e' < 0 ∧
    tableS6Bins e s ∧ tableS6Bins e' s' ∧
    roundHundredth e = -6/100 ∧ roundHundredth e' = -6/100 ∧
    roundHundredth s = 3/100 ∧ roundHundredth s' = 3/100 ∧
    wholeNormalTail (waldStatistic e s) < 1/20 ∧
    1/20 < wholeNormalTail (waldStatistic e' s'))

/-- P037-T3; main p. 569; 2018 Correction p. E3598; SI Table S6 p. 41.
The two significance descriptions are incompatible. The strict rounding
bins give the same displayed estimate and standard error for two witnesses
with opposite actual two-sided normal Wald decisions. The exact ratio
envelope is (11/7,13/5), containing the unique normal 0.975 quantile, which
lies strictly between 1.95996 and 1.95997. The normal-tail comparisons at
1.9 and 2 and the six stated five-decimal approximations are certified;
rounding alone therefore does not determine significance. Decimal tail
approximations mean error less than 0.000005. The usual measure-theoretic
conditions are assumed. -/
def T3WholeStatement : Prop :=
  T3Statement ∧ wholeWaldRounding ∧ wholeNormalNumbers ∧
  wholeNormalQuantile ∧ wholeNormalDecisions

/-! Coordinates for the exponential-to-simplex calculation. `n` denotes
the number of schools minus two, so every vector below has at least two
coordinates. The last coordinate of the cone is the positive total. -/

def positiveOrthant (n : ℕ) : Set (Fin (n+2) → ℝ) := {e | ∀ i, 0 < e i}

def simplexCone (n : ℕ) : Set (Fin (n+2) → ℝ) :=
  {x | (fun i : Fin (n+1) => x i.castSucc) ∈ openSimplex (n+1) ∧ 0 < x (Fin.last (n+1))}

noncomputable def simplexConeMap (n : ℕ) (x : Fin (n+2) → ℝ) : Fin (n+2) → ℝ :=
  fun i => x (Fin.last (n+1)) * appendSimplex (n+1) (fun j => x j.castSucc) i

noncomputable def simplexConeInverse (n : ℕ) (e : Fin (n+2) → ℝ) : Fin (n+2) → ℝ :=
  Fin.snoc (fun i : Fin (n+1) => e i.castSucc / ∑ j, e j) (∑ j, e j)

noncomputable def simplexConeJacobian (n : ℕ) (x : Fin (n+2) → ℝ) :
    Matrix (Fin (n+2)) (Fin (n+2)) ℝ :=
  fun i j => if i.val < n+1 then
    if j.val < n+1 then (if i = j then x (Fin.last (n+1)) else 0) else x i
    else if j.val < n+1 then -x (Fin.last (n+1))
    else 1 - ∑ k : Fin (n+1), x k.castSucc

noncomputable def exponentialProduct (n : ℕ) : Measure (Fin (n+2) → ℝ) :=
  Measure.pi (fun _ => expMeasure 1)

noncomputable def exponentialWeightLaw (n : ℕ) : Measure (Fin (n+2) → ℝ) :=
  Measure.map normalizedWeights (exponentialProduct n)

noncomputable def exponentialConeDensityLaw (n : ℕ) : Measure (Fin (n+2) → ℝ) :=
  (volume.restrict (simplexCone n)).withDensity (fun x =>
    ENNReal.ofReal (x (Fin.last (n+1)) ^ (n+1) * Real.exp (-x (Fin.last (n+1)))))

def exponentialJointLaw : Prop := ∀ n,
  Measure.map (simplexConeInverse n) (exponentialProduct n) = exponentialConeDensityLaw n

def exponentialSimplexLaw : Prop := ∀ n,
  exponentialWeightLaw n = simplexLaw (n+1) ∧
  IsProbabilityMeasure (simplexLaw (n+1)) ∧
  ∀ᵐ p ∂simplexLaw (n+1), (∀ i, 0 < p i) ∧ ∑ i, p i = 1

/-- The pointwise ratio algebra is asserted only on a set of full measure
where the draws and every denominator used in the claim are positive. -/
def PositiveRatioFacts {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ)
    (X : Fin (n+2) → Ω → ℝ) : Prop :=
  ∀ᵐ w ∂μ, (∀ i, 0 < X i w) ∧ 0 < ∑ i, X i w ∧
    0 < X 0 w + X 1 w ∧
    normalizedWeights (fun i => X i w) 0 /
      (normalizedWeights (fun i => X i w) 0 + normalizedWeights (fun i => X i w) 1) =
      X 0 w / (X 0 w + X 1 w) ∧
    (X 0 w / (X 0 w + X 1 w) < 1/4 ↔ X 0 w < X 1 w / 3)

def bootstrapRandomComparison : Prop :=
  ∀ (n : ℕ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U E : Fin (n+2) → Ω → ℝ),
    (∀ i, Measurable (U i)) → (∀ i, Measurable (E i)) →
    iIndepFun U μ → iIndepFun E μ →
    (∀ i, Measure.map (U i) μ = uniformDraw) →
    (∀ i, Measure.map (E i) μ = expMeasure 1) →
    PositiveRatioFacts μ n U ∧ PositiveRatioFacts μ n E ∧
    Measure.map (fun w => normalizedWeights (fun i => U i w)) μ = uniformWeightLaw n ∧
    Measure.map (fun w => normalizedWeights (fun i => E i w)) μ = simplexLaw (n+1) ∧
    (μ {w | normalizedWeights (fun i => U i w) ∈ ratioEvent n}).toReal = 1/6 ∧
    (μ {w | normalizedWeights (fun i => E i w) ∈ ratioEvent n}).toReal = 1/4 ∧
    (μ {w | E 0 w < E 1 w / 3}).toReal = 1/4 ∧
    Measure.map (fun w => normalizedWeights (fun i => U i w)) μ ≠
      Measure.map (fun w => normalizedWeights (fun i => E i w)) μ

def exponentialCombinedIntegral : Prop :=
  IntegrableOn (fun v : ℝ => Real.exp (-v) * (1 - Real.exp (-v/3))) (Ioi 0) ∧
  (∫ v : ℝ in Ioi 0, Real.exp (-v) * (1 - Real.exp (-v/3))) = 1/4

/-- The inverse formula is a genuine unique WLS solution on the canonical
positive-weight, full-column-rank domain, including an empty coefficient type. -/
def wlsRegularity : Prop :=
  ∀ {I K : Type} [Fintype I] [Fintype K] [DecidableEq K]
    (w : I → ℝ) (X : Matrix I K ℝ) (y : I → ℝ),
    (∀ i, 0 < w i) → Function.Injective X.mulVec →
    (gramWeighted w X).det ≠ 0 ∧ WLS w X y (wlsCoefficient w X y) ∧
    ∀ b, WLS w X y b → b = wlsCoefficient w X y

/-- P037-T4; SI Appendix Table S6 note p. 41 and Table S7 note p. 42.
For every number of schools at least two, normalized independent uniforms
give ratio-event probability 1/6. Normalized independent standard
exponentials have the constant-density Dirichlet(1,...,1) simplex law and
give probability 1/4, also the probability E1 < E2/3 and the integral of
exp(-v)(1-exp(-v/3)) on the positive half-line. These are different weight
laws, with probability difference -1/12. All normalization and ratio
denominators are positive almost surely. Positive common rescaling,
including normalization, preserves the unique WLS coefficients for positive
weights and full column rank. The usual measure-theoretic conditions are
assumed. -/
def T4WholeStatement : Prop :=
  T4Statement ∧ exponentialSimplexLaw ∧ bootstrapRandomComparison ∧
  exponentialCombinedIntegral ∧ wlsRegularity

noncomputable def twoExponentialForward (e : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![e 0 / (e 0 + e 1), e 0 + e 1]

noncomputable def twoExponentialForwardDerivative : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (Matrix.toLin' (!![1/4, -1/4; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)).toContinuousLinearMap

/-- P037-T5; SI Appendix Tables S6 and S7 pp. 41–42; validator's
construction, mathematical clause (b). The printed claim is false:
the displayed forward map e ↦ (e1/(e1+e2), e1+e2) has at the positive
point (1,1) derivative matrix [[1/4,-1/4],[1,1]], whose absolute determinant
is 1/2, whereas t^(n-1) is 2 for n=2 and t=2. Thus the stated Jacobian
orientation is false. The inverse-map volume factor t^(n-1) and the
normalized-exponential construction are not refuted. The usual
measure-theoretic conditions are assumed. -/
def T5WholeStatement : Prop :=
  (∀ i : Fin 2, 0 < (![1,1] : Fin 2 → ℝ) i) ∧
  (∑ i : Fin 2, (![1,1] : Fin 2 → ℝ) i) = 2 ∧
  twoExponentialForward ![1,1] = ![1/2,2] ∧
  HasFDerivAt twoExponentialForward twoExponentialForwardDerivative ![1,1] ∧
  |(!![1/4,-1/4;1,1] : Matrix (Fin 2) (Fin 2) ℝ).det| = 1/2 ∧
  |(!![1/4,-1/4;1,1] : Matrix (Fin 2) (Fin 2) ℝ).det| ≠
    (∑ i : Fin 2, (![1,1] : Fin 2 → ℝ) i)^(2-1)

end SAP.P037a
