import Mathlib
import SAP.P061a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a

open scoped BigOperators Topology Classical BoundedContinuousFunction ENNReal
open Filter MeasureTheory

/-- The literal binary vector corresponding to a list of pairs. -/
def flattenBitsW1 (K : ℕ) (z : Fin K → BitPair) (i : Fin (K*2)) : Fin 2 :=
  if (finProdFinEquiv.symm i).2 = 0 then (z (finProdFinEquiv.symm i).1).1
  else (z (finProdFinEquiv.symm i).1).2

/-- The other member of the same pair. -/
def partnerIndexW1 (K : ℕ) (i : Fin (K*2)) : Fin (K*2) :=
  finProdFinEquiv ((finProdFinEquiv.symm i).1,
    if (finProdFinEquiv.symm i).2 = 0 then 1 else 0)

/-- Exact coordinate and hybrid interpretation of the paired encoding. -/
def PairEncodingW1 (K : ℕ) : Prop :=
  Function.Bijective (flattenBitsW1 K) ∧
  (∀ i, partnerIndexW1 K i ≠ i ∧ partnerIndexW1 K (partnerIndexW1 K i) = i) ∧
  (∀ i z, ((flattenBitsW1 K z i).val : ℝ) = pairedOwnBit K i z ∧
    pairedPartnerBit K i z = pairedOwnBit K (partnerIndexW1 K i) z) ∧
  (∀ i e z, flattenBitsW1 K (pairedReplacement K i e z) =
    Function.update (flattenBitsW1 K z) i e)

/-- Assignment dependence between distinct units, defined through all events. -/
def assignmentEdgeW1 {K : ℕ} (D : AtomicDesign (Fin K → BitPair))
    (i j : Fin (K*2)) : Prop :=
  i ≠ j ∧ ¬independent D (pairedOwnBit K i) (pairedOwnBit K j)

/-- Raw response influence: change only j's assignment and change i's response. -/
def interferenceEdgeW1 (m : ℕ) (i j : Fin (m^8*2)) : Prop :=
  i ≠ j ∧ ∃ z z' : Fin (m^8) → BitPair,
    (∀ k, k ≠ j → pairedOwnBit (m^8) k z = pairedOwnBit (m^8) k z') ∧
    pairResponses m i z ≠ pairResponses m i z'

/-- Graph degrees are the numbers of adjacent vertices; max degree is their finite supremum. -/
noncomputable def relationDegreeW1 {N : ℕ} (R : Fin N → Fin N → Prop) (i : Fin N) : ℕ :=
  (Finset.univ.filter (R i)).card

noncomputable def relationMaxDegreeW1 {N : ℕ} (R : Fin N → Fin N → Prop) : ℕ :=
  Finset.univ.sup (relationDegreeW1 R)

/-- All finite probability, expectation, coverage, and limit facts already in the package. -/
def PairBaseW1 (D : ∀ m, AtomicDesign (Fin (m^8) → BitPair)) : Prop :=
    (∀ m z, (D m).mass z = ∏ k : Fin (m^8),
      if (z k).1 = (z k).2 then (1+pairParameter m)/4 else (1-pairParameter m)/4) ∧
    (∀ m, 2 ≤ m → PairInferenceFacts D m) ∧
    (Tendsto (fun (index : ℕ) => populationContrast (D (index+2)) (pairedOwnBit ((index+2)^8)) (pairResponses (index+2)) 1 0 -
      pairDirectContrast (index+2) (D (index+2))) atTop (𝓝 0) ∧
    Tendsto (fun (index : ℕ) => ((index+2)^8*2 : ℝ)*designVariance (D (index+2)) (pairEstimator (index+2) (D (index+2)))) atTop (𝓝 4) ∧
    Tendsto (fun (index : ℕ) => ((populationContrast (D (index+2)) (pairedOwnBit ((index+2)^8)) (pairResponses (index+2)) 1 0 -
      pairDirectContrast (index+2) (D (index+2)))/pairStandardError (index+2) (D (index+2)))^2) atTop atTop ∧
    Tendsto (fun (index : ℕ) => eventProbability (D (index+2))
      (fun z => |pairEstimator (index+2) (D (index+2)) z - pairDirectContrast (index+2) (D (index+2))| ≤ 5*pairStandardError (index+2) (D (index+2)))) atTop (𝓝 0))

/-- P061-T4; main p. 14, supplement's HT contrast.
Independent correlated pairs on the full binary cube have exactly one assignment-dependence
neighbor and one interference neighbor per unit. All clauses (a)–(f) hold: positivity, bounded
responses, the exact AEED, zero direct effect, unbiased HT moments, both variance expressions
and coverage bounds. The target gap vanishes but its standardized value diverges; its exact
population-size normalization and the standard-error limit give the claimed orders.
The usual measure-theoretic conditions are assumed; here every space is finite.
Limits use m=index+2, along the claimed populations N=2m^8. -/
def T4WholeStatement : Prop :=
  ∃ D : ∀ m, AtomicDesign (Fin (m^8) → BitPair), PairBaseW1 D ∧
    (∀ m, 2 ≤ m → PairEncodingW1 (m^8) ∧
      (∀ i j, assignmentEdgeW1 (D m) i j ↔ j = partnerIndexW1 (m^8) i) ∧
      (∀ i j, interferenceEdgeW1 m i j ↔ j = partnerIndexW1 (m^8) i) ∧
      (∀ i, relationDegreeW1 (assignmentEdgeW1 (D m)) i = 1 ∧
        relationDegreeW1 (interferenceEdgeW1 m) i = 1) ∧
      relationMaxDegreeW1 (assignmentEdgeW1 (D m)) = 1 ∧
      relationMaxDegreeW1 (interferenceEdgeW1 m) = 1 ∧
      variancePolynomial m =
        8*(1+1/(m : ℝ))*(1+1/(m : ℝ)) +
          (6+2/(m : ℝ))*(1/(m : ℝ))^2 - 4*(1/(m : ℝ))^4 ∧
      (populationContrast (D m) (pairedOwnBit (m^8)) (pairResponses m) 1 0 -
        pairDirectContrast m (D m)) * Real.rpow (m^8*2 : ℝ) (1/4 : ℝ) =
          Real.rpow 2 (1/4 : ℝ)) ∧
    Tendsto (fun n : ℕ =>
      (populationContrast (D (n+2)) (pairedOwnBit ((n+2)^8)) (pairResponses (n+2)) 1 0 -
        pairDirectContrast (n+2) (D (n+2))) / pairStandardError (n+2) (D (n+2))) atTop atTop ∧
    Tendsto (fun n : ℕ => pairStandardError (n+2) (D (n+2)) *
      Real.sqrt ((n+2)^8*2 : ℝ)) atTop (𝓝 2)

/-- A population of size n+2 with one correlated pair and n further fair bits. -/
abbrev BoundarySpaceW1 (n : ℕ) := Fin (n+2) → Fin 2

def boundaryExposureW1 (n : ℕ) : Exposures (BoundarySpaceW1 n) (n+2) :=
  fun i z => ((z i).val : ℝ)

noncomputable def boundaryResponsesW1 (n : ℕ) : Responses (BoundarySpaceW1 n) (n+2) :=
  fun i z => if i = 0 then 1 + ((z 1).val : ℝ)/(n+2 : ℝ)
    else if i = 1 then 1 + ((z 0).val : ℝ)/(n+2 : ℝ) else 1

noncomputable def boundaryScaleW1 (n : ℕ) : ℝ := 1/(n+2 : ℝ)
noncomputable def boundaryTargetW1 (n : ℕ) : ℝ := 1/(n+2 : ℝ)^2

def boundarySignW1 (n : ℕ) (z : BoundarySpaceW1 n) : ℝ := 2*((z 0).val : ℝ)-1

noncomputable def boundaryEstimatorW1 (n : ℕ) (z : BoundarySpaceW1 n) : ℝ :=
  boundaryTargetW1 n + boundaryScaleW1 n * boundarySignW1 n z

noncomputable def boundaryDirectW1 (n : ℕ) (D : AtomicDesign (BoundarySpaceW1 n)) : ℝ :=
  (n+2 : ℝ)⁻¹ * ∑ i, mean D (fun z =>
    boundaryResponsesW1 n i (Function.update z i 1) -
      boundaryResponsesW1 n i (Function.update z i 0))

/-- The probability law assigning mass one half to each of -1 and 1. -/
noncomputable def fairSignLawW1 : Measure ℝ :=
  (1/2 : ℝ≥0∞) • Measure.dirac (-1) + (1/2 : ℝ≥0∞) • Measure.dirac 1

/-- The full-support design density, with an independent fair remainder. -/
def BoundaryMassW1 (n : ℕ) (D : AtomicDesign (BoundarySpaceW1 n)) : Prop :=
  ∀ z, D.mass z = (if z 0 = z 1 then (3/8 : ℝ) else 1/8) * (1/2 : ℝ)^n

def BoundaryMarginsW1 (n : ℕ) (D : AtomicDesign (BoundarySpaceW1 n)) : Prop :=
  (∀ z, supported D z) ∧
  (∀ i, exposureProbability D (boundaryExposureW1 n) i 1 = 1/2 ∧
    exposureProbability D (boundaryExposureW1 n) i 0 = 1/2)

/-- Actual EPOs and feasible raw direct effects, not stipulated target values. -/
def BoundaryTargetsW1 (n : ℕ) (D : AtomicDesign (BoundarySpaceW1 n)) : Prop :=
  (∀ i z, 1 ≤ boundaryResponsesW1 n i z ∧ boundaryResponsesW1 n i z ≤ 3/2) ∧
  (∀ i, exposureMean D (boundaryExposureW1 n) (boundaryResponsesW1 n) i 1 =
      (if i = 0 ∨ i = 1 then 1 + (3/4 : ℝ)/(n+2 : ℝ) else 1) ∧
    exposureMean D (boundaryExposureW1 n) (boundaryResponsesW1 n) i 0 =
      (if i = 0 ∨ i = 1 then 1 + (1/4 : ℝ)/(n+2 : ℝ) else 1)) ∧
  (∀ i z, boundaryResponsesW1 n i (Function.update z i 1) -
    boundaryResponsesW1 n i (Function.update z i 0) = 0) ∧
  populationContrast D (boundaryExposureW1 n) (boundaryResponsesW1 n) 1 0 = boundaryTargetW1 n ∧
  boundaryDirectW1 n D = 0

/-- Exact fair-sign statistic and boundary coverages, with its true variance. -/
def BoundaryStatisticW1 (n : ℕ) (D : AtomicDesign (BoundarySpaceW1 n)) : Prop :=
  mean D (boundaryEstimatorW1 n) = boundaryTargetW1 n ∧
  designVariance D (boundaryEstimatorW1 n) = (boundaryScaleW1 n)^2 ∧
  (∀ f : ℝ →ᵇ ℝ, mean D (fun z => f ((boundaryEstimatorW1 n z - boundaryTargetW1 n)/
      boundaryScaleW1 n)) = (f (-1) + f 1)/2) ∧
  eventProbability D (fun z => |boundaryEstimatorW1 n z - boundaryTargetW1 n| ≤
    boundaryScaleW1 n) = 1 ∧
  eventProbability D (fun z => |boundaryEstimatorW1 n z| ≤ boundaryScaleW1 n) = 1/2

/-- The printed claim is false: the unrestricted equal-coverage clause fails at atoms.
P061-T5; main p. 14, the corrected inference-transfer assertion.
On populations of size N=n+2 with individualistic exposures and finite feasible hybrids,
AEED=1/N^2 and direct effect=0. An unbiased estimator has exact standard error s=1/N;
its centered score has the fair-sign law and its estimated scale equals s. The standardized
target gap tends to zero and both studentized scores have this same limiting law, yet at q=1
the AEED intervals have coverage 1 and the direct-effect intervals have coverage 1/2.
Both coverage limits exist and differ. All usual measure-theoretic conditions hold on these
finite full-support spaces. The law-transfer assertion survives; the unqualified coverage
consequence in the canonical conjunction is false. -/
def T5WholeStatement : Prop :=
  IsProbabilityMeasure fairSignLawW1 ∧
  ∃ D : ∀ n, AtomicDesign (BoundarySpaceW1 n),
    (∀ n, BoundaryMassW1 n (D n) ∧ BoundaryMarginsW1 n (D n) ∧
      BoundaryTargetsW1 n (D n) ∧ BoundaryStatisticW1 n (D n)) ∧
    (∀ n, 0 < boundaryScaleW1 n) ∧
    (∀ n, targetMoment (D n) (boundaryExposureW1 n) (boundaryResponsesW1 n) 1 ∧
      targetMoment (D n) (boundaryExposureW1 n) (boundaryResponsesW1 n) 0 ∧
      ∀ i, HasMean (D n) (fun z =>
        boundaryResponsesW1 n i (Function.update z i 1) -
          boundaryResponsesW1 n i (Function.update z i 0))) ∧
    weakLimit D (fun n z => (boundaryEstimatorW1 n z -
      populationContrast (D n) (boundaryExposureW1 n) (boundaryResponsesW1 n) 1 0)/
        boundaryScaleW1 n) fairSignLawW1 ∧
    probabilityLimit D (fun n _ => boundaryScaleW1 n / boundaryScaleW1 n) 1 ∧
    Tendsto (fun n => |populationContrast (D n) (boundaryExposureW1 n)
      (boundaryResponsesW1 n) 1 0 - boundaryDirectW1 n (D n)| / boundaryScaleW1 n)
      atTop (𝓝 0) ∧
    weakLimit D (fun n z => (boundaryEstimatorW1 n z - boundaryDirectW1 n (D n))/
      boundaryScaleW1 n) fairSignLawW1 ∧
    (∀ n, eventProbability (D n) (fun z => |boundaryEstimatorW1 n z -
      populationContrast (D n) (boundaryExposureW1 n) (boundaryResponsesW1 n) 1 0| ≤
        boundaryScaleW1 n) = 1 ∧
      eventProbability (D n) (fun z => |boundaryEstimatorW1 n z - boundaryDirectW1 n (D n)| ≤
        boundaryScaleW1 n) = 1/2) ∧
    Tendsto (fun n => eventProbability (D n) (fun z => |boundaryEstimatorW1 n z -
      populationContrast (D n) (boundaryExposureW1 n) (boundaryResponsesW1 n) 1 0| ≤
        boundaryScaleW1 n)) atTop (𝓝 1) ∧
    Tendsto (fun n => eventProbability (D n) (fun z => |boundaryEstimatorW1 n z -
      boundaryDirectW1 n (D n)| ≤ boundaryScaleW1 n)) atTop (𝓝 (1/2 : ℝ)) ∧
    (1 : ℝ) ≠ 1/2

/-- Atomic probability measure with every subset measurable. -/
noncomputable def atomicMeasureW1 {Ω : Type} (D : AtomicDesign Ω) : @Measure Ω ⊤ :=
  @Measure.sum Ω Ω ⊤ (fun z => ENNReal.ofReal (D.mass z) • @Measure.dirac Ω ⊤ z)

/-- Positive and negative extended expectations; these remain meaningful when infinite. -/
noncomputable def positiveExpectationW1 {Ω : Type} (D : AtomicDesign Ω) (f : Ω → ℝ) : ℝ≥0∞ :=
  ∑' z, ENNReal.ofReal (D.mass z * max (f z) 0)

noncomputable def negativeExpectationW1 {Ω : Type} (D : AtomicDesign Ω) (f : Ω → ℝ) : ℝ≥0∞ :=
  positiveExpectationW1 D (fun z => -f z)

noncomputable def positiveIntegralW1 {Ω : Type} (μ : @Measure Ω ⊤) (f : Ω → ℝ) : ℝ≥0∞ :=
  @lintegral Ω ⊤ μ (fun z => ENNReal.ofReal (max (f z) 0))

/-- Normalized restriction to a positive-probability cell; used only with a positive denominator. -/
noncomputable def conditionalMeasureW1 {Ω : Type} (D : AtomicDesign Ω) (A : Ω → Prop) :
    @Measure Ω ⊤ :=
  (ENNReal.ofReal (eventProbability D A))⁻¹ • (atomicMeasureW1 D).restrict {z | A z}

def realUnitVectorW1 (z : ℝ) : Fin 1 → ℝ := fun _ => z

/-- Existence-aware versions of Equations (5)–(8). -/
def OrdinaryEPOW1 {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g : Exposures Ω N)
    (y : Responses Ω N) (i : Fin N) (d a : ℝ) : Prop :=
  0 < exposureProbability D g i d ∧
  HasMean D (fun z => if g i z = d then y i z else 0) ∧ exposureMean D g y i d = a

def OrdinaryAEPOW1 {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g : Exposures Ω N)
    (y : Responses Ω N) (d a : ℝ) : Prop :=
  0 < N ∧ ∃ u : Fin N → ℝ, (∀ i, OrdinaryEPOW1 D g y i d (u i)) ∧
    a = (N : ℝ)⁻¹ * ∑ i, u i

def OrdinaryEEDW1 {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g : Exposures Ω N)
    (y : Responses Ω N) (i : Fin N) (d d' a : ℝ) : Prop :=
  ∃ u v : ℝ, OrdinaryEPOW1 D g y i d u ∧ OrdinaryEPOW1 D g y i d' v ∧ a = u-v

def OrdinaryAEEDW1 {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g : Exposures Ω N)
    (y : Responses Ω N) (d d' a : ℝ) : Prop :=
  ∃ u v : ℝ, OrdinaryAEPOW1 D g y d u ∧ OrdinaryAEPOW1 D g y d' v ∧ a = u-v

/-- The exact geometric witness already certified by the package. -/
def GeometricBaseW1 (D : AtomicDesign ℝ) : Prop :=
    D.mass = realIntegerMass ∧
    (∀ z, supported D z ↔ ∃ k : ℕ, (k : ℝ) = z) ∧
    positiveExposure D integerExposure 1 ∧ positiveExposure D integerExposure 0 ∧
    (exposureProbability D integerExposure 0 1 = 1/2 ∧
    exposureProbability D integerExposure 0 0 = 1/2 ∧
    exposureMean D integerExposure integerResponse 0 0 = 0 ∧
    ¬Summable (fun z : ℝ => D.mass z *
      (if integerExposure 0 z = 1 then integerResponse 0 z else 0)) ∧
    ¬HasMean D (estimateExposureMean D integerExposure integerResponse 1)) ∧
    HasMean D (fun z => if integerExposure 0 z=0 then integerResponse 0 z else 0) ∧
    (∀ k, integerResponseTerm D k = (-1 : ℝ)^k) ∧
    (∀ m : ℕ,
      (∑ k ∈ Finset.range (2*m), max (integerResponseTerm D k) 0) = (m : ℝ) ∧
      (∑ k ∈ Finset.range (2*m), max (-(integerResponseTerm D k)) 0) = (m : ℝ) ∧
      (∑ k ∈ Finset.range (2*m), |integerResponseTerm D k|) = 2*m ∧
      (∑ k ∈ Finset.range (2*m), integerResponseTerm D k) = 0 ∧
      (∑ k ∈ Finset.range (2*m+1), integerResponseTerm D k) = 1) ∧
    ¬Summable (fun k => max (integerResponseTerm D k) 0) ∧
    ¬Summable (fun k => max (-(integerResponseTerm D k)) 0) ∧
    (∀ z, estimateExposureMean D integerExposure integerResponse 1 z =
      2*integerResponse 0 z*(if integerExposure 0 z = 1 then 1 else 0)) ∧
    (∀ k, integerEstimatorTerm D k = 2*(-1 : ℝ)^k) ∧
    ¬Summable (fun k => max (integerEstimatorTerm D k) 0) ∧
    ¬Summable (fun k => max (-(integerEstimatorTerm D k)) 0)

/-- P061-T7; main Equations (5)–(8), pp. 6–7, supplement Equation (3), p. 2.
The one-unit real-assignment geometric design is a probability measure on the power set,
with identity assignment vector, nonnegative-integer support, finite raw responses and both
exposure probabilities 1/2. Its weighted positive-integer terms alternate +1,-1, giving all
stated finite sign-part sums and no limit of the ordered signed series. The exposure-one
numerator and conditional mean have both sign parts +infinity, whereas the exposure-zero
ordinary EPO is zero. The exposure-one EPO, AEPO, EED and AEED have no ordinary value.
The pointwise finite HT estimator has positive and negative expectations +infinity and no
ordinary finite expectation. The usual measure-theoretic conditions are assumed for existing
quantities; nonexistence of the claimed means is the conclusion being demonstrated. -/
def T7WholeStatement : Prop :=
  ∃ D : AtomicDesign ℝ, GeometricBaseW1 D ∧
    @IsProbabilityMeasure ℝ ⊤ (atomicMeasureW1 D) ∧
    (∀ A : Set ℝ, atomicMeasureW1 D A =
      ∑' z : ℝ, if z ∈ A then ENNReal.ofReal (D.mass z) else 0) ∧
    (∀ A : Set ℝ, (atomicMeasureW1 D A).toReal = eventProbability D (fun z => z ∈ A)) ∧
    Function.Bijective realUnitVectorW1 ∧
    (¬∃ a : ℝ, Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, integerResponseTerm D k)
      atTop (𝓝 a)) ∧
    positiveExpectationW1 D (fun z => if integerExposure 0 z = 1 then integerResponse 0 z else 0) = ⊤ ∧
    negativeExpectationW1 D (fun z => if integerExposure 0 z = 1 then integerResponse 0 z else 0) = ⊤ ∧
    positiveIntegralW1 (atomicMeasureW1 D)
      (fun z => if integerExposure 0 z = 1 then integerResponse 0 z else 0) = ⊤ ∧
    positiveIntegralW1 (atomicMeasureW1 D)
      (fun z => -(if integerExposure 0 z = 1 then integerResponse 0 z else 0)) = ⊤ ∧
    positiveIntegralW1 (conditionalMeasureW1 D (fun z => integerExposure 0 z = 1))
      (integerResponse 0) = ⊤ ∧
    positiveIntegralW1 (conditionalMeasureW1 D (fun z => integerExposure 0 z = 1))
      (fun z => -integerResponse 0 z) = ⊤ ∧
    (¬∃ a, OrdinaryEPOW1 D integerExposure integerResponse 0 1 a) ∧
    (¬∃ a, OrdinaryAEPOW1 D integerExposure integerResponse 1 a) ∧
    (¬∃ a, OrdinaryEEDW1 D integerExposure integerResponse 0 1 0 a) ∧
    (¬∃ a, OrdinaryAEEDW1 D integerExposure integerResponse 1 0 a) ∧
    OrdinaryEPOW1 D integerExposure integerResponse 0 0 0 ∧
    positiveExpectationW1 D (estimateExposureMean D integerExposure integerResponse 1) = ⊤ ∧
    negativeExpectationW1 D (estimateExposureMean D integerExposure integerResponse 1) = ⊤ ∧
    positiveIntegralW1 (atomicMeasureW1 D) (estimateExposureMean D integerExposure integerResponse 1) = ⊤ ∧
    positiveIntegralW1 (atomicMeasureW1 D) (fun z => -estimateExposureMean D integerExposure integerResponse 1 z) = ⊤ ∧
    (¬∃ a : ℝ, HasMean D (estimateExposureMean D integerExposure integerResponse 1) ∧
      mean D (estimateExposureMean D integerExposure integerResponse 1) = a)

end SAP.P061a
