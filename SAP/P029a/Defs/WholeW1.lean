import Mathlib
import SAP.P029a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029a

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology

universe u v

noncomputable section

/-- The randomized binary-IV setting, before imposing no defiers or relevance.
Measurability and integrability are the usual measure-theoretic conditions. -/
structure WholeIVCore {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialResponse X) (Z : Ω → Bool) : Prop where
  covariate_measurable : Measurable (fun ω => (U ω).x)
  d0_measurable : Measurable (fun ω => (U ω).d0)
  d1_measurable : Measurable (fun ω => (U ω).d1)
  y0_measurable : Measurable (fun ω => (U ω).y0)
  y1_measurable : Measurable (fun ω => (U ω).y1)
  assignment_measurable : Measurable Z
  y0_integrable : Integrable (fun ω => (U ω).y0) μ
  y1_integrable : Integrable (fun ω => (U ω).y1) μ
  randomized : IndepFun Z (fun ω => ((U ω).x, (U ω).d0, (U ω).d1,
    (U ω).y0, (U ω).y1)) μ
  assignment_pos : 0 < eventProbability μ {ω | Z ω = true}
  assignment_lt_one : eventProbability μ {ω | Z ω = true} < 1

/-- The three positive type masses of each of the two fixed six-atom witnesses. -/
def WholeTypeMasses : Prop :=
  ∀ R ∈ ({ignorabilityResponse, baselineResponse} : Set (Fin 3 → PotentialResponse Unit)),
    finiteProbability sixAtomMass (fun i => (R i.1).isComplier) = 1/2 ∧
    finiteProbability sixAtomMass (fun i => (R i.1).d0 = true ∧ (R i.1).d1 = true) = 1/4 ∧
    finiteProbability sixAtomMass (fun i => (R i.1).d0 = false ∧ (R i.1).d1 = false) = 1/4

/-- Positive-mass-profile one-sided implication, without separately assuming no defiers
or global relevance. Both follow from these premises. -/
def WholeOneSidedImplication : Prop :=
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialResponse X) (Z : Ω → Bool),
    WholeIVCore μ U Z → (∀ᵐ ω ∂μ, (U ω).d0 = false) →
    ∀ x, 0 < eventProbability μ {ω | (U ω).x = x} →
      0 < complianceProbability μ U x → ReceiptMeanEquality μ U Z x →
      LatentMeanEquality μ U x

/-- P029-T2; Section 3.4, p. 499 (PDF p. 8), comparison following Assumption 1.
The two ignorability conditions are incomparable, as witnessed by the stated six-atom laws
with type masses (1/2, 1/4, 1/4). The baseline-selection law has constant effect one and
received-treatment means (1/2, 0) and (3/2, 1). Under randomized one-sided noncompliance,
received-treatment ignorability implies latent ignorability at every positive-mass profile
with positive compliance. The usual measure-theoretic conditions are assumed. -/
def T2WholeStatement : Prop :=
  IgnorabilityWitnessFacts ∧ IgnorabilityIncomparability ∧ BaselineSelectionFacts ∧
    BaselineEffectFacts ∧ WholeTypeMasses ∧ WholeOneSidedImplication.{u,v}

/-- For T4, `X` enumerates the finite positive-mass support, called Ω in the claim.
Thus `profile_mass` expresses the choice of support, rather than an overlap restriction.
No defiers is imposed almost surely; relevance is a consequence, not a premise. -/
structure WholeFiniteModel {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialResponse X) (Z : Ω → Bool)
    : Prop extends WholeIVCore μ U Z where
  no_defiers : μ {ω | (U ω).isDefier} = 0
  profile_mass : ∀ x, 0 < eventProbability μ {ω | (U ω).x = x}
  score_pos : ∀ x, 0 < complianceProbability μ U x

/-- All five population identities and the separate ATE sufficiency implications. -/
def WholeWeightedFormulas {Ω X : Type*} [MeasurableSpace Ω] [Fintype X]
    (μ : Measure Ω) (U : Ω → PotentialResponse X) (Z : Ω → Bool) (w : X → ℝ) : Prop :=
  populationWald μ U Z (fun ω => w (U ω).x) =
    (∫ ω, w (U ω).x * (if (U ω).isComplier then (U ω).treatmentEffect else 0) ∂μ) /
    (∫ ω, w (U ω).x * (if (U ω).isComplier then 1 else 0) ∂μ) ∧
  populationWald μ U Z (fun ω => w (U ω).x) =
    (∑ x, eventProbability μ {ω | (U ω).x = x} * w x * complianceProbability μ U x * complierMeanEffect μ U x) /
    (∑ x, eventProbability μ {ω | (U ω).x = x} * w x * complianceProbability μ U x) ∧
  populationWald μ U Z (fun _ => 1) =
    eventMean μ (fun ω => (U ω).treatmentEffect) {ω | (U ω).isComplier} ∧
  populationWald μ U Z (fun ω => 1 / complianceProbability μ U (U ω).x) =
    ∑ x, eventProbability μ {ω | (U ω).x = x} * complierMeanEffect μ U x ∧
  populationWald μ U Z (fun _ => 1) -
      populationWald μ U Z (fun ω => 1 / complianceProbability μ U (U ω).x) =
    populationCovariance μ (fun ω => complianceProbability μ U (U ω).x)
      (fun ω => complierMeanEffect μ U (U ω).x) / eventProbability μ {ω | (U ω).isComplier} ∧
  (eventMean μ (fun ω => (U ω).treatmentEffect) {ω | (U ω).isComplier} =
      (∫ ω, (U ω).treatmentEffect ∂μ) →
    populationWald μ U Z (fun _ => 1) = (∫ ω, (U ω).treatmentEffect ∂μ)) ∧
  ((∀ x, LatentMeanEquality μ U x) →
    populationWald μ U Z (fun ω => 1 / complianceProbability μ U (U ω).x) =
      (∫ ω, (U ω).treatmentEffect ∂μ))

/-- The two mean-equality premises in the corrected sufficiency assertion. -/
def WholeMeanPremises {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (U : Ω → PotentialResponse X) : Prop :=
  eventMean μ (fun ω => (U ω).treatmentEffect) {ω | (U ω).isComplier} =
    (∫ ω, (U ω).treatmentEffect ∂μ) ∧ ∀ x, LatentMeanEquality μ U x

/-- The two alternative joint-independence hypotheses in clause (vii). -/
def WholeJointIndependence {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialResponse X) : Prop :=
  IndepFun (fun ω => (U ω).treatmentEffect)
      (fun ω => (decide (U ω).isComplier, (U ω).x)) μ ∨
    IndepFun (fun ω => decide (U ω).isComplier)
      (fun ω => ((U ω).treatmentEffect, (U ω).x)) μ

/-- The full finite-support population assertion; the probability space is unrestricted. -/
def WholeFinitePopulation : Prop :=
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialResponse X) (Z : Ω → Bool),
    WholeFiniteModel μ U Z →
    (∀ w : X → ℝ, (∀ x, 0 < w x) → WholeWeightedFormulas μ U Z w) ∧
    (WholeJointIndependence μ U → WholeMeanPremises μ U ∧
      populationWald μ U Z (fun _ => 1) = (∫ ω, (U ω).treatmentEffect ∂μ) ∧
      populationWald μ U Z (fun ω => 1 / complianceProbability μ U (U ω).x) =
        (∫ ω, (U ω).treatmentEffect ∂μ))

/-- The entire observed and potential tuple to which iid sampling refers. -/
def wholeJoint {Ω X : Type*} (U : Ω → PotentialResponse X) (Z : Ω → Bool) (ω : Ω) :=
  ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1, Z ω)

/-- Independent, identically distributed measurable copies; no independence between the
sample and the estimated compliance scores is required. -/
structure WholeIID {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : ℕ → Ω → PotentialResponse X) (Z : ℕ → Ω → Bool) : Prop where
  measurable : ∀ i, Measurable (wholeJoint (U i) (Z i))
  independent : iIndepFun (fun i => wholeJoint (U i) (Z i)) μ
  identical : ∀ i, IdentDistrib (wholeJoint (U i) (Z i)) (wholeJoint (U 0) (Z 0)) μ μ

/-- Cell indices are profile, assignment arm, and moment (0 = 1, 1 = Y, 2 = D). -/
abbrev WholeCellIndex (X : Type*) := X × Bool × Fin 3

/-- The three moments entering the intercept-only weighted IV ratio. -/
def wholeObservation {X : Type*} (U : PotentialResponse X) (z : Bool) (k : Fin 3) : ℝ :=
  if k = 0 then 1 else if k = 1 then U.observedOutcome z else indicatorValue (U.receivedTreatment z)

/-- Raw cell moments in the population. Integrability follows from the model's conditions. -/
def wholePopulationCells {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (U : Ω → PotentialResponse X) (Z : Ω → Bool)
    (c : WholeCellIndex X) : ℝ :=
  ∫ ω in {ω | (U ω).x = c.1 ∧ Z ω = c.2.1}, wholeObservation (U ω) (Z ω) c.2.2 ∂μ

/-- Empirical cell moments for the nonempty sample of size n+1. -/
def wholeEmpiricalCells {Ω X : Type*} (U : ℕ → Ω → PotentialResponse X)
    (Z : ℕ → Ω → Bool) (n : ℕ) (ω : Ω) (c : WholeCellIndex X) : ℝ :=
  (∑ i : Fin (n+1), if (U i.val ω).x = c.1 ∧ Z i.val ω = c.2.1
    then wholeObservation (U i.val ω) (Z i.val ω) c.2.2 else 0) / (n+1 : ℕ)

/-- Weighted arm moment obtained by summing the profile cells. -/
def wholeCellArm {X : Type*} [Fintype X] (a : WholeCellIndex X → ℝ)
    (w : X → ℝ) (z : Bool) (k : Fin 3) : ℝ := ∑ x, w x * a (x,z,k)

/-- The weighted Wald ratio. Normalizing each arm by its weight total is exactly the
sample estimator in S7 after grouping observations by profile. Division uses zero at a
zero denominator; this only specifies otherwise undefined finite-sample values. -/
def wholeCellWald {X : Type*} [Fintype X] (a : WholeCellIndex X → ℝ) (w : X → ℝ) : ℝ :=
  (wholeCellArm a w true 1 / wholeCellArm a w true 0 -
    wholeCellArm a w false 1 / wholeCellArm a w false 0) /
  (wholeCellArm a w true 2 / wholeCellArm a w true 0 -
    wholeCellArm a w false 2 / wholeCellArm a w false 0)

/-- Precisely the nonzero population denominators required for continuous division. -/
def WholeWaldDomain {X : Type*} [Fintype X]
    (a : WholeCellIndex X → ℝ) (w : X → ℝ) : Prop :=
  wholeCellArm a w true 0 ≠ 0 ∧ wholeCellArm a w false 0 ≠ 0 ∧
    wholeCellArm a w true 2 / wholeCellArm a w true 0 -
      wholeCellArm a w false 2 / wholeCellArm a w false 0 ≠ 0

/-- Profile-based inverse-score estimator, expressed as finite cell sums.
Using score one gives the ordinary intercept-only IV/Wald (bivariate 2SLS) estimator. -/
def wholeSampleWald {Ω X : Type*} [Fintype X] (U : ℕ → Ω → PotentialResponse X)
    (Z : ℕ → Ω → Bool) (s : ℕ → Ω → X → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  wholeCellWald (wholeEmpiricalCells U Z n ω) (fun x => 1 / s n ω x)

/-- Sampling limits and ATE consistency under the separate mean-equality premises.
The score estimates are arbitrary measurable functions of the same sample (and may use
additional randomness), consistent at each supported profile. No rate or moment assumption
on estimated scores, and no nonzero-denominator condition on every sample, is imposed. -/
def WholeFiniteSampling : Prop :=
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → PotentialResponse X)
    (Z : ℕ → Ω → Bool), WholeFiniteModel μ (U 0) (Z 0) → WholeIID μ U Z →
    ∀ s : ℕ → Ω → X → ℝ, (∀ n x, Measurable (fun ω => s n ω x)) →
      (∀ x, TendstoInMeasure μ (fun n ω => s n ω x) atTop
        (fun _ => complianceProbability μ (U 0) x)) →
    TendstoInMeasure μ (wholeSampleWald U Z (fun _ _ _ => 1)) atTop
      (fun _ => populationWald μ (U 0) (Z 0) (fun _ => 1)) ∧
    TendstoInMeasure μ (wholeSampleWald U Z s) atTop
      (fun _ => populationWald μ (U 0) (Z 0)
        (fun ω => 1 / complianceProbability μ (U 0) (U 0 ω).x)) ∧
    (eventMean μ (fun ω => (U 0 ω).treatmentEffect) {ω | (U 0 ω).isComplier} =
        (∫ ω, (U 0 ω).treatmentEffect ∂μ) →
      TendstoInMeasure μ (wholeSampleWald U Z (fun _ _ _ => 1)) atTop
        (fun _ => ∫ ω, (U 0 ω).treatmentEffect ∂μ)) ∧
    ((∀ x, LatentMeanEquality μ (U 0) x) →
      TendstoInMeasure μ (wholeSampleWald U Z s) atTop
        (fun _ => ∫ ω, (U 0 ω).treatmentEffect ∂μ))

/-- P029-T4; Section 3.4, p. 499 (PDF p. 8), corrected heterogeneous-effect sufficiency
statement; Appendix equations (10) and (13), p. 504 (PDF p. 13).
For finite positive-mass covariate support, the weighted Wald identities, LATE and true-score
ICSW formulas, covariance gap, separate ATE sufficiency implications, both separation laws,
and both joint-independence sufficient conditions hold. For iid sampling and measurable
profile-based consistent score estimates, ordinary IV and estimated-score ICSW converge in
probability to the respective population ratios. The respective mean-equality premises give
ATE consistency; imposing both gives consistency of both estimators. The usual
measure-theoretic conditions are assumed. -/
def T4WholeStatement : Prop :=
  WholeFinitePopulation.{u,v} ∧ MarginalWitnessFacts ∧ ConditionalWitnessFacts ∧
    IndependenceWitnessMeans ∧ WholeFiniteSampling.{u,v}

/-- Standard normal CDF used by the package's probit link. -/
def wholePhi (t : ℝ) : ℝ := cdf (gaussianReal 0 1) t

/-- Intercept and binary-profile slope, with finite real coefficients. -/
def wholeBinaryProbit (β : ℝ × ℝ) (x : Bool) : ℝ :=
  wholePhi (β.1 + β.2 * indicatorValue x)

/-- Two nested probit equations for always-or-complier and conditional always-taker. -/
def wholeNestedProbit (β : (ℝ × ℝ) × (ℝ × ℝ)) (c : Bool × Bool) : ℝ :=
  nestedReceiptProbability (wholeBinaryProbit β.1 c.1) (wholeBinaryProbit β.2 c.1) c.2

/-- The package's receipt-probability clipping, in exact real arithmetic. -/
def wholeClipReceipt (q : ℝ) : ℝ := max (1/100000) (min (1-1/100000) q)

def wholeClippedNestedProbit (β : (ℝ × ℝ) × (ℝ × ℝ)) (c : Bool × Bool) : ℝ :=
  wholeClipReceipt (wholeNestedProbit β c)

/-- Bernoulli negative weighted log likelihood as a function of cell probabilities. -/
def wholeCellObjective {I C : Type*} [Fintype I] (cell : I → C)
    (D : I → Bool) (w : I → ℝ) (q : C → ℝ) : ℝ :=
  observationWeightedObjective (fun i => bernoulliContribution (q (cell i)) (D i)) w

/-- The two-sided source objective: observation weights are inside the logarithm. -/
def wholePackageCellObjective {I C : Type*} [Fintype I] (cell : I → C)
    (D : I → Bool) (w : I → ℝ) (q : C → ℝ) : ℝ :=
  insideLogObjective (fun i => bernoulliContribution (q (cell i)) (D i)) w

/-- The one-sided source fit ignores its supplied observation-weight argument. -/
def wholeOneSidedPackageObjective (_w : Bool × Fin 4 → ℝ) (q : Bool → ℝ) : ℝ :=
  wholeCellObjective Prod.fst treatedReceipt (fun _ => 1) q

/-- Existence of finite model coefficients attaining the fit, global optimality, and
uniqueness of fitted probabilities (coefficients themselves need not be unique). -/
def WholeRealizedMinimum {Θ C : Type*} (rate : Θ → C → ℝ) (qhat : C → ℝ)
    (Q : (C → ℝ) → ℝ) : Prop :=
  (∃ θ, rate θ = qhat) ∧ ∀ θ, Q qhat ≤ Q (rate θ) ∧
    (Q qhat = Q (rate θ) ↔ rate θ = qhat)

/-- Every pair of interior probabilities has finite intercept/slope probit coefficients. -/
def WholeBinaryProbitSaturation : Prop :=
  ∀ q : Bool → ℝ, (∀ x, q x ∈ Ioo (0 : ℝ) 1) → ∃ β, wholeBinaryProbit β = q

/-- Every ordered raw receipt array is realized by the two nested probit equations.
The universal realization concerns raw probabilities, before the source's clipping. -/
def WholeNestedProbitSaturation : Prop :=
  ∀ q : Bool × Bool → ℝ,
    (∀ x, 0 < q (x,false) ∧ q (x,false) < q (x,true) ∧ q (x,true) < 1) →
    ∃ β, wholeNestedProbit β = q

/-- The unweighted source fit and the observation-weighted fit for the one-sided sample. -/
def WholeOneSidedFits : Prop :=
  (∀ w : Bool × Fin 4 → ℝ, (∀ i, 0 < w i) →
    WholeRealizedMinimum wholeBinaryProbit specifiedUnweightedScores (wholeOneSidedPackageObjective w)) ∧
  WholeRealizedMinimum wholeBinaryProbit specifiedWeightedScores
    (wholeCellObjective Prod.fst treatedReceipt treatedWeight)

/-- Both clipped nested-probit fits for the four-cell two-sided witness. -/
def WholeTwoSidedFits : Prop :=
  (∀ w : (Bool × Bool) × Fin 4 → ℝ, (∀ i, 0 < w i) →
    WholeRealizedMinimum wholeClippedNestedProbit specifiedInsideLogRates
      (wholePackageCellObjective Prod.fst twoSidedReceipt w)) ∧
  WholeRealizedMinimum wholeClippedNestedProbit specifiedWeightedRates
    (wholeCellObjective Prod.fst twoSidedReceipt twoSidedObservationWeight)

/-- Actual refitting at each positive perturbation and derivatives of the resulting
Wald-estimate functions, not just of prescribed rational comparison functions. -/
def WholePerturbationFits : Prop :=
  (∀ t : ℝ, 0 < t → WholeRealizedMinimum wholeBinaryProbit (specifiedPerturbedScores t)
    (wholeCellObjective Prod.fst treatedReceipt (treatedPerturbationWeight t))) ∧
  HasDerivAt (fun t : ℝ =>
    finiteWald (fun _ : Bool × Bool × Fin 4 => 1/16) weightWitnessResponse weightWitnessAssignment
      (fun i => perturbedRecordWeight t i / specifiedPerturbedScores t i.1)) (-1/16) 1 ∧
  HasDerivAt (fun t : ℝ =>
    finiteWald (fun _ : Bool × Bool × Fin 4 => 1/16) weightWitnessResponse weightWitnessAssignment
      (fun i => perturbedRecordWeight t i / specifiedUnweightedScores i.1)) 0 1

/-- The remaining two unweighted compliance-score values in the two-sided witness. -/
def WholeTwoSidedScoreValues : Prop :=
  specifiedInsideLogRates (false,true) - specifiedInsideLogRates (false,false) = 1/4 ∧
  specifiedInsideLogRates (true,true) - specifiedInsideLogRates (true,false) = 1/2

/-- P029-T7; package icsw 1.0.0, compliance.score.R lines 43–48 and 81–92,
icsw.tsls.R lines 28–37 and package help; article Section 3.3, p. 498 (PDF p. 7).
Positive weights inside the logarithm leave all minimizers unchanged; a zero weight gives
infinite extended objective. In the sixteen-record one-sided witness, the actual unweighted
and weighted probit fits have scores (1/4,3/4) and (3/4,27/28), giving Wald estimates 3/2 and
17/10. Every ordered raw two-sided receipt array has finite nested-probit coefficients;
the stated two-sided arrays are the actual clipped package and corrected fits, with the
stated score differences and likelihood ratio. Under the positive weight perturbation,
actual refitting yields scores (1/(3+t),3/4) and the stated Wald curve with derivative
-1/16 at one, while the fixed-score estimate has derivative zero. These facts refute the
package help's interpretation that the supplied weights refit the compliance model.
The usual measure-theoretic conditions are assumed. -/
def T7WholeStatement : Prop :=
  T7Statement.{u,v} ∧ WholeBinaryProbitSaturation ∧ WholeNestedProbitSaturation ∧
    WholeOneSidedFits ∧ WholeTwoSidedFits ∧ WholePerturbationFits ∧ WholeTwoSidedScoreValues

end
end SAP.P029a
