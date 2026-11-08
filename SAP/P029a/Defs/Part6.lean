import SAP.P029a.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029a

universe u v

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

noncomputable section

/-- Additional numerical values in the two SEM witnesses. -/
def SEMWitnessMeans : Prop :=
  finiteConditionalMean semDefierWitnessMass
    (fun i => indicatorValue ((semDefierResponse i.1).receivedTreatment i.2))
    (fun i => i.2 = false) = 1/4 ∧
  finiteConditionalMean semDefierWitnessMass
    (fun i => indicatorValue ((semDefierResponse i.1).receivedTreatment i.2))
    (fun i => i.2 = true) = 3/4 ∧
  finiteCovariance semDefierWitnessMass (fun i => indicatorValue i.2)
    (fun i => (semDefierResponse i.1).observedOutcome i.2) /
    finiteCovariance semDefierWitnessMass (fun i => indicatorValue i.2)
      (fun i => indicatorValue ((semDefierResponse i.1).receivedTreatment i.2)) = 1 ∧
  finiteConditionalMean (fun _ : Fin 4 => 1/4)
    (fun i => indicatorValue ((semDependentResponse i).receivedTreatment (semDependentAssignment i)))
    (fun i => semDependentAssignment i = false) = 1/2 ∧
  finiteConditionalMean (fun _ : Fin 4 => 1/4)
    (fun i => indicatorValue ((semDependentResponse i).receivedTreatment (semDependentAssignment i)))
    (fun i => semDependentAssignment i = true) = 1 ∧
  finiteCovariance (fun _ : Fin 4 => 1/4) (fun i => indicatorValue (semDependentAssignment i))
    (fun i => (semDependentResponse i).y0) = 0 ∧
  finiteCovariance (fun _ : Fin 4 => 1/4) (fun i => indicatorValue (semDependentAssignment i))
    (fun i => (semDependentResponse i).observedOutcome (semDependentAssignment i)) /
    finiteCovariance (fun _ : Fin 4 => 1/4) (fun i => indicatorValue (semDependentAssignment i))
      (fun i => indicatorValue ((semDependentResponse i).receivedTreatment (semDependentAssignment i))) = 1 ∧
  finiteConditionalMean (fun _ : Fin 4 => 1/4)
    (fun i => if |(semDependentResponse i).y0| = 2 then 1 else 0)
    (fun i => semDependentAssignment i = true) = 1 ∧
  finiteConditionalMean (fun _ : Fin 4 => 1/4)
    (fun i => if |(semDependentResponse i).y0| = 2 then 1 else 0)
    (fun i => semDependentAssignment i = false) = 0

def HeterogeneousWitnessMeans : Prop :=
  finiteConditionalMean (bernoulliProductMass (fun _ : Bool => 1/2) (1/2))
    (fun i => (heterogeneousResponse i.1).treatmentEffect)
    (fun i => (heterogeneousResponse i.1).isComplier) = 3/2 ∧
  finiteCovariance (bernoulliProductMass (fun _ : Bool => 1/2) (1/2))
    (fun i => indicatorValue i.2)
    (fun i => indicatorValue ((heterogeneousResponse i.1).receivedTreatment i.2)) = 1/4 ∧
  (finiteConditionalMean (bernoulliProductMass (fun _ : Bool => 1/2) (1/2))
    (fun i => indicatorValue ((heterogeneousResponse i.1).receivedTreatment i.2)) (fun i => i.2 = true) -
  finiteConditionalMean (bernoulliProductMass (fun _ : Bool => 1/2) (1/2))
    (fun i => indicatorValue ((heterogeneousResponse i.1).receivedTreatment i.2)) (fun i => i.2 = false)) = 1 ∧
  (∀ t : Bool, finiteProbability (bernoulliProductMass (fun _ : Bool => 1/2) (1/2))
    (fun i => (heterogeneousResponse i.1).treatmentEffect = if t then 2 else 1) = 1/2)

/-- Polynomial certificates for the four closed-domain likelihood bounds. -/
def ClosedLikelihoodCertificates : Prop :=
  ∀ p q : ℝ,
    1 - (1-p)*(1-q) = p + (1-p)*q ∧
    1/4 - (1-p)*q = (p-1/2)^2 + (1-p)*(p-q) ∧
    1 - p*(1-q) = (1-p) + p*q ∧
    1 - p*q = (1-p) + p*(1-q)

def ClosedFitValues : Prop :=
  twoReceiptFit (false,false) = (0,0) ∧
  twoReceiptFit (false,true) = (1/2,1/2) ∧
  twoReceiptFit (true,false) = (1,0) ∧
  twoReceiptFit (true,true) = (1,1) ∧
  (∀ d, twoReceiptLikelihood d (twoReceiptFit d).1 (twoReceiptFit d).2 =
    if d.1 = false ∧ d.2 = true then 1/4 else 1) ∧
  twoReceiptMass (false,false) = 3/16 ∧ twoReceiptMass (false,true) = 1/16 ∧
  twoReceiptMass (true,false) = 9/16 ∧ twoReceiptMass (true,true) = 3/16

/-- T1: the complete six-atom refutation of the printed ordering. -/
def T1Statement : Prop :=
  IgnorabilityWitnessFacts ∧ PotentialPairIndependence ∧ IgnorabilityWitnessMeans

/-- T2 retains the full IV bundle as an explicit premise of the one-sided implication. -/
def T2Statement : Prop :=
  IgnorabilityIncomparability ∧ BaselineSelectionFacts ∧ BaselineEffectFacts ∧ OneSidedImplication.{u,v}

/-- T3: both independence readings have the stated population counterexamples. -/
def T3Statement : Prop :=
  MarginalWitnessFacts ∧ MarginalNestedProbabilities ∧ ConditionalWitnessFacts ∧
  ConditionalWitnessDependence ∧ IndependenceWitnessMeans ∧ IndependenceWitnessNumbers

/-- T4 concerns population ratios; it makes no sampling convergence assertion. -/
def T4Statement : Prop :=
  WeightedPopulationIdentities.{u,v} ∧ JointIndependenceSufficiency.{u,v} ∧
  MarginalWitnessFacts ∧ ConditionalWitnessFacts ∧ IndependenceWitnessMeans

/-- T5 includes actual outcome cross-products and positive-weight coefficient recovery. -/
def T5Statement : Prop :=
  NoiseScoringWitnessFacts ∧ NoiseDesignDeterminant ∧ NoiseWitnessAdmissibility ∧
  PositiveWeightRecovery ∧ NoiseCrossProductFacts ∧ ConstantRunScoringFacts

/-- T6 includes every positive replicate count by the defining formula of RMSE. -/
def T6Statement : Prop :=
  (∀ y : ℝ, (y + 5) - y = 5) ∧ ConstantSampleEffect ∧ ConstantPopulationEffect.{u} ∧
  CorrectedRMSE ∧ UniformCovariateMoments ∧ BenchmarkMoments.{u} ∧ SquaredErrorIdentity ∧
  FiniteRunErrorIdentity ∧ FiniteExpectedErrorIdentity.{u} ∧ ExpectedErrorIdentity.{u} ∧
  NoiseScoringWitnessFacts ∧ NoiseWitnessAdmissibility

/-- T7 does not identify its prescribed scores or receipt rates as fitted optima. -/
def T7Statement : Prop :=
  InsideLogWeightIdentity.{u} ∧ InsideLogMinimumInvariance.{u,v} ∧ ZeroWeightContribution ∧
  ZeroWeightObjective.{u} ∧ SpecifiedScoreWaldFacts ∧ SpecifiedTwoSidedFacts ∧
  SpecifiedPerturbationFacts ∧ PerturbationDerivatives

/-- T8 proves likelihood fitting for free cell probabilities. -/
def T8Statement : Prop :=
  ZeroAndUnitWeights.{u} ∧ IntegerWeightReplication.{u} ∧ CellStrictConcavity ∧ CellUniqueMaximum ∧
  FreeCellUniqueMinimum.{u,v} ∧ ConcreteFreeCellFits ∧ ConstantWeightEquivalence.{u,v} ∧
  SpecifiedScoreWaldFacts ∧ SpecifiedTwoSidedFacts ∧ SpecifiedPerturbationFacts

/-- Both directions of the compliance/race comparisons have opposite signs in the completions. -/
def RaceReverseComparisons : Prop :=
  (finiteConditionalMean recordMass (fun i => indicatorValue (raceCompletionA i))
      (fun i => recordedContact i = true) >
    finiteConditionalMean recordMass (fun i => indicatorValue (raceCompletionA i))
      (fun i => recordedContact i = false)) ∧
  (finiteConditionalMean recordMass (fun i => indicatorValue (raceCompletionB i))
      (fun i => recordedContact i = true) <
    finiteConditionalMean recordMass (fun i => indicatorValue (raceCompletionB i))
      (fun i => recordedContact i = false))

/-- T9 retains the explicit binary-label-compatible completions and arbitrary raw-code preservation. -/
def T9Statement : Prop :=
  RaceCompletionFacts ∧ RawRaceCodePreservation ∧ RecordedAssignmentSupport ∧ RaceReverseComparisons

/-- T10 retains finite count algebra, the stated rate comparisons, and the covariance identity. -/
def T10Statement : Prop :=
  BinaryPopulationSign ∧ RaleighContactComparisons ∧ RaceCompletionFacts ∧
  RecordedAssignmentSupport ∧ GroupedCovarianceIdentity.{u}

/-- T11: both finite SEM counterexamples with all their explicit moment values. -/
def T11Statement : Prop := SEMDefierFacts ∧ SEMDependenceFacts ∧ SEMWitnessMeans

/-- T12: SEM and IV assumptions are non-nested, including the all-complier LATE. -/
def T12Statement : Prop :=
  SEMDefierFacts ∧ SEMDependenceFacts ∧ SEMConstantEffect.{u,v} ∧ HeterogeneousIVFacts ∧
  HeterogeneousWitnessMeans

/-- T13 uses closed receipt probabilities and natural powers, including the boundary convention. -/
def T13Statement : Prop :=
  SaturatedBiasWitnessFacts ∧ SaturatedScoreBiasFacts ∧ FivePerArmBiasFacts ∧
  ClosedLikelihoodCertificates ∧ ClosedFitValues

end
end SAP.P029a
