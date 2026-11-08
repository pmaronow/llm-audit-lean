import Mathlib
import SAP.P011a.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

def T7Statement : Prop := DegreeOnlyIdentity ∧ DegreeOnlyBounds ∧
  DegreeOnlyConservative ∧ UnboundedDegreeGap ∧ SignWitnessFacts

def T8Statement : Prop := RevisedCorollaries ∧ OracleSpecialCases ∧
  CycleCounterexample ∧ PathCounterexample

def T9Statement : Prop := ResidualRootRate ∧ ResidualPrediction ∧
  ResidualMisspecification ∧ ResidualFailure ∧ ResidualPerturbation

def T10Statement : Prop := UniversalImpossibility ∧ MixtureMoments

def T11Statement : Prop := AlternatingCounterexample ∧ AlternatingMoments ∧
  (∀ k y, V2star (alternatingFamily.model k) y =
    V2 (alternatingFamily.model k).G (weighted (alternatingFamily.model k) y) ∧
    (alternatingFamily.size k : ℝ)*V2 (alternatingFamily.model k).G
      (weighted (alternatingFamily.model k) y) = sampleVariance (weighted (alternatingFamily.model k) y) ∧
    (alternatingFamily.size k : ℝ)*V2star (alternatingFamily.model k) y - scaledTrue alternatingFamily k =
      meanSpread (alternatingFamily.model k) + varianceRemainder (alternatingFamily.model k) y)

def T12Statement : Prop := HomoskedasticRepair ∧ HomoskedasticIdentities

def T13Statement : Prop := MatchingReduction ∧ MatchingCounts ∧ MatchingInstances

def T14Statement : Prop := RelaxationUpperBound ∧ RelaxationGaps ∧
  RelaxationProgramValues ∧ RelaxationNamedWitness

end
end SAP.P011a
