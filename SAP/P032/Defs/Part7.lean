import SAP.P032.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P032

open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory Filter

noncomputable section

variable {R M P : Type*} [Fintype R] [Fintype M] [Fintype P]
  [DecidableEq R] [DecidableEq M] [DecidableEq P]

def survivalRiskSetsStatement : Prop :=
  (Finset.univ.filter (fun r : Fin 10 => survivalAtRisk r 1)) = {0,1,2,4,6,8} ∧
    (Finset.univ.filter (fun r : Fin 10 => survivalAtRisk r 2)) = {3,5,7,9}

def survivalScoresStatement : Prop :=
  survivalRiskCount 1 = 6 ∧ survivalRiskCount 2 = 4 ∧ survivalEventCount 1 = 2 ∧ survivalEventCount 2 = 2 ∧
    survivalRiskMean 1 = 0 ∧ survivalRiskMean 2 = 0 ∧ survivalInformation = 12 ∧
    (∀ r, survivalEfficientScore r = survivalScores r) ∧ (∑ r, survivalScores r) = 0

def survivalSubjectTotalsStatement : Prop :=
  (fun k : Fin 6 => ∑ r, if (survivalRecords r).id = k then survivalScores r else 0) =
      ![2/3,-2/3,7/6,-7/6,-5/6,5/6]

def survivalComponentsStatement : Prop :=
  recordScalarCovariance survivalInfluence = 19/432 ∧
    clusterScalarCovariance (fun r => (survivalRecords r).id) survivalInfluence = 5/144 ∧
    (fun i => memberScalarCovariance (fun r => (survivalRecords r).dyad) i survivalInfluence) =
      ![25/864,59/2592,89/2592,185/2592] ∧
    (∑ i : Fin 4, memberScalarCovariance (fun r => (survivalRecords r).dyad) i survivalInfluence) = 17/108

def survivalDiscrepancyStatement : Prop :=
  quadForm (fun r s => dyadicMask (fun r => (survivalRecords r).dyad) r s)
      survivalInfluence = 5/144 ∧
    (17/108 : ℝ)-5/144-2*(19/432) = 5/144 ∧
    (17/108 : ℝ)-5/144-2*(5/144) = 23/432 ∧
    (23/432 : ℝ)-(5/144) = 8/432 ∧
    ((10-1 : ℝ)/10)*(6/(6-1)) = 27/25 ∧
    (17/108 : ℝ)-5/144-2*((27/25)*(5/144)) = 103/2160 ∧
    (5/144 : ℝ) ≠ 23/432 ∧ (5/144 : ℝ) ≠ 103/2160 ∧
    (0 : ℝ) < 5/144 ∧ (0 : ℝ) < 23/432 ∧ (0 : ℝ) < 103/2160

def survivalFitStatement : Prop :=
  (∀ β, survivalLogLikelihood β = survivalClosedLikelihood β) ∧
    (∀ β, β ≠ 0 → survivalLogLikelihood β < survivalLogLikelihood 0)

def survivalPartitionStatement : Prop :=
  subjectMask (fun r => (survivalRecords r).id) = repeatedMask (fun r => (survivalRecords r).dyad)

def tenFitStatement : Prop :=
  tenDesignMatrix.transpose * tenDesignMatrix = !![10,2;2,42] ∧
    tenBreadMatrix * (tenDesignMatrix.transpose * tenDesignMatrix) = 1 ∧
    tenBreadMatrix = olsBread tenDesignMatrix ∧ tenDesignMatrix.transpose *ᵥ tenResponse = ![4,4] ∧
    leastSquares tenDesignMatrix tenResponse = ![5/13,1/13] ∧ fitResidual tenDesignMatrix tenResponse = tenResidualValues ∧
    tenDesignMatrix.transpose *ᵥ tenResidualValues = 0

def tenVarianceStatement : Prop :=
  tenDyadicMeat = (1/169 : ℝ) • !![1984,-1108;-1108,50] ∧
    scoreCovariance recordMask tenScoreValues = (1/169 : ℝ) • !![3744,4052;4052,15584] ∧
    tenCovariance = (1/3655808 : ℝ) • !![460765,-79681;-79681,7157]

def tenGateFailureStatement : Prop :=
  (∀ i : Fin 2, 0 < tenCovariance i i) ∧
    tenCovariance.det = -70529/308915776 ∧
    quadForm tenCovariance ![1,6] = -237755/3655808 ∧
    ¬tenCovariance.PosSemidef ∧
    (∀ hV : tenCovariance.IsHermitian, diagonalGate tenCovariance hV = tenCovariance) ∧
    quadForm ((5/4 : ℝ) • tenCovariance) ![1,6] = -1188775/14623232

def tenDecompositionStatement : Prop :=
  (∑ m : Fin 5, scoreCovariance (memberMask tenDyadData m) tenScoreValues)-
      scoreCovariance recordMask tenScoreValues-
      (3 : ℝ) • scoreCovariance recordMask tenScoreValues = tenDyadicMeat

def imputationFitsStatement : Prop :=
  imputationProbability false = 1/2 ∧ imputationProbability true = 3/4 ∧
    imputationEstimate false = 0 ∧ imputationEstimate true = Real.log 3 ∧
    imputationInformation false = 6 ∧ imputationInformation true = 9/2 ∧
    imputationDyadCovariance false = 2/9 ∧ imputationDyadCovariance true = 8/81 ∧
    imputationRecordCovariance false = 1/6 ∧ imputationRecordCovariance true = 2/9 ∧
    (∀ i, imputationMemberCovariance false i = 7/36) ∧
    (fun i => imputationMemberCovariance true i) = ![5/27,5/27,11/81,11/81] ∧
    ((∑ i, imputationMemberCovariance false i)-imputationDyadCovariance false-2*imputationRecordCovariance false) = 2/9 ∧
    ((∑ i, imputationMemberCovariance true i)-imputationDyadCovariance true-2*imputationRecordCovariance true) = 8/81

def imputationBetweenStatement : Prop :=
  estimateAverage fiveEstimates 0 = (2/5 : ℝ)*Real.log 3 ∧
    betweenCovariance fiveEstimates 0 0 = (3/10 : ℝ)*(Real.log 3)^2 ∧
    rubinContribution fiveEstimates 0 0 = (9/25 : ℝ)*(Real.log 3)^2

def imputationGapStatement : Prop :=
  correctPooledVariance = 14/81+(9/25 : ℝ)*(Real.log 3)^2 ∧
    codePooledVariance = 14/81+(441/1300 : ℝ)*(Real.log 3)^2 ∧
    codePooledVariance-correctPooledVariance = -(27/1300 : ℝ)*(Real.log 3)^2 ∧
    codePooledVariance < correctPooledVariance ∧ 0 < codePooledVariance ∧ 0 < correctPooledVariance ∧
    (4*(12/13 : ℝ)-5/6-2*(23/24)) = 49/52

def imputationPartitionStatement : Prop :=
  Fintype.card (Fin 6 × Fin 4) = 24 ∧
    (∀ i : Fin 4, (Finset.univ.filter
      (fun r : Fin 6 × Fin 4 => i ∈ (sixDyadData r.1).members)).card = 12)

def studyRecoveryStatement : Prop :=
  ∀ i : Fin 22, ∀ k : ℕ,
      (k ≤ (studyData i).n ∧
        |(k : ℚ)/((studyData i).n : ℚ)-((studyData i).lossMilli : ℚ)/1000| ≤ (1/2000 : ℚ)) ↔
      k = (studyData i).loss

def studyThresholdStatement : Prop :=
  (Finset.univ.filter (fun i : Fin 22 => (studyData i).n ≤ 2*(studyData i).loss)) = ({4,8,9,20} : Finset (Fin 22)) ∧
    (Finset.univ.filter (fun i : Fin 22 => (studyData i).n < 2*(studyData i).loss)) = ({4,9,20} : Finset (Fin 22)) ∧
    ({i : Fin 22 | (studyData i).n ≤ 2*(studyData i).loss} : Finset (Fin 22)).card = 4 ∧
    ({i : Fin 22 | (studyData i).n < 2*(studyData i).loss} : Finset (Fin 22)).card = 3 ∧
    (Finset.univ.filter (fun i : Fin 22 => 500 ≤ (studyData i).lossMilli)) = ({4,8,9,20} : Finset (Fin 22)) ∧
    (studyData 8).n = 4 ∧ (studyData 8).loss = 2

def studyOtherCountsStatement : Prop :=
  Fintype.card (Fin 22) = 22 ∧ (∑ i, (studyData i).n) = 691 ∧
    ({i : Fin 22 | (studyData i).loss = 0} : Finset (Fin 22)).card = 7 ∧
    ({i : Fin 22 | 1000 < (studyData i).serMilli} : Finset (Fin 22)).card = 18 ∧
    (∀ i, 898 ≤ (studyData i).serMilli ∧ (studyData i).serMilli ≤ 4158) ∧
    (studyData 6).serMilli = 898 ∧ (studyData 8).serMilli = 4158

/-- The exact fitted Cox counterexample, including both erroneous subtractions. -/
def T3Statement : Prop :=
  survivalRiskSetsStatement ∧ survivalScoresStatement ∧ survivalSubjectTotalsStatement ∧
  survivalComponentsStatement ∧ survivalDiscrepancyStatement ∧ survivalFitStatement ∧
  survivalPartitionStatement ∧
  max (5/144 : ℝ) 0 = 5/144 ∧ max (23/432 : ℝ) 0 = 23/432 ∧
  max (103/2160 : ℝ) 0 = 103/2160

/-- The actual ten-dyad OLS covariance and failure of its diagonal gate. -/
def T6Statement : Prop :=
  tenFitStatement ∧ tenVarianceStatement ∧ tenDecompositionStatement ∧
  tenCovariance.IsHermitian ∧ tenGateFailureStatement

/-- Decomposition values and pooling discrepancy; no direct ordered-pair equality. -/
def imputationDCR (B : Bool) : ℝ :=
  (∑ i, imputationMemberCovariance B i)-imputationDyadCovariance B-
    2*imputationRecordCovariance B

def T8Statement : Prop :=
  imputationFitsStatement ∧ imputationBetweenStatement ∧ imputationGapStatement ∧
  imputationPartitionStatement ∧
  (3*(2/9 : ℝ)+2*(8/81))/5 = 14/81 ∧
  codePooledVariance = 14/81+(49/52 : ℝ)*rubinContribution fiveEstimates 0 0 ∧
  codePooledVariance-correctPooledVariance =
    ((49/52 : ℝ)-1)*rubinContribution fiveEstimates 0 0 ∧
  (∀ B : Bool, 0 < imputationDCR B ∧ max (imputationDCR B) 0 = imputationDCR B) ∧
  max codePooledVariance 0 = codePooledVariance ∧
  max correctPooledVariance 0 = correctPooledVariance

/-- Exact recovery and corrected counts for the printed Supplementary Table A.2. -/
def T10Statement : Prop :=
  (∀ i : Fin 22, 0 < (studyData i).n) ∧ studyRecoveryStatement ∧
  studyThresholdStatement ∧ studyOtherCountsStatement

/-- All four universal lower-bound readings fail. -/
def T5Statement : Prop :=
  ¬UniversalPopulationBound ∧ ¬UniversalStrictPopulationBound ∧
  ¬UniversalExpectationBound ∧ ¬UniversalLimitBound

end
end SAP.P032
