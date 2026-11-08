import SAP.P032.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P032.Bridge

open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory Filter

noncomputable section

theorem survivalScores_eq : survivalScores = AronowAudit.P032.coxScores := rfl

theorem survivalInfluence_eq : survivalInfluence = AronowAudit.P032.coxInfluence := rfl

theorem survivalClosedLikelihood_eq :
    survivalClosedLikelihood = AronowAudit.P032.coxClosedLikelihood := rfl

theorem scalarRecord_eq : @recordScalarCovariance = @AronowAudit.P032.scalarRecord := rfl

theorem subjectMask_eq : @subjectMask = @AronowAudit.P032.idPattern := rfl

/-! The two tables contain SAP structures. Projection through a table lookup
requires these finite, purely structural correspondences. -/

theorem survivalId_eq (r : Fin 10) :
    (survivalRecords r).id = (AronowAudit.P032.coxRecords r).id := by fin_cases r <;> rfl

theorem survivalMembers_eq (r : Fin 10) :
    ((survivalRecords r).dyad).members = ((AronowAudit.P032.coxRecords r).dyad).members := by
  fin_cases r <;> rfl

theorem survivalStart_eq (r : Fin 10) :
    (survivalRecords r).start = (AronowAudit.P032.coxRecords r).start := by fin_cases r <;> rfl

theorem survivalStop_eq (r : Fin 10) :
    (survivalRecords r).stop = (AronowAudit.P032.coxRecords r).stop := by fin_cases r <;> rfl

theorem survivalX_eq (r : Fin 10) :
    (survivalRecords r).x = (AronowAudit.P032.coxRecords r).x := by fin_cases r <;> rfl

theorem survivalStatus_eq (r : Fin 10) :
    (survivalRecords r).status = (AronowAudit.P032.coxRecords r).status := by fin_cases r <;> rfl

theorem survivalRisk_iff (r : Fin 10) (t : ℕ) :
    survivalAtRisk r t ↔ AronowAudit.P032.coxRisk r t := by
  simp only [survivalAtRisk, AronowAudit.P032.coxRisk, survivalStart_eq, survivalStop_eq]

theorem survivalEvent_iff (r : Fin 10) (t : ℕ) :
    survivalEvent r t ↔ AronowAudit.P032.coxEvent r t := by
  simp only [survivalEvent, AronowAudit.P032.coxEvent, survivalStatus_eq, survivalStop_eq]

theorem survivalRiskCount_eq : survivalRiskCount = AronowAudit.P032.coxRiskN := by
  funext t
  simp only [survivalRiskCount, AronowAudit.P032.coxRiskN, survivalRisk_iff]

theorem survivalEventCount_eq : survivalEventCount = AronowAudit.P032.coxEventN := by
  funext t
  simp only [survivalEventCount, AronowAudit.P032.coxEventN, survivalEvent_iff]

theorem survivalRiskMean_eq : survivalRiskMean = AronowAudit.P032.coxRiskMean := by
  funext t
  simp only [survivalRiskMean, AronowAudit.P032.coxRiskMean, survivalRisk_iff,
    survivalX_eq, survivalRiskCount_eq]

theorem survivalInformation_eq : survivalInformation = AronowAudit.P032.coxInformation := by
  simp only [survivalInformation, AronowAudit.P032.coxInformation, survivalEventCount_eq,
    survivalRisk_iff, survivalX_eq, survivalRiskCount_eq, survivalRiskMean_eq]

theorem survivalEfficientScore_eq : survivalEfficientScore = AronowAudit.P032.coxEfficientScore := by
  funext r
  simp only [survivalEfficientScore, AronowAudit.P032.coxEfficientScore, survivalRisk_iff,
    survivalEvent_iff, survivalEventCount_eq, survivalRiskCount_eq, survivalX_eq, survivalRiskMean_eq]

theorem survivalLikelihood_eq : survivalLogLikelihood = AronowAudit.P032.coxLogLikelihood := by
  funext β
  simp only [survivalLogLikelihood, AronowAudit.P032.coxLogLikelihood, survivalEvent_iff,
    survivalX_eq, survivalEventCount_eq, survivalRisk_iff]

theorem survivalMember_eq (i : Fin 4) :
    memberScalarCovariance (fun r => (survivalRecords r).dyad) i survivalInfluence =
    AronowAudit.P032.scalarMember (fun r => (AronowAudit.P032.coxRecords r).dyad) i
      AronowAudit.P032.coxInfluence := by
  simp only [memberScalarCovariance, AronowAudit.P032.scalarMember, survivalMembers_eq]
  rfl

theorem survivalCluster_eq :
    clusterScalarCovariance (fun r => (survivalRecords r).id) survivalInfluence =
    AronowAudit.P032.scalarCluster (fun r => (AronowAudit.P032.coxRecords r).id)
      AronowAudit.P032.coxInfluence := by
  simp only [clusterScalarCovariance, AronowAudit.P032.scalarCluster, survivalId_eq]
  rfl

theorem survivalDyadicMask_eq :
    dyadicMask (fun r => (survivalRecords r).dyad) =
    AronowAudit.P032.dyPattern (fun r => (AronowAudit.P032.coxRecords r).dyad) := by
  funext r s
  simp only [dyadicMask, AronowAudit.P032.dyPattern, survivalMembers_eq]

theorem survivalSubjects_eq : (fun r => (survivalRecords r).id) =
    (fun r => (AronowAudit.P032.coxRecords r).id) := funext survivalId_eq

theorem survivalRepeatedMask_eq : repeatedMask (fun r => (survivalRecords r).dyad) =
    AronowAudit.P032.repeatPattern (fun r => (AronowAudit.P032.coxRecords r).dyad) := by
  funext r s
  simp only [repeatedMask, AronowAudit.P032.repeatPattern, survivalMembers_eq]

/-- The entire constructed survival example is transported without recomputing it. -/
theorem survivalAssembly : T3Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by norm_num, by norm_num, by norm_num⟩
  · simpa only [survivalRiskSetsStatement, survivalRisk_iff] using AronowAudit.P032.cox_exact_risk_sets
  · simpa only [survivalScoresStatement, survivalRiskCount_eq, survivalEventCount_eq,
      survivalRiskMean_eq, survivalInformation_eq, survivalEfficientScore_eq, survivalScores_eq] using
      AronowAudit.P032.cox_risk_score_certificate
  · simpa only [survivalSubjectTotalsStatement, survivalId_eq, survivalScores_eq] using
      AronowAudit.P032.cox_subject_score_totals
  · unfold survivalComponentsStatement
    rw [survivalCluster_eq]
    simp_rw [survivalMember_eq]
    exact AronowAudit.P032.cox_components
  · simpa only [survivalDiscrepancyStatement, survivalDyadicMask_eq, quadForm_eq, survivalInfluence_eq] using
      AronowAudit.P032.cox_substitution_counterexample
  · simpa only [survivalFitStatement, survivalLikelihood_eq, survivalClosedLikelihood_eq] using
      AronowAudit.P032.cox_unique_fit
  · simpa only [survivalPartitionStatement, subjectMask_eq, survivalSubjects_eq,
      survivalRepeatedMask_eq] using
      AronowAudit.P032.cox_id_is_repeated_dyad

theorem studyN_eq (i : Fin 22) : (studyData i).n = (AronowAudit.P032.studies i).n := by
  fin_cases i <;> rfl

theorem studyLoss_eq (i : Fin 22) : (studyData i).loss = (AronowAudit.P032.studies i).loss := by
  fin_cases i <;> rfl

theorem studyLossMilli_eq (i : Fin 22) :
    (studyData i).lossMilli = (AronowAudit.P032.studies i).lossMilli := by fin_cases i <;> rfl

theorem studySerMilli_eq (i : Fin 22) :
    (studyData i).serMilli = (AronowAudit.P032.studies i).serMilli := by fin_cases i <;> rfl

theorem studyAssembly : T10Statement := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · simpa only [studyRecoveryStatement, studyN_eq, studyLoss_eq, studyLossMilli_eq] using
      AronowAudit.P032.study_unique_rational_recovery
  · simpa only [studyThresholdStatement, studyN_eq, studyLoss_eq, studyLossMilli_eq] using
      AronowAudit.P032.study_threshold_counts
  · simpa only [studyOtherCountsStatement, studyN_eq, studyLoss_eq, studySerMilli_eq] using
      AronowAudit.P032.study_neighboring_counts

end
end SAP.P032.Bridge
