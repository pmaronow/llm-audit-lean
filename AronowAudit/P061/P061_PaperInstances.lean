import AronowAudit.P061.P061_PaperDomains
namespace AronowAudit.P061.PaperInstances
open scoped BigOperators Classical
noncomputable section

def pairEmbedding (z : BinaryPair) : Fin 2 → Fin 2 := ![z.1,z.2]

theorem pairEmbedding_injective : Function.Injective pairEmbedding := by
  intro z w h
  exact Prod.ext (congrFun h 0) (congrFun h 1)

/-- Actual two-unit SRS: exactly one of two units is sampled, equally likely. -/
def twoUnitSRS : Design (Fin 2 → Fin 2) :=
  extendDesign pairEmbedding pairEmbedding_injective oppositeDesign

theorem twoUnitSRS_complete : CompleteRandomization twoUnitSRS 1 := by
  intro z
  have he : pairEmbedding (z 0,z 1)=z := by
    funext i
    fin_cases i <;> rfl
  rw [←he]
  change Function.extend pairEmbedding oppositeDesign.p (fun _ => 0)
      (pairEmbedding (z 0,z 1)) = _
  rw [Function.Injective.extend_apply pairEmbedding_injective]
  generalize z 0=a
  generalize z 1=b
  fin_cases a <;> fin_cases b <;>
    norm_num [oppositeDesign,pairEmbedding,Finset.univ_fin2] <;> decide

/-- The raw response is the other unit's assignment; global SUTVA fails. -/
def interferingOutcome : OutcomeSchedule (Fin 2 → Fin 2) 2 :=
  fun i z => if i=0 then (z 1).val else (z 0).val

theorem interferingOutcome_not_sutva :
    ¬SUTVA (fun (i : Fin 2) (z : Fin 2 → Fin 2) => (z i).val) interferingOutcome := by
  intro h
  have hh := h 0 ![0,0] ![0,1] (by norm_num)
  norm_num [interferingOutcome] at hh

theorem actual_SRS_and_CR_application :
    (∀ z, Support twoUnitSRS z → (Finset.univ.filter (fun i => z i=1)).card=1) ∧
    expectation twoUnitSRS
      (sampleMean (fun i z => (z i).val) interferingOutcome 1 1)=
      aepo twoUnitSRS (fun i z => (z i).val) interferingOutcome 1 ∧
    expectation twoUnitSRS (fun z =>
      sampleMean (fun i z => (z i).val) interferingOutcome 1 1 z-
      sampleMean (fun i z => (z i).val) interferingOutcome 0 1 z)=
      aeed twoUnitSRS (fun i z => (z i).val) interferingOutcome 1 0 := by
  have hs := PaperDomains.sample_mean_SRS_T17 twoUnitSRS interferingOutcome 1
    (by norm_num) (by norm_num) twoUnitSRS_complete
  have hc := PaperDomains.difference_in_means_CR_T17 twoUnitSRS interferingOutcome 1
    (by norm_num) (by norm_num) twoUnitSRS_complete
  exact ⟨hs.1,hs.2.2,hc.2⟩

theorem actual_general_SRS_application :
    SamplingCompletion.SimpleRandomExposure twoUnitSRS (fun i z => (z i).val) 1 1 ∧
    expectation twoUnitSRS
      (sampleMean (fun i z => (z i).val) interferingOutcome 1 1)=
      aepo twoUnitSRS (fun i z => (z i).val) interferingOutcome 1 := by
  have hd : SamplingCompletion.SimpleRandomExposure twoUnitSRS (fun i z => (z i).val) 1 1 := by
    unfold SamplingCompletion.SimpleRandomExposure
    rw [SamplingCompletion.maskDesign_own]
    exact twoUnitSRS_complete
  exact ⟨hd,(PaperDomains.sample_mean_SRS_general_T17 twoUnitSRS _ interferingOutcome 1 1
    (by norm_num) (by norm_num) hd (Set.toFinite _)).2.2⟩

def oneDesign : Design Unit := uniformDesign Unit
def oneExposure : ExposureMapping Unit 1 := fun _ _ => 0
def oneOutcome : OutcomeSchedule Unit 1 := fun _ _ => 3
def onePrediction : OutcomeSchedule Unit 1 := fun _ _ => 5

theorem one_positive : ∀ i, 0<pi oneDesign oneExposure i 0 := by
  intro i
  norm_num [pi,probability,oneDesign,oneExposure,uniformDesign,tsum_fintype]

theorem one_prediction_moment : ∀ i,
    expectation oneDesign (fun z =>
      (if oneExposure i z=0 then onePrediction i z else 0)/pi oneDesign oneExposure i 0)=
      expectation oneDesign (onePrediction i) := by
  intro i
  norm_num [expectation,pi,probability,oneDesign,oneExposure,onePrediction,uniformDesign,tsum_fintype]

theorem actual_adjustment_and_moment_application :
    Integrable oneDesign (regressionEstimator oneDesign oneExposure oneOutcome onePrediction 0) ∧
    expectation oneDesign (regressionEstimator oneDesign oneExposure oneOutcome onePrediction 0)=
      aepo oneDesign oneExposure oneOutcome 0 := by
  exact PaperDomains.covariate_adjustment_T20 oneDesign oneExposure oneOutcome onePrediction 0
    (by norm_num) one_positive (finite_type_targeted_moment _ _ _ _)
    (fun _ => Summable.of_finite) (finite_type_targeted_moment _ _ _ _) one_prediction_moment

#print axioms twoUnitSRS_complete
#print axioms actual_SRS_and_CR_application
#print axioms actual_adjustment_and_moment_application
end
end AronowAudit.P061.PaperInstances
