import SAP.P006b.Bridge
import AronowAudit.P006.Wave1.AverageBestResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b.T26Repair

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
open AronowAudit.P006
open AronowAudit.P006.Wave1
open AronowAudit.P006.Wave1.AverageBestResponse
open AronowAudit.P006.Wave1.BinaryExperiment

noncomputable section

theorem refutation : SAP.P006b.T26Statement := by
  classical
  intro hall
  let P : AronowAudit.P006.Experiment (Fin 2 → Bool × Bool) Bool 2 := E26
  have hstanding : AronowAudit.P006.Standing P := by
    simpa [P, E26] using
      BinaryExperiment.standing_of BinaryExperiment.n1_proof BinaryExperiment.n3_proof
        BinaryExperiment.n4_proof BinaryExperiment.n5_proof 2 (by norm_num)
        effectE001 (fun _ _ _ => 0)
  have hfull : ∀ x : Bool, 0 < (P.PX {x}).toReal := by
    intro x
    cases x <;>
      norm_num [P, E26, BinaryExperiment.binExp, BinaryExperiment.fairLaw,
        Fintype.sum_bool, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply]
  have hunbiased : AronowAudit.P006.PointwiseUnbiased P {π | Admissible π} := by
    intro π _ x
    refine ⟨integrable_zero _ _ _, ?_⟩
    simp [P, E26, BinaryExperiment.binExp]
  have hval : AverageBestResponse.S1 :=
    AverageBestResponse.n1_proof BinaryExperiment.n1_proof
      (BinaryExperiment.n2_proof BinaryExperiment.n1_proof)
  have hnot :
      ¬ (AronowAudit.P006.IsBest {π | AronowAudit.P006.Admissible π} E26.expectedATO
            (AronowAudit.P006.printedAverageRule E26.μ1) ∧
          AronowAudit.P006.IsBest {π | AronowAudit.P006.Admissible π} E26.expectedATT
            (AronowAudit.P006.printedAverageRule E26.τ)) := by
    rintro ⟨hATO, _hATT⟩
    have hone : AronowAudit.P006.Admissible (fun _ : Bool => (1 : ℝ)) :=
      AverageBestResponse.admissible_of_zero_one _ (fun _ => Or.inr rfl)
    have hpr : ∀ x : Bool,
        AronowAudit.P006.printedAverageRule effectE001 x = AronowAudit.P006.binaryRule (0, 1) x :=
      T1_average_counterexample.1
    have hadm : AronowAudit.P006.Admissible (AronowAudit.P006.printedAverageRule effectE001) := by
      refine AverageBestResponse.admissible_of_zero_one _ (fun x => ?_)
      rw [hpr x]
      cases x <;> simp [AronowAudit.P006.binaryRule]
    have h := hATO.2 _ hone
    change E26.expectedATO (fun _ => 1) ≤
      E26.expectedATO (AronowAudit.P006.printedAverageRule effectE001) at h
    rw [(hval _ hone).1, (hval _ hadm).1, hpr false, hpr true] at h
    have hlt := T1_average_counterexample.2.2.2.1
    simp only [AronowAudit.P006.binaryRule] at h hlt
    norm_num at h hlt
    linarith
  let E : SAP.P006b.Experiment (Fin 2 → Bool × Bool) Bool 2 :=
    SAP.P006b.Bridge.fromProject P
  have hstandingSAP : SAP.P006b.Standing E :=
    SAP.P006b.Bridge.standing_fromProject hstanding
  have hfullSAP : ∀ x : Bool, 0 < (E.PX {x}).toReal := by
    intro x
    simpa [E, SAP.P006b.Bridge.fromProject] using hfull x
  have hunbiasedSAP :
      SAP.P006b.PointwiseUnbiased E {π | SAP.P006b.Admissible π} := by
    simpa [E, SAP.P006b.Bridge.fromProject,
      SAP.P006b.PointwiseUnbiased, AronowAudit.P006.PointwiseUnbiased,
      SAP.P006b.Admissible, AronowAudit.P006.Admissible] using hunbiased
  have hbest := hall E hstandingSAP hfullSAP hunbiasedSAP
  have hproj : SAP.P006b.Bridge.toProject E = P := by
    simpa [E] using SAP.P006b.Bridge.experiment_roundtrip P
  have hμ1 : E.μ1 = (SAP.P006b.Bridge.toProject E).μ1 := rfl
  have hτ : E.τ = (SAP.P006b.Bridge.toProject E).τ := rfl
  have hbestATO0 : AronowAudit.P006.IsBest
      {π | AronowAudit.P006.Admissible π} (SAP.P006b.Bridge.toProject E).expectedATO
      (AronowAudit.P006.printedAverageRule (SAP.P006b.Bridge.toProject E).μ1) := by
    have h := hbest.1
    simpa only [SAP.P006b.Bridge.IsBest_eq, SAP.P006b.Bridge.Admissible_eq,
      SAP.P006b.Bridge.printedAverageRule_eq, SAP.P006b.Bridge.expectedATO_eq, hμ1] using h
  have hbestATT0 : AronowAudit.P006.IsBest
      {π | AronowAudit.P006.Admissible π} (SAP.P006b.Bridge.toProject E).expectedATT
      (AronowAudit.P006.printedAverageRule (SAP.P006b.Bridge.toProject E).τ) := by
    have h := hbest.2
    simpa only [SAP.P006b.Bridge.IsBest_eq, SAP.P006b.Bridge.Admissible_eq,
      SAP.P006b.Bridge.printedAverageRule_eq, SAP.P006b.Bridge.expectedATT_eq, hτ] using h
  have hbestATO : AronowAudit.P006.IsBest
      {π | AronowAudit.P006.Admissible π} E26.expectedATO
      (AronowAudit.P006.printedAverageRule E26.μ1) := by
    simpa [hproj, P] using hbestATO0
  have hbestATT : AronowAudit.P006.IsBest
      {π | AronowAudit.P006.Admissible π} E26.expectedATT
      (AronowAudit.P006.printedAverageRule E26.τ) := by
    simpa [hproj, P] using hbestATT0
  exact hnot ⟨hbestATO, hbestATT⟩

end

end SAP.P006b.T26Repair

#print axioms SAP.P006b.T26Repair.refutation
