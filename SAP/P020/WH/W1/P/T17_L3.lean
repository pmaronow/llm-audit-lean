import SAP.P020.WH.W1.Leaves
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory SAP.P020

noncomputable section

theorem SAP.P020.WH.W1.T17_L3_proof : SAP.P020.WH.W1.T17_L3 := by
  classical
  intro P
  refine ⟨?_, ?_, ?_, ?_⟩
  · infer_instance
  · exact iIndepFun_infinitePi
      (P := fun _ : ℕ => SAP.P020.W1AssignmentMeasure P)
      (X := fun _ x => x) (fun _ => measurable_id)
  · intro r
    exact Measure.infinitePi_map_eval
      (fun _ : ℕ => SAP.P020.W1AssignmentMeasure P) r
  · intro h
    change (Measure.infinitePi
      (fun _ : ℕ => SAP.P020.W1AssignmentMeasure P)).map
        (fun ω : ℕ → SAP.P020.W1Assignment P =>
          fun i : Fin h => ω i.val) =
      (uniformOn Set.univ : Measure (SAP.P020.CopyAssignments P h))
    rw [← AsymptoticStatistics.pi_const_eq_infinitePi_map
      (SAP.P020.W1AssignmentMeasure P) h]
    have hpi : Measure.pi (fun _ : Fin h =>
        (uniformOn Set.univ : Measure (SAP.P020.W1Assignment P))) =
        (uniformOn Set.univ : Measure (Fin h → SAP.P020.W1Assignment P)) := by
      rw [← ProbabilityTheory.uniformOn_pi]
      simp
    simpa only [SAP.P020.W1AssignmentMeasure, SAP.P020.CopyAssignments] using hpi
