import SAP.P010.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set

theorem SAP.P010.WH.W1.T17_L1_proof : SAP.P010.WH.W1.T17_L1 := by
  intro K d μ a
  have hpair : Measurable (fun ω : SAP.P010.Population K d =>
      (SAP.P010.check ω, SAP.P010.arm ω)) := by
    change Measurable (fun ω : AronowAudit.P010.State K d =>
      (AronowAudit.P010.observedS ω, AronowAudit.P010.assignment ω))
    exact AronowAudit.P010.measurable_observedS.prodMk
      AronowAudit.P010.measurable_assignment
  have hfirstSet : MeasurableSet {v : Bool × Fin K | v.1 = true ∧ v.2 = a} :=
    MeasurableSet.inter
      (measurable_fst (measurableSet_singleton true))
      (measurable_snd (measurableSet_singleton a))
  have hsecondSet : MeasurableSet {v : Bool × Fin K | v.2 = a} :=
    measurable_snd (measurableSet_singleton a)
  constructor
  · rw [SAP.P010.observedCheckArmLaw, Measure.map_apply hpair hfirstSet]
    change μ {ω | SAP.P010.check ω = true ∧ SAP.P010.arm ω = a} =
      μ (SAP.P010.passed ∩ SAP.P010.assigned a)
    rfl
  · rw [SAP.P010.observedCheckArmLaw, Measure.map_apply hpair hsecondSet]
    change μ {ω | SAP.P010.arm ω = a} = μ (SAP.P010.assigned a)
    rfl
