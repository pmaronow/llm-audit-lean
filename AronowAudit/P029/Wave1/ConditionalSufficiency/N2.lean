import AronowAudit.P029.Wave1.ConditionalSufficiencyBlueprint

namespace AronowAudit.P029.Wave1.ConditionalSufficiency

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029 AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

/-- Conditional independence under the literal normalized restricted measure. -/
theorem n2_proof : N2 := by
  classical
  intro hFM1 hFM2 hFM4 hFM5 x hx
  have hp : ValidLaw conditionalJoint := conditional_independence_counterexample.1.1
  obtain ⟨_hprob, _hIntegral, hMass, _hCE⟩ := hFM1 conditionalJoint hp
  have hmass : mP (atomicMeasure conditionalJoint)
      {i | (liftUnit independenceUnit i).x = x} =
      fP conditionalJoint (fun i => (independenceUnit i.1).x = x) := by
    simpa only [Set.mem_setOf_eq, liftUnit] using
      hMass {i | (liftUnit independenceUnit i).x = x}
  have hxFinite : 0 < fP conditionalJoint (fun i => (independenceUnit i.1).x = x) := by
    rwa [hmass] at hx
  have hbase : IndepFun (fun i : (Triple × Bool) × Bool => i.1.1.2.1)
      (fun i => ((independenceUnit i.1).d0, (independenceUnit i.1).d1))
      (ENNReal.ofReal ((fP conditionalJoint (fun i => (independenceUnit i.1).x = x))⁻¹) •
        (atomicMeasure conditionalJoint).restrict {i | (independenceUnit i.1).x = x}) :=
    hFM5 hFM2 hFM4 conditionalJoint hp (fun i => i.1.1.2.1)
      (fun i => ((independenceUnit i.1).d0, (independenceUnit i.1).d1))
      (fun i => (independenceUnit i.1).x)
      conditional_independence_counterexample.2.1 x hxFinite
  have hbit : Measurable (fun b : Bool => bit b) := Measurable.of_discrete
  have hid : Measurable (fun d : Bool × Bool => d) := measurable_id
  have hcomposed := hbase.comp hbit hid
  rw [hmass]
  simpa only [Function.comp_def, liftUnit, independenceUnit, PotentialUnit.tau, sub_zero]
    using hcomposed

end

end AronowAudit.P029.Wave1.ConditionalSufficiency
