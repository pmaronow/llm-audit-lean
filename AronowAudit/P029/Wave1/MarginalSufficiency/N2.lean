import AronowAudit.P029.Wave1.MarginalSufficiencyBlueprint

namespace AronowAudit.P029.Wave1.MarginalSufficiency

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029 AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

/-- Pass from independence of Boolean effect and full type to the printed marginal premise. -/
theorem n2_proof : N2 := by
  classical
  intro hFM2
  have hp : ValidLaw marginalJoint := marginal_independence_counterexample.1.1
  have hbase : IndepFun (fun i : (Triple × Bool) × Bool => i.1.1.2.1)
      (fun i => ((independenceUnit i.1).d0, (independenceUnit i.1).d1))
      (atomicMeasure marginalJoint) :=
    hFM2 marginalJoint hp (fun i => i.1.1.2.1)
      (fun i => ((independenceUnit i.1).d0, (independenceUnit i.1).d1))
      marginal_independence_counterexample.2.1
  have hbit : Measurable (fun b : Bool => bit b) := Measurable.of_discrete
  have hcomplier : Measurable (fun d : Bool × Bool => decide (d.1 = false ∧ d.2 = true)) :=
    Measurable.of_discrete
  have hcomposed := hbase.comp hbit hcomplier
  convert hcomposed using 1 <;> ext i <;>
    simp [Function.comp_def, liftUnit, independenceUnit, PotentialUnit.tau,
      PotentialUnit.complier]

end

end AronowAudit.P029.Wave1.MarginalSufficiency
