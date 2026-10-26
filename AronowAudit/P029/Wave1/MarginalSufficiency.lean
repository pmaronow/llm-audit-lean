import AronowAudit.P029.Wave1.MarginalSufficiencyBlueprint
import AronowAudit.P029.Wave1.FiniteMeasure.N1
import AronowAudit.P029.Wave1.FiniteMeasure.N2
import AronowAudit.P029.Wave1.FiniteMeasure.N3
import AronowAudit.P029.Wave1.FiniteMeasure.N6
import AronowAudit.P029.Wave1.MarginalSufficiency.N1
import AronowAudit.P029.Wave1.MarginalSufficiency.N2

namespace AronowAudit.P029.Wave1

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029 AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

theorem printed_marginal_sufficiency_refuted :
  ¬ (∀ {Ω X : Type} [MeasurableSpace Ω]
      [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
      IVAssumptions μ U Z →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x) →
      IndepFun (fun ω => (U ω).tau) (fun ω => decide (U ω).complier) μ →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} → latentAt μ U x) ∧
      mWald μ U Z (fun _ => 1) = (∫ ω, (U ω).tau ∂μ) ∧
      mWald μ U Z (fun ω => 1 / scoreAt μ U (U ω).x) = (∫ ω, (U ω).tau ∂μ)) := by
  exact MarginalSufficiency.assemble
    FiniteMeasure.n1_proof
    FiniteMeasure.n2_proof
    FiniteMeasure.n3_proof
    FiniteMeasure.n6_proof
    MarginalSufficiency.n1_proof
    MarginalSufficiency.n2_proof

end

end AronowAudit.P029.Wave1
