import AronowAudit.P029.Wave1.IgnorabilityOrderingBlueprint
import AronowAudit.P029.Wave1.FiniteMeasure.N1
import AronowAudit.P029.Wave1.FiniteMeasure.N2
import AronowAudit.P029.Wave1.FiniteMeasure.N3
import AronowAudit.P029.Wave1.FiniteMeasure.N6
import AronowAudit.P029.Wave1.IgnorabilityOrdering.N1

namespace AronowAudit.P029.Wave1

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029 AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

theorem printed_ignorability_ordering_refuted :
  ¬ (∀ {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
      IVAssumptions μ U Z → ∀ (x : X), 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x →
        typicalAt μ U Z x → latentAt μ U x) := by
  exact IgnorabilityOrdering.assemble
    FiniteMeasure.n1_proof
    FiniteMeasure.n2_proof
    FiniteMeasure.n3_proof
    FiniteMeasure.n6_proof
    IgnorabilityOrdering.n1_proof

end

end AronowAudit.P029.Wave1
