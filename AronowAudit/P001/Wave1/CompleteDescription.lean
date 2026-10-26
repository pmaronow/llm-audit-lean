import AronowAudit.P001.Wave1.CompleteDescriptionBlueprint
import AronowAudit.P001.Wave1.CompleteDescription.N1
import AronowAudit.P001.Wave1.CompleteDescription.N2

set_option autoImplicit false

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem printed_complete_description_contract_refuted :
  ¬ ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X) (D U : Ω → ℝ),
    Measurable D → Measurable U → ∀ (m : E → ℝ → ℝ → ℝ),
    Measurable (fun ω => m (X ω) 0 (U ω)) → Measurable (fun ω => m (X ω) 1 (U ω)) →
    (∀ ω, m (X ω) 0 (U ω) ∈ Set.Icc (0 : ℝ) 100 ∧ m (X ω) 1 (U ω) ∈ Set.Icc (0 : ℝ) 100) →
    CI μ X hX (fun ω => (m (X ω) 0 (U ω), m (X ω) 1 (U ω))) D :=
  CompleteDescription.assemble CompleteDescription.n1_proof CompleteDescription.n2_proof

end

end AronowAudit.P001.Wave1
