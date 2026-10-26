import AronowAudit.P001.Wave1.MarDiscreteBlueprint
import AronowAudit.P001.Wave1.MarSelection.N1
import AronowAudit.P001.Wave1.MarSelection.N2
import AronowAudit.P001.Wave1.MarSelection.N3
import AronowAudit.P001.Wave1.MarSelection.N4
import AronowAudit.P001.Wave1.MarSelection.N5
import AronowAudit.P001.Wave1.MarSelection.N6
import AronowAudit.P001.Wave1.MarSelection.N7
import AronowAudit.P001.Wave1.MarDiscrete.N1

set_option autoImplicit false

universe u v

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem mar_discrete_paper_support_identification :
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y R : Ω → ℝ), Measurable Y → Measurable R →
    Integrable Y μ → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < prob μ {ω | R ω = 0} → 0 < prob μ {ω | R ω = 1} →
    ∀ (p : E → ℝ), IsCEF μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    CI μ X hX Y R → ∀ (m : E → ℝ),
    IsCEF (μ.restrict {ω | R ω = 1}) X (fun ω => censored (Y ω) (R ω)) m →
    Integrable (m ∘ X) μ →
    IsCEF μ X Y m ∧
      Summable (fun x : E => m x * prob μ {ω | X ω = x}) ∧
      mean μ Y = ∑' x : E, m x * prob μ {ω | X ω = x} := by
  exact MarDiscrete.assemble
    ⟨MarSelection.n1_proof, MarSelection.n2_proof, MarSelection.n3_proof,
      MarSelection.n4_proof, MarSelection.n5_proof, MarSelection.n6_proof, MarSelection.n7_proof⟩
    MarDiscrete.n1_proof

end

end AronowAudit.P001.Wave1
