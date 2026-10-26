import AronowAudit.P001.Wave1.MarVectorBlueprint
import AronowAudit.P001.Wave1.MarSelection.N1
import AronowAudit.P001.Wave1.MarSelection.N2
import AronowAudit.P001.Wave1.MarSelection.N3
import AronowAudit.P001.Wave1.MarSelection.N4
import AronowAudit.P001.Wave1.MarSelection.N5
import AronowAudit.P001.Wave1.MarSelection.N6
import AronowAudit.P001.Wave1.MarSelection.N7

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem mar_vector_paper_support_cef :
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y R : Ω → ℝ), Measurable Y → Measurable R →
    Integrable Y μ → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < prob μ {ω | R ω = 0} → 0 < prob μ {ω | R ω = 1} →
    ∀ (p m : (Fin K → ℝ) → ℝ), IsCEF μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    CI μ X hX Y R →
    IsCEF (μ.restrict {ω | R ω = 1}) X (fun ω => censored (Y ω) (R ω)) m →
    Integrable (m ∘ X) μ →
    IsCEF μ X Y m ∧ mean μ Y = mean μ (m ∘ X) := by
  exact MarVector.assemble
    ⟨MarSelection.n1_proof, MarSelection.n2_proof, MarSelection.n3_proof,
      MarSelection.n4_proof, MarSelection.n5_proof, MarSelection.n6_proof, MarSelection.n7_proof⟩

end

end AronowAudit.P001.Wave1
