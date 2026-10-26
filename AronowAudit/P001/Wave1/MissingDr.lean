import AronowAudit.P001.Wave1.MissingDrBlueprint
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

theorem missing_double_robustness_paper_support :
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y R : Ω → ℝ), Measurable Y → Measurable R →
    Integrable Y μ → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < prob μ {ω | R ω = 0} → 0 < prob μ {ω | R ω = 1} →
    ∀ (p : (Fin K → ℝ) → ℝ), IsCEF μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    CI μ X hX Y R →
    ∀ (m q : (Fin K → ℝ) → ℝ), Measurable m → Measurable q → Integrable (m ∘ X) μ →
    ((IsCEF (μ.restrict {ω | R ω = 1}) X (fun ω => censored (Y ω) (R ω)) m ∧
        ∃ η : ℝ, 0 < η ∧ ∀ᵐ ω ∂μ, η < q (X ω) ∧ q (X ω) < 1 - η) ∨
      q ∘ X =ᵐ[μ] p ∘ X) →
    mean μ Y =
      mean μ (fun ω => m (X ω) + R ω * (censored (Y ω) (R ω) - m (X ω)) / q (X ω)) := by
  exact MissingDr.assemble
    ⟨MarSelection.n1_proof, MarSelection.n2_proof, MarSelection.n3_proof,
      MarSelection.n4_proof, MarSelection.n5_proof, MarSelection.n6_proof, MarSelection.n7_proof⟩

end

end AronowAudit.P001.Wave1
