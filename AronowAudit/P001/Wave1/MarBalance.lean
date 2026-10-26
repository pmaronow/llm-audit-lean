import AronowAudit.P001.Wave1.MarBalanceBlueprint
import AronowAudit.P001.Wave1.MarSelection.N1
import AronowAudit.P001.Wave1.MarBalance.N1
import AronowAudit.P001.Wave1.MarBalance.N2
import AronowAudit.P001.Wave1.MarBalance.N3

set_option autoImplicit false

universe u v

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem mar_propensity_paper_support_balance :
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y R : Ω → ℝ), Measurable Y → Measurable R →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < prob μ {ω | R ω = 0} → 0 < prob μ {ω | R ω = 1} →
    ∀ (p : (Fin K → ℝ) → ℝ) (hp : IsCEF μ X R p), CI μ X hX Y R →
    ∀ (ε : ℝ), 0 < ε → (∀ᵐ ω ∂μ, ε < p (X ω)) →
    CI μ (p ∘ X) (hp.1.comp hX) R X ∧ CI μ (p ∘ X) (hp.1.comp hX) Y R ∧
      IsCEF μ (p ∘ X) R id ∧ (∀ᵐ ω ∂μ, ε < p (X ω)) := by
  exact MarBalance.assemble MarSelection.n1_proof MarBalance.n1_proof
    MarBalance.n2_proof MarBalance.n3_proof

end

end AronowAudit.P001.Wave1
