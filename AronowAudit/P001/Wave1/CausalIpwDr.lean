import AronowAudit.P001.Wave1.CausalIpwDrBlueprint
import AronowAudit.P001.Wave1.MarSelection.N1
import AronowAudit.P001.Wave1.MarSelection.N2
import AronowAudit.P001.Wave1.MarSelection.N3
import AronowAudit.P001.Wave1.MarSelection.N4
import AronowAudit.P001.Wave1.MarSelection.N5
import AronowAudit.P001.Wave1.MarSelection.N6
import AronowAudit.P001.Wave1.MarSelection.N7
import AronowAudit.P001.Wave1.CausalIpwDr.N1
import AronowAudit.P001.Wave1.CausalIpwDr.N2

set_option autoImplicit false

universe u v w

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem causal_ipw_and_dr_paper_contract :
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y0 Y1 D : Ω → ℝ),
    Measurable Y0 → Measurable Y1 → Measurable D → Integrable Y0 μ → Integrable Y1 μ →
    (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    0 < prob μ {ω | D ω = 0} → 0 < prob μ {ω | D ω = 1} →
    ∀ (p : (Fin K → ℝ) → ℝ), IsCEF μ X D p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω) ∧ p (X ω) < 1 - ε) →
    CI μ X hX (fun ω => (Y0 ω, Y1 ω)) D →
    let Y := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
    mean μ (fun ω => Y1 ω - Y0 ω) =
      mean μ (fun ω => Y ω * D ω / p (X ω) - Y ω * (1 - D ω) / (1 - p (X ω))) ∧
    (∀ m0 m1 q : (Fin K → ℝ) → ℝ,
      Measurable m0 → Measurable m1 → Measurable q →
      Integrable (m0 ∘ X) μ → Integrable (m1 ∘ X) μ →
      ((IsCEF (μ.restrict {ω | D ω = 0}) X Y m0 ∧
        IsCEF (μ.restrict {ω | D ω = 1}) X Y m1 ∧
        ∃ η : ℝ, 0 < η ∧ ∀ᵐ ω ∂μ, η < q (X ω) ∧ q (X ω) < 1 - η) ∨
        q ∘ X =ᵐ[μ] p ∘ X) →
      mean μ (fun ω => Y1 ω - Y0 ω) =
        mean μ (fun ω => m1 (X ω) + D ω * (Y ω - m1 (X ω)) / q (X ω) -
          m0 (X ω) - (1 - D ω) * (Y ω - m0 (X ω)) / (1 - q (X ω)))) := by
  exact CausalIpwDr.assemble
    ⟨MarSelection.n1_proof, MarSelection.n2_proof, MarSelection.n3_proof,
      MarSelection.n4_proof, MarSelection.n5_proof, MarSelection.n6_proof, MarSelection.n7_proof⟩
    CausalIpwDr.n1_proof CausalIpwDr.n2_proof

end

end AronowAudit.P001.Wave1
