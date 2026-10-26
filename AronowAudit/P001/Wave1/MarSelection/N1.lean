import AronowAudit.P001.Wave1.MarSelectionBlueprint

set_option autoImplicit false

universe u v w

namespace AronowAudit.P001.Wave1.MarSelection

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n1_proof : N1.{u} := by
  intro Ω mΩ μ _ m hm R hR hbin
  have hbound : ∀ᵐ ω ∂μ, ‖R ω‖ ≤ (1 : ℝ) := by
    filter_upwards [hbin] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hRi : Integrable R μ := Integrable.of_bound (hR.mono hm le_rfl).aestronglyMeasurable 1 hbound
  have hnonneg : (0 : Ω → ℝ) ≤ᵐ[μ] R := by
    filter_upwards [hbin] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hle : R ≤ᵐ[μ] (fun _ => (1 : ℝ)) := by
    filter_upwards [hbin] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hlow := condExp_nonneg (m := m) hnonneg
  have hupp := condExp_mono (m := m) hRi (integrable_const (1 : ℝ)) hle
  rw [condExp_const hm (1 : ℝ)] at hupp
  filter_upwards [hlow, hupp] with ω hω0 hω1
  exact ⟨hω0, hω1⟩

end

end AronowAudit.P001.Wave1.MarSelection
