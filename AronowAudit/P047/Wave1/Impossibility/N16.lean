import AronowAudit.P047.Wave1.ImpossibilityBlueprint

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

/-- Remove an error of the form `C / (M + 1)` without any sign assumption on `C`. -/
theorem remove_reciprocal_error (a r C : ℝ)
    (h : ∀ M : ℕ, a - C / (M + 1) ≤ r) : a ≤ r := by
  by_contra! hr
  have hδ : 0 < a - r := sub_pos.mpr hr
  obtain ⟨M, hM⟩ := exists_nat_gt (C / (a - r))
  have hcross : C < (M : ℝ) * (a - r) := (div_lt_iff₀ hδ).mp hM
  have hden : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hsmall : C / ((M : ℝ) + 1) < a - r := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hbound := h M
  linarith

theorem n16_proof : N16 := by
  intro r C h
  exact remove_reciprocal_error (1 / 2) r C h

end

end AronowAudit.P047.Wave1.Impossibility
