import AronowAudit.P001.Wave1.PolynomialBlpBlueprint
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.PolynomialBlp

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- Compactness supplies the two almost-sure bounds needed for `MemLp.of_bound`. -/
theorem n1_proof : N1.{u} := by
  intro Ω _ μ _ X Y a b m hX hsupp hm hc
  have hmMeas : Measurable (fun ω => m (X ω)) := hm.1.comp hX
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc a b)).exists_bound_of_continuousOn hc
  have hmBound : ∀ᵐ ω ∂μ, ‖m (X ω)‖ ≤ C := by
    filter_upwards [hsupp] with ω hω using hC (X ω) hω
  refine ⟨MemLp.of_bound hmMeas.aestronglyMeasurable C hmBound, ?_⟩
  intro q
  have hqMeas : Measurable (fun ω => q.eval (X ω)) := q.continuous.measurable.comp hX
  obtain ⟨D, hD⟩ := (isCompact_Icc : IsCompact (Set.Icc a b)).exists_bound_of_continuousOn
    q.continuous.continuousOn
  have hqBound : ∀ᵐ ω ∂μ, ‖q.eval (X ω)‖ ≤ D := by
    filter_upwards [hsupp] with ω hω using hD (X ω) hω
  exact MemLp.of_bound hqMeas.aestronglyMeasurable D hqBound

end

end AronowAudit.P001.Wave1.PolynomialBlp
