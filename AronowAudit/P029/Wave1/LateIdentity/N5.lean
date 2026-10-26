import AronowAudit.P029.Wave1.LateIdentityBlueprint

namespace AronowAudit.P029.Wave1.LateIdentity

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

universe u v

noncomputable section

/-- Normalize the restricted effect integral by the positive complier mass. -/
theorem n5_proof : N5.{u, v} := by
  intro h2 Ω X _ _ μ _ U Z hiv hc
  have hC : MeasurableSet {ω | (U ω).complier} := (h2 μ U Z hiv).2.2
  have hrestrict :
      (∫ ω, (if (U ω).complier then (U ω).tau else 0) ∂μ) =
        ∫ ω in {ω | (U ω).complier}, (U ω).tau ∂μ := by
    simpa only [Set.indicator, Set.mem_setOf_eq] using
      (integral_indicator (μ := μ) (f := fun ω => (U ω).tau) hC)
  rw [hrestrict]
  unfold mCE
  exact (mul_div_cancel₀ _ (ne_of_gt hc)).symm

end

end AronowAudit.P029.Wave1.LateIdentity
