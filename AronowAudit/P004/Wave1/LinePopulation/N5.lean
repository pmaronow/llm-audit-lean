import AronowAudit.P004.Wave1.LinePopulation.N2

namespace AronowAudit.P004.Wave1.LinePopulation

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

theorem n5_proof : N5 := by
  classical
  intro N R B hB hR x z
  by_cases hx : ∃ j : Fin N, x = planePoint (10 * (j : ℝ)) 0
  · obtain ⟨j, rfl⟩ := hx
    rw [line_outcome_at_atom]
    exact hR j z
  · have hzero : (linePopulation R).outcome x z = 0 := by
      change (∑ j : Fin N, if x = planePoint (10 * (j : ℝ)) 0 then R j z else 0) = 0
      apply Finset.sum_eq_zero
      intro j _
      exact if_neg (fun hj => hx ⟨j, hj⟩)
    rw [hzero, abs_zero]
    exact hB

end
end AronowAudit.P004.Wave1.LinePopulation
