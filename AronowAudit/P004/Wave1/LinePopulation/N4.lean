import AronowAudit.P004.Wave1.LinePopulation.N2

namespace AronowAudit.P004.Wave1.LinePopulation

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

theorem n4_proof : N4 := by
  intro N R d hd i
  refine ⟨line_region_measurable R d i, ?_, ?_, ?_⟩
  · have hself : i ∈ ball (nodeSeparation (linePopulation R)) i d := by
      simp [ball, n1_proof R, hd]
    have hcard : 0 < (ball (nodeSeparation (linePopulation R)) i d).card :=
      Finset.card_pos.mpr ⟨i, hself⟩
    rw [line_spatial_mass]
    exact_mod_cast hcard
  · rw [line_spatial_mass]
    simp
  · intro z
    have hi : Integrable (fun x => (linePopulation R).outcome x z)
        (∑ j : Fin N, Measure.dirac (planePoint (10 * (j : ℝ)) 0)) := by
      rw [integrable_finsetSum_measure]
      intro j _
      exact integrable_dirac (by simp)
    exact hi.integrableOn

end
end AronowAudit.P004.Wave1.LinePopulation
