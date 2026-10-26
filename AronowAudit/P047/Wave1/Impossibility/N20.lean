import AronowAudit.P047.Wave1.ImpossibilityBlueprint

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

theorem n20_proof : N20.{u} := by
  intro R _ Q _ lo hi n
  have hb : BddBelow (insert (1 : ℝ) {r | ∃ L : CausalLaw, UnknownModel L ∧
      r = ((sampleLaw L.measure).prod Q).real
        {z | lo n (observedSample n z.1, z.2) ≤ (ate L : EReal) ∧
          (ate L : EReal) ≤ hi n (observedSample n z.1, z.2)}}) := by
    refine ⟨0, ?_⟩
    rintro r (rfl | ⟨L, _hL, rfl⟩)
    · norm_num
    · exact measureReal_nonneg
  constructor
  · constructor
    · unfold randCoverage
      apply le_csInf (Set.insert_nonempty _ _)
      rintro r (rfl | ⟨L, _hL, rfl⟩)
      · norm_num
      · exact measureReal_nonneg
    · exact csInf_le hb (Set.mem_insert _ _)
  · exact ⟨measureReal_nonneg, measureReal_le_one⟩

end

end AronowAudit.P047.Wave1.Impossibility
