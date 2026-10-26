import AronowAudit.P029.Wave1.FiniteMeasureBlueprint

namespace AronowAudit.P029.Wave1.FiniteMeasure

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

/-- The Wald ratio and compliance score use the same finite normalized means. -/
theorem n6_proof : N6 := by
  classical
  intro hN1 L X _ _ _ p hp U Z
  obtain ⟨_, _, hP, hCE⟩ := hN1 p hp
  constructor
  · intro w
    simp only [mWald, mArm, fWald, hCE, Set.mem_setOf_eq]
  · intro x
    simp only [scoreAt, fScore, hP, Set.mem_setOf_eq]

end

end AronowAudit.P029.Wave1.FiniteMeasure
