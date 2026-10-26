import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint
import AronowAudit.P053.P053_NormalQuantiles

/-! Continuity of the standard normal CDF, from
`AronowAudit.P053.NormalCompletion.cdf_continuousAt` and Mathlib's
`ProbabilityTheory.nullSingletonClass_gaussianReal`. -/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation

theorem n11_proof : N11 := by
  intro x
  have := ProbabilityTheory.nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  exact AronowAudit.P053.NormalCompletion.cdf_continuousAt _ x

end AronowAudit.P031.Wave1.LargeSampleRefutation
