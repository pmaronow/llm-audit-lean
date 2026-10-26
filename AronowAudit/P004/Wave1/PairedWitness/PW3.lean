import AronowAudit.P004.Wave1.PairedWitnessBlueprint

namespace AronowAudit.P004.Wave1.PairedWitness

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators Classical

theorem pw3_proof : PW3 := by
  intro N
  funext i
  have hdot : dot (pairO N i) pairTheta = 0 := by
    simp [dot, pairO, pairTheta]
  change logistic (dot (pairO N i) pairTheta) = (1 / 2 : ℝ)
  rw [hdot]
  norm_num [logistic, Real.exp_zero]

end
end AronowAudit.P004.Wave1.PairedWitness
