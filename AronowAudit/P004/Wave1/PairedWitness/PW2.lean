import AronowAudit.P004.Wave1.PairedWitness.PW3

namespace AronowAudit.P004.Wave1.PairedWitness

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators Classical

theorem pw2_proof : PW2 := by
  change Overlap (fun N => propensities (pairO N) pairTheta)
  refine ⟨1 / 4, by norm_num, by norm_num, ?_⟩
  intro N i
  beta_reduce
  rw [pw3_proof N]
  norm_num

end
end AronowAudit.P004.Wave1.PairedWitness
