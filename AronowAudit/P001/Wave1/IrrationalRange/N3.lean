import AronowAudit.P001.Wave1.IrrationalRangeBlueprint
import AronowAudit.P001.Wave1.IrrationalRange.N1

namespace AronowAudit.P001.Wave1.IrrationalRange

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableIrrationalRangeN3 (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem n3_proof : N3 := by
  apply isProbabilityMeasure_iff.mpr
  unfold irrHalfLaw
  rw [Measure.smul_apply, comap_subtype_coe_apply n1_proof.1,
    Set.image_univ, Subtype.range_coe, n1_proof.2.1]
  norm_num
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

end
end AronowAudit.P001.Wave1.IrrationalRange
