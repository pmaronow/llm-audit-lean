import AronowAudit.P022.Wave1.SharpBoundsBlueprint

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.SharpBounds
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology
noncomputable section

theorem n12_proof : N12 := by
  intro N _ v w
  unfold finiteCovariance finiteMean
  calc
    (𝔼 i, (v i - (𝔼 j, v j)) * (w i - (𝔼 j, w j))) =
        𝔼 i, (v i * w i - (𝔼 j, w j) * v i - (𝔼 j, v j) * w i +
          (𝔼 j, v j) * (𝔼 j, w j)) := by
      apply Finset.expect_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
        Finset.expect_sub_distrib, ← Finset.mul_expect, ← Finset.mul_expect,
        Finset.expect_const Finset.univ_nonempty]
      ring

end
end AronowAudit.P022.Wave1.SharpBounds
