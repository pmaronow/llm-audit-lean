import AronowAudit.P022.Wave1.SharpBoundsBlueprint

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.SharpBounds
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology
noncomputable section

theorem n1_proof : N1 := by
  intro N z y h g
  unfold finiteMean
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  congr 1
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using (h.map g).sum_eq

end
end AronowAudit.P022.Wave1.SharpBounds
