import AronowAudit.P022.Wave1.SharpBounds.N5

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.SharpBounds
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology
noncomputable section

theorem n6_proof : N6 := by
  intro N _ y1 y0 J hJ
  constructor
  · apply Measure.ext_of_Iic
    intro x
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [Measure.map_apply measurable_fst measurableSet_Iic,
      Measure.map_apply (measurable_of_finite _) measurableSet_Iic, measure_unitLaw]
    exact (hJ x).1
  · apply Measure.ext_of_Iic
    intro x
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [Measure.map_apply measurable_snd measurableSet_Iic,
      Measure.map_apply (measurable_of_finite _) measurableSet_Iic, measure_unitLaw]
    exact (hJ x).2

end
end AronowAudit.P022.Wave1.SharpBounds
