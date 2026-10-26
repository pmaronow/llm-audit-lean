import AronowAudit.P022.Wave1.SharpBoundsBlueprint

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.SharpBounds
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology
noncomputable section

theorem n11_proof : N11 := by
  intro J c e
  let μ : Measure (ℝ × ℝ) := J
  let A : Set (ℝ × ℝ) := {p | c ≤ p.1}
  let B : Set (ℝ × ℝ) := {p | e ≤ p.2}
  change μ.real (A ∩ B) ≤ min (μ.real A) (μ.real B) ∧
    μ.real A + μ.real B - 1 ≤ μ.real (A ∩ B)
  constructor
  · exact le_min (measureReal_mono Set.inter_subset_left) (measureReal_mono Set.inter_subset_right)
  · have hB : MeasurableSet B := measurableSet_le measurable_const measurable_snd
    have hadd := measureReal_union_add_inter (μ := μ) (s := A) hB
    have hle : μ.real (A ∪ B) ≤ 1 := measureReal_le_one
    linarith

end
end AronowAudit.P022.Wave1.SharpBounds
