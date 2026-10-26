import AronowAudit.P001.Wave1.PdaMeanNotIdentifiedBlueprint
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N2

namespace AronowAudit.P001.Wave1.PdaMeanNotIdentified

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidablePdaMeanNotIdentifiedN3 (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem n3_proof : N3 := by
  letI : IsProbabilityMeasure gapMarginal := n2_proof.1
  have hi : Integrable (fun x : ℝ => x) gapMarginal := by
    apply Integrable.of_bound measurable_id'.aestronglyMeasurable 2
    filter_upwards [n2_proof.2] with x hx
    simpa only [Real.norm_eq_abs] using (n1_proof.2.2.2.1 x hx).2
  have hneg : (∫ x in Set.Icc (-2 : ℝ) (-1), x) = -3 / 2 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ -1), integral_id]
    norm_num
  have hpos : (∫ x in Set.Icc (1 : ℝ) 2, x) = 3 / 2 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2), integral_id]
    norm_num
  refine ⟨hi, ?_⟩
  rw [gapMarginal_eq_smul_restrict, integral_smul_measure,
    setIntegral_union gap_intervals_disjoint measurableSet_Icc
      continuous_id'.integrableOn_Icc
      continuous_id'.integrableOn_Icc,
    hneg, hpos]
  norm_num

end
end AronowAudit.P001.Wave1.PdaMeanNotIdentified
