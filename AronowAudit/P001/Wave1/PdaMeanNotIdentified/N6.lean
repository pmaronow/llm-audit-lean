import AronowAudit.P001.Wave1.PdaMeanNotIdentifiedBlueprint
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N2
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N4

namespace AronowAudit.P001.Wave1.PdaMeanNotIdentified

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidablePdaMeanNotIdentifiedN6 (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem n6_proof : N6 := by
  letI : IsProbabilityMeasure gapMarginal := n2_proof.1
  letI : IsProbabilityMeasure (uniformLaw (-1) 1) := n4_proof.1
  have hyi : Integrable (fun y : ℝ => y) (uniformLaw (-1) 1) := by
    apply Integrable.of_bound measurable_id'.aestronglyMeasurable 1
    filter_upwards [n4_proof.2] with y hy
    simpa only [Real.norm_eq_abs] using abs_le.mpr hy
  have hym : (∫ y, y ∂uniformLaw (-1) 1) = 0 := by
    rw [uniformLaw_neg_one_one_eq_smul_restrict, integral_smul_measure,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), integral_id]
    norm_num
  change Integrable Prod.snd (gapMarginal.prod (uniformLaw (-1) 1)) ∧ _
  refine ⟨hyi.comp_snd gapMarginal, ?_⟩
  intro A hA
  have hevent : (Prod.fst ⁻¹' A : Set (ℝ × ℝ)) = A ×ˢ Set.univ := by
    ext xy
    simp
  change (∫ xy in Prod.fst ⁻¹' A, xy.2 ∂gapMarginal.prod (uniformLaw (-1) 1)) = 0
  rw [hevent, ← Measure.prod_restrict, Measure.restrict_univ,
    integral_fun_snd (fun y : ℝ => y), hym, smul_zero]

end
end AronowAudit.P001.Wave1.PdaMeanNotIdentified
