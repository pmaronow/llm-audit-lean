import AronowAudit.P001.Wave1.CausalIpwDrBlueprint

set_option autoImplicit false

universe u v w

namespace AronowAudit.P001.Wave1.CausalIpwDr

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n1_proof : N1.{u, v, w} := by
  intro Ω E F _ _ _ μ X hX U D hCI A B hA hB
  have hcomp : Measurable (fun d : ℝ => 1 - d) := measurable_const.sub measurable_id
  exact hCI A ((fun d : ℝ => 1 - d) ⁻¹' B) hA (hB.preimage hcomp)

end

end AronowAudit.P001.Wave1.CausalIpwDr
