import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

theorem n20_proof : N20 := by
  intro ha hb hc
  change expect (fun _ : Fin 66 => (1 / 66 : ℚ))
    (fun t => cliqueConditionalV t false) = 1040129476423 / 2326402995840
  unfold cliqueConditionalV expectedVariance
  rw [expect_div, expect_sub, expect_add, expect_const_mul]
  rw [ha, hb, hc] <;> norm_num

end

end AronowAudit.P044.Wave1.SimulatedVariance
