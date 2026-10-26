import AronowAudit.P029.Wave1.PackageWeightedFitBlueprint

namespace AronowAudit.P029.Wave1.PackageWeightedFit

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

/-- All sixteen likelihood factors and observation weights are strictly positive. -/
theorem n1_proof : N1 := by
  have hinterior (q : Theta) (x z : Bool) :
      0 < q.val (x, z) ∧ q.val (x, z) < 1 := by
    obtain ⟨h0, h01, h1⟩ := q.property x
    cases z with
    | false => exact ⟨h0, lt_trans h01 h1⟩
    | true => exact ⟨lt_trans h0 h01, h1⟩
  constructor
  · intro q i
    obtain ⟨h0, h1⟩ := hinterior q i.1 i.2.1
    unfold lik bernoulliFactor
    exact mul_pos (pow_pos h0 _) (pow_pos (sub_pos.mpr h1) _)
  · intro i
    unfold obsW
    split <;> norm_num

end

end AronowAudit.P029.Wave1.PackageWeightedFit
