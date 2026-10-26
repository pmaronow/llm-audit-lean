import AronowAudit.P001.Wave1.PdaMeanNotIdentifiedBlueprint

namespace AronowAudit.P001.Wave1.PdaMeanNotIdentified

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidablePdaMeanNotIdentifiedN7 (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem n7_proof : N7 := by
  intro x hx
  rcases lt_or_gt_of_ne hx with hin | hout
  · have hpoly : HasDerivAt (fun y : ℝ => y * (1 - y ^ 2) ^ 2)
        (1 - 6 * x ^ 2 + 5 * x ^ 4) x := by
      have hp := (hasDerivAt_id' x).mul ((((hasDerivAt_id' x).pow 2).const_sub 1).pow 2)
      exact hp.congr_deriv (by norm_num <;> ring)
    have heq : pdaBump =ᶠ[nhds x] (fun y : ℝ => y * (1 - y ^ 2) ^ 2) := by
      have hnb : {y : ℝ | |y| < 1} ∈ nhds x :=
        (isOpen_lt continuous_abs continuous_const).mem_nhds hin
      filter_upwards [hnb] with y hy
      simp only [pdaBump, if_pos hy]
    simpa only [pdaBumpDeriv, if_pos hin] using hpoly.congr_of_eventuallyEq heq
  · have heq : pdaBump =ᶠ[nhds x] (fun _ : ℝ => (0 : ℝ)) := by
      have hnb : {y : ℝ | 1 < |y|} ∈ nhds x :=
        (isOpen_lt continuous_const continuous_abs).mem_nhds hout
      filter_upwards [hnb] with y hy
      simp only [pdaBump, if_neg (not_lt.mpr hy.le)]
    simpa only [pdaBumpDeriv, if_neg (not_lt.mpr hout.le)] using
      (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq

end
end AronowAudit.P001.Wave1.PdaMeanNotIdentified
