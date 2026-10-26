import AronowAudit.P001.Wave1.PdaMeanNotIdentifiedBlueprint
import Mathlib.Topology.Piecewise

namespace AronowAudit.P001.Wave1.PdaMeanNotIdentified

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidablePdaMeanNotIdentifiedN9 (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem n9_proof : N9 := by
  have hp : Continuous (fun x : ℝ => 1 - 6 * x ^ 2 + 5 * x ^ 4) := by
    fun_prop
  unfold N9 pdaBumpDeriv
  apply Continuous.if _ hp continuous_const
  intro x hx
  have hxabs : |x| = 1 := (frontier_lt_subset_eq continuous_abs continuous_const) hx
  rcases (abs_eq zero_le_one).mp hxabs with hx | hx
  · rw [hx]
    norm_num
  · rw [hx]
    norm_num

end
end AronowAudit.P001.Wave1.PdaMeanNotIdentified
