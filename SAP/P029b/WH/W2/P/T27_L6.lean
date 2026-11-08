import SAP.P029b.WH.W2.Leaves
import AronowAudit.P053.P053_NormalQuantiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory

local instance : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

theorem SAP.P029b.WH.W2.T27_L6_proof : SAP.P029b.WH.W2.T27_L6 := by
  change ∀ p : ℝ, 0 < p → p < 1 → ∃ θ : ℝ, cdf (gaussianReal 0 1) θ = p
  intro p hp0 hp1
  exact AronowAudit.P053.NormalCompletion.exists_cdf_eq
    (gaussianReal 0 1) hp0 hp1
