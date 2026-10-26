import AronowAudit.P002.Wave1.E61EigenvalueBlueprint
import Mathlib.Analysis.SpecialFunctions.Exp

namespace AronowAudit.P002.Wave1.E61Eigenvalue
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- A polynomial times a decaying exponential is summable, also on an injective subsequence. -/
theorem n8_proof : N8 := by
  intro sizes sub hsizes hsub c hc
  have hlinear : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-c * n)) := by
    simpa only [pow_one] using Real.summable_pow_mul_exp_neg_nat_mul 1 hc
  have hconstant : Summable (fun n : ℕ => Real.exp (-c * n)) := by
    simpa only [pow_zero, one_mul] using Real.summable_pow_mul_exp_neg_nat_mul 0 hc
  have hall : Summable (fun n : ℕ => 2 * ((n : ℝ) + 1) * Real.exp (-c * n)) := by
    refine ((hlinear.add hconstant).mul_left (2 : ℝ)).congr ?_
    intro n
    ring
  simpa only [Function.comp_def] using
    hall.comp_injective (hsizes.comp hsub).injective

end
end AronowAudit.P002.Wave1.E61Eigenvalue
