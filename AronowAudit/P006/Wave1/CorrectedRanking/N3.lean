import AronowAudit.P006.Wave1.CorrectedRankingBlueprint
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

set_option autoImplicit false
universe u v
namespace AronowAudit.P006.Wave1.CorrectedRanking
open AronowAudit.P006 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
noncomputable section

theorem n3_proof : N3.{u} := by
  intro C _ Q P _ _ hac n hn f hf
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have hρ : Integrable (fun x => (Q.rnDeriv P x).toReal * f x) P :=
    (integrable_toReal_rnDeriv_mul_iff hac).2 hf
  have heq : (fun x => f x * referenceWeight n Q P x) =
      fun x => (n : ℝ)⁻¹ * ((Q.rnDeriv P x).toReal * f x) := by
    funext x
    unfold referenceWeight
    ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hρ.const_mul _
  · rw [heq, integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
    exact integral_toReal_rnDeriv_mul hac

end
end AronowAudit.P006.Wave1.CorrectedRanking
