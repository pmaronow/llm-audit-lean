import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- The finite pushforward identity needs no injectivity of the assignment map. -/
theorem n4_proof : N4 := by
  classical
  have havg (F : Assignment 12 → ℝ) :
      ∑ z, cliqueMass z * F z = (∑ r, F (cliqueAssignments r)) / 66 := by
    unfold cliqueMass
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      (∑ r : Fin 66, ∑ z : Assignment 12,
          (if cliqueAssignments r = z then (1 / 66 : ℝ) else 0) * F z) =
          ∑ r : Fin 66, (1 / 66 : ℝ) * F (cliqueAssignments r) := by
        apply Finset.sum_congr rfl
        intro r _
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      _ = (∑ r, F (cliqueAssignments r)) / 66 := by
        rw [← Finset.mul_sum]
        ring
  change DesignFacts
  refine ⟨?_, ?_, havg⟩
  · intro z
    unfold cliqueMass
    apply Finset.sum_nonneg
    intro r _
    split_ifs <;> norm_num
  · have htotal := havg (fun _ => (1 : ℝ))
    norm_num at htotal
    exact htotal

end

end AronowAudit.P044.Wave1.SimulatedVariance
