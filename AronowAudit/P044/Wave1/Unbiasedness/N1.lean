import AronowAudit.P044.Wave1.UnbiasednessBlueprint

namespace AronowAudit.P044.Wave1.Unbiasedness

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- The assignment pushforward is a probability law and preserves every finite expectation. -/
theorem n1_proof : N1 := by
  classical
  have hpush (F : Assignment 4 → ℝ) :
      ∑ z, starMass z * F z = (∑ r : Fin 6, F (starAssignments r)) / 6 := by
    calc
      ∑ z, starMass z * F z =
          ∑ z : Assignment 4, ∑ r : Fin 6,
            (if starAssignments r = z then (1 / 6 : ℝ) else 0) * F z := by
        simp only [starMass, Finset.sum_mul]
      _ = ∑ r : Fin 6, ∑ z : Assignment 4,
            (if starAssignments r = z then (1 / 6 : ℝ) else 0) * F z :=
        Finset.sum_comm
      _ = ∑ r : Fin 6, (1 / 6 : ℝ) * F (starAssignments r) := by
        apply Finset.sum_congr rfl
        intro r _
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      _ = (∑ r : Fin 6, F (starAssignments r)) / 6 := by
        rw [← Finset.mul_sum]
        ring
  refine ⟨?_, ?_, hpush⟩
  · intro z
    unfold starMass
    apply Finset.sum_nonneg
    intro r _
    split_ifs <;> norm_num
  · have htotal := hpush (fun _ => (1 : ℝ))
    norm_num at htotal
    exact htotal

end

end AronowAudit.P044.Wave1.Unbiasedness
