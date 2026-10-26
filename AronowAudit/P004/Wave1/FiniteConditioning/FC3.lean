import AronowAudit.P004.Wave1.FiniteConditioning.FC1
import AronowAudit.P004.Wave1.FiniteConditioning.FC2

namespace AronowAudit.P004.Wave1.FiniteConditioning

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Averaging the complement and then the retained coordinates averages the whole cube. -/
theorem fc3_proof : FC3 := by
  classical
  intro N p hp J U
  let S : Set (Fin N) := J
  have hdep : DependsOn (conditionOn p J U) S := by
    intro z z' hzz'
    exact fc1_proof p J U z z' hzz'
  rw [GraphCompletion.expect_left p S (conditionOn p J U) hdep,
    GraphCompletion.expect_split p S U]
  apply Finset.sum_congr rfl
  intro a _
  have hrestrict :
      (fun j : (J : Set (Fin N)) =>
        GraphCompletion.join S a (fun _ => false) j) = a := by
    funext j
    exact GraphCompletion.join_left S a (fun _ => false) j
  rw [conditionOn_eq_sum p hp J]
  rw [hrestrict, Finset.mul_sum]
  refine Finset.sum_congr (by congr 1 <;> exact Subsingleton.elim _ _) (fun b _ => ?_)
  rw [← mul_assoc]
  congr!

end
end AronowAudit.P004.Wave1.FiniteConditioning
