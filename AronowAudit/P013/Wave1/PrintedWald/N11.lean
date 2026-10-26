import AronowAudit.P013.Wave1.PrintedWald.N8

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.PrintedWald

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- In expression (10), precisely the same-unit cross-exposure joints are zero. -/
theorem n11_proof : N11 := by
  classical
  intro h1 h7 k z
  have hterm : ∀ i j : Fin (2 * k + 3 + 1),
      (if jointPi (wPop (2 * k + 3)) i j 1 0 = 0 then
        indicator (wPop (2 * k + 3)).exposure i 1 z *
            (wPop (2 * k + 3)).outcome i 1 ^ 2 / (2 * pi (wPop (2 * k + 3)) i 1) +
          indicator (wPop (2 * k + 3)).exposure j 0 z *
            (wPop (2 * k + 3)).outcome j 0 ^ 2 / (2 * pi (wPop (2 * k + 3)) j 0)
       else 0) =
      if j = i then indicator (wPop (2 * k + 3)).exposure i 1 z +
        indicator (wPop (2 * k + 3)).exposure i 0 z else 0 := by
    intro i j
    by_cases hji : j = i
    · subst j
      simp [wJoint_self_cross_zero, h1 (2 * k + 3) i 1,
        h1 (2 * k + 3) i 0, wOutcome_sq]
    · have hpos : 0 < jointPi (wPop (2 * k + 3)) i j 1 0 :=
        wDistinct_joint_pos h7 k i j 1 0 (Ne.symm hji)
      simp only [if_neg (ne_of_gt hpos), if_neg hji]
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_add_distrib, indicator_sum_fin_two]
  push_cast
  ring

end

end AronowAudit.P013.Wave1.PrintedWald
