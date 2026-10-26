import AronowAudit.P013.Wave1.PrintedWald.N8

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.PrintedWald

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- No off-diagonal same-exposure joint is zero, so the A₂ correction vanishes. -/
theorem n9_proof : N9 := by
  classical
  intro h7 k z d
  unfold correctionA2
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  have hpos : 0 < jointPi (wPop (2 * k + 3)) i j d d :=
    wDistinct_joint_pos h7 k i j d d (mem_erase.mp hj).1.symm
  exact if_neg (ne_of_gt hpos)

end

end AronowAudit.P013.Wave1.PrintedWald
