import AronowAudit.P013.Wave1.PrintedWaldBlueprint

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.PrintedWald

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- Every bit of every coordinate has marginal exposure probability one half. -/
theorem n1_proof : N1 := by
  classical
  intro n i d
  change pi (relabelPopulation (wBasePop n) (wEquiv n)) i d = 1 / 2
  rw [pi_relabel]
  change expectation (replicateDesign (wAtom n) (wCoords n))
    (fun zs => if pairExposure (zs (wIndex n i)) (decide (i.val % 2 = 1)) = d
      then 1 else 0) = 1 / 2
  rw [replicate_marginal (wAtom n) (wCoords n) (wIndex n i)
    (fun a : Fin 4 => if pairExposure a (decide (i.val % 2 = 1)) = d then 1 else 0)]
  by_cases hi : i.val % 2 = 1 <;> fin_cases d <;>
    norm_num [wAtom, expectation, pairAtomDesign, pairExposure, hi,
      Fin.sum_univ_succ] <;> ring

end

end AronowAudit.P013.Wave1.PrintedWald
