import AronowAudit.P013.Wave1.PrintedWaldBlueprint

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.PrintedWald

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- At the even sizes, distinct units on one coordinate use opposite bits; units
on different coordinates have product joint probabilities. -/
theorem n7_proof : N7 := by
  classical
  intro k i j d e hne
  let n : ℕ := 2 * k + 3
  let P := wAtom n
  let gi : Fin 4 → ℝ := fun a =>
    if pairExposure a (decide (i.val % 2 = 1)) = d then 1 else 0
  let gj : Fin 4 → ℝ := fun a =>
    if pairExposure a (decide (j.val % 2 = 1)) = e then 1 else 0
  have hmax : max 4 (n + 1) = 2 * k + 4 := by dsimp [n]; omega
  have hei : expectation P gi = 1 / 2 := by
    by_cases hi : i.val % 2 = 1 <;> fin_cases d <;>
      norm_num [P, wAtom, gi, expectation, pairAtomDesign, pairExposure, hi,
        Fin.sum_univ_succ] <;> ring
  have hej : expectation P gj = 1 / 2 := by
    by_cases hj : j.val % 2 = 1 <;> fin_cases e <;>
      norm_num [P, wAtom, gj, expectation, pairAtomDesign, pairExposure, hj,
        Fin.sum_univ_succ] <;> ring
  change jointPi (relabelPopulation (wBasePop n) (wEquiv n)) i j d e = _
  rw [jointPi_relabel]
  change expectation (replicateDesign P (wCoords n))
    (fun zs => gi (zs (wIndex n i)) * gj (zs (wIndex n j))) = _
  by_cases hquot : i.val / 2 = j.val / 2
  · rw [if_pos hquot]
    have hindex : wIndex n i = wIndex n j := Fin.ext hquot
    simp only [hindex]
    rw [replicate_marginal P (wCoords n) (wIndex n j) (fun a => gi a * gj a)]
    have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
    by_cases hi : i.val % 2 = 1
    · have hj : j.val % 2 ≠ 1 := by omega
      fin_cases d <;> fin_cases e <;>
        norm_num [P, wAtom, gi, gj, expectation, pairAtomDesign, pairExposure,
          hi, hj, hmax, Fin.sum_univ_succ]
    · have hj : j.val % 2 = 1 := by omega
      fin_cases d <;> fin_cases e <;>
        norm_num [P, wAtom, gi, gj, expectation, pairAtomDesign, pairExposure,
          hi, hj, hmax, Fin.sum_univ_succ]
  · have hindex : wIndex n i ≠ wIndex n j := by
      intro h
      exact hquot (congrArg Fin.val h)
    rw [if_neg hquot,
      replicate_pair_marginal P (wCoords n) _ _ hindex gi gj, hei, hej]
    norm_num

end

end AronowAudit.P013.Wave1.PrintedWald
