import AronowAudit.P013.Wave1.PrintedWaldBlueprint
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.PrintedWald

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- Group the individual HT difference scores by their randomization coordinate.
The last fibre has one unit precisely when the population size is odd. -/
theorem n3_proof : N3 := by
  classical
  intro h1 n z
  let zs : Fin (wCoords n) → Fin 4 := (wEquiv n).symm z
  let score : Fin (n + 1) → ℝ := fun i =>
    2 * (2 * ((pairExposure (zs (wIndex n i)) (decide (i.val % 2 = 1))).val : ℝ) - 1) *
      (if i.val % 2 = 0 then 1 else -1)
  have hunit (i : Fin (n + 1)) :
      indicator (wPop n).exposure i 1 z * ((wPop n).outcome i 1 / pi (wPop n) i 1) -
        indicator (wPop n).exposure i 0 z * ((wPop n).outcome i 0 / pi (wPop n) i 0) =
          score i := by
    rw [h1 n i 1, h1 n i 0]
    change (if pairExposure (zs (wIndex n i)) (decide (i.val % 2 = 1)) = 1 then 1 else 0) *
        ((if i.val % 2 = 0 then (1 : ℝ) else -1) / (1 / 2 : ℝ)) -
      (if pairExposure (zs (wIndex n i)) (decide (i.val % 2 = 1)) = 0 then 1 else 0) *
        ((if i.val % 2 = 0 then (1 : ℝ) else -1) / (1 / 2 : ℝ)) = score i
    dsimp only [score]
    generalize pairExposure (zs (wIndex n i)) (decide (i.val % 2 = 1)) = a
    fin_cases a <;> by_cases hp : i.val % 2 = 0 <;> norm_num [hp]
  have hscale : ((n : ℝ) + 1) * htEffect (wPop n) 1 0 z = ∑ i, score i := by
    calc
      ((n : ℝ) + 1) * htEffect (wPop n) 1 0 z =
          htTotal (wPop n) 1 z - htTotal (wPop n) 0 z := by
        unfold htEffect
        have hN : (n : ℝ) + 1 ≠ 0 := by positivity
        push_cast
        field_simp [hN] <;> ring
      _ = ∑ i, score i := by
        unfold htTotal
        rw [← sum_sub_distrib]
        exact sum_congr rfl (fun i _ => hunit i)
  rw [hscale]
  change (∑ i, score i) = ∑ b, coordScore n b (zs b)
  calc
    (∑ i, score i) = ∑ b, ∑ i ∈ univ.filter (fun i => wIndex n i = b), score i :=
      (sum_fiberwise (univ : Finset (Fin (n + 1))) (wIndex n) score).symm
    _ = ∑ b, coordScore n b (zs b) := by
      apply sum_congr rfl
      intro b _
      have hb : b.val < (n + 2) / 2 := b.isLt
      have hfirst : 2 * b.val < n + 1 := by omega
      let i0 : Fin (n + 1) := ⟨2 * b.val, hfirst⟩
      have hindex0 : wIndex n i0 = b := by
        apply Fin.ext
        dsimp only [wIndex, i0]
        omega
      have hparity0 : i0.val % 2 = 0 := by dsimp only [i0]; omega
      have hscore0 : score i0 =
          2 * (2 * ((pairExposure (zs b) false).val : ℝ) - 1) := by
        simp [score, hindex0, hparity0]
      by_cases hfull : 2 * b.val + 1 < n + 1
      · let i1 : Fin (n + 1) := ⟨2 * b.val + 1, hfull⟩
        have hindex1 : wIndex n i1 = b := by
          apply Fin.ext
          dsimp only [wIndex, i1]
          omega
        have hparity1 : i1.val % 2 = 1 := by dsimp only [i1]; omega
        have hscore1 : score i1 =
            -(2 * (2 * ((pairExposure (zs b) true).val : ℝ) - 1)) := by
          simp [score, hindex1, hparity1]
        have hne : i0 ≠ i1 := by
          intro h
          have hv := congrArg Fin.val h
          dsimp only [i0, i1] at hv
          omega
        have hfibre : univ.filter (fun i : Fin (n + 1) => wIndex n i = b) =
            {i0, i1} := by
          ext i
          simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
            Fin.ext_iff, wIndex]
          dsimp only [i0, i1]
          omega
        have hsum : (∑ i ∈ univ.filter (fun i => wIndex n i = b), score i) =
            score i0 + score i1 := by
          rw [hfibre]
          simp [hne]
        rw [hsum, hscore0, hscore1]
        simp only [coordScore, if_pos hfull]
        ring
      · have hfibre : univ.filter (fun i : Fin (n + 1) => wIndex n i = b) =
            {i0} := by
          ext i
          have hi := i.isLt
          simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff, wIndex]
          dsimp only [i0]
          omega
        rw [hfibre, sum_singleton, hscore0]
        simp only [coordScore, if_neg hfull]

end

end AronowAudit.P013.Wave1.PrintedWald
