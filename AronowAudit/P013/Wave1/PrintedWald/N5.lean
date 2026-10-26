import AronowAudit.P013.Wave1.PrintedWaldBlueprint
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Fin

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.PrintedWald

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- Exact all-size variance, obtained from coordinate additivity and the four-atom
moments. The unused second bit on the singleton coordinate changes no moment. -/
theorem n5_proof : N5 := by
  classical
  intro h1 h3 h4 n
  have hmoment (b : Fin (wCoords n)) :
      variance (wAtom n) (coordScore n b) =
        if 2 * b.val + 1 < n + 1 then
          16 * pairSplitProbability (max 4 (n + 1)) else 4 := by
    by_cases hb : 2 * b.val + 1 < n + 1
    · have hscore : coordScore n b = pairScore := by
        funext a
        fin_cases a <;> norm_num [coordScore, hb, pairScore, pairExposure]
      rw [if_pos hb, hscore]
      exact (pair_score_moments (max 4 (n + 1)) (le_max_left 4 (n + 1))).2
    · rw [if_neg hb]
      norm_num [coordScore, hb, wAtom, variance, covariance, expectation,
        pairAtomDesign, pairExposure, Fin.sum_univ_succ] <;> ring
  have hfull :
      (univ.filter (fun b : Fin (wCoords n) => 2 * b.val + 1 < n + 1)).card =
        (n + 1) / 2 := by
    have hf : univ.filter (fun b : Fin (wCoords n) => 2 * b.val + 1 < n + 1) =
        univ.filter (fun b : Fin (wCoords n) => b.val < (n + 1) / 2) := by
      ext b
      simp only [mem_filter, mem_univ, true_and]
      omega
    rw [hf, Fin.card_filter_val_lt, min_eq_right]
    unfold wCoords
    omega
  have hsingle :
      (univ.filter (fun b : Fin (wCoords n) => ¬ (2 * b.val + 1 < n + 1))).card =
        (n + 1) % 2 := by
    have hpartition := card_filter_add_card_filter_not
      (s := (univ : Finset (Fin (wCoords n))))
      (fun b => 2 * b.val + 1 < n + 1)
    rw [hfull, card_univ, Fintype.card_fin] at hpartition
    unfold wCoords at hpartition ⊢
    omega
  have hscale :
      variance (wDesign n) (fun z => ((n : ℝ) + 1) * htEffect (wPop n) 1 0 z) =
        ((n : ℝ) + 1) ^ 2 * variance (wDesign n) (htEffect (wPop n) 1 0) := by
    have h := covariance_mul_const (wDesign n) (htEffect (wPop n) 1 0)
      (htEffect (wPop n) 1 0) ((n : ℝ) + 1) ((n : ℝ) + 1)
    simpa only [variance, pow_two, mul_comm, mul_left_comm, mul_assoc] using h
  have hscore :
      (fun z => ((n : ℝ) + 1) * htEffect (wPop n) 1 0 z) =
        (fun z => ∑ b, coordScore n b ((wEquiv n).symm z b)) := by
    funext z
    exact h3 h1 n z
  have hrelabel :
      variance (wDesign n) (fun z => ∑ b, coordScore n b ((wEquiv n).symm z b)) =
        variance (wBase n) (fun zs => ∑ b, coordScore n b (zs b)) := by
    simp only [variance, covariance, wDesign, expectation_relabel,
      Equiv.symm_apply_apply]
  calc
    ((n : ℝ) + 1) ^ 2 * variance (wDesign n) (htEffect (wPop n) 1 0) =
        variance (wDesign n) (fun z => ((n : ℝ) + 1) * htEffect (wPop n) 1 0 z) :=
      hscale.symm
    _ = variance (wDesign n) (fun z => ∑ b, coordScore n b ((wEquiv n).symm z b)) := by
      rw [hscore]
    _ = variance (wBase n) (fun zs => ∑ b, coordScore n b (zs b)) := hrelabel
    _ = ∑ b, variance (wAtom n) (coordScore n b) :=
      h4 (wAtom n) (wCoords n) (coordScore n)
    _ = ∑ b : Fin (wCoords n), if 2 * b.val + 1 < n + 1 then
        16 * pairSplitProbability (max 4 (n + 1)) else 4 := by
      exact sum_congr rfl (fun b _ => hmoment b)
    _ = 16 * (((n + 1) / 2 : ℕ) : ℝ) * pairSplitProbability (max 4 (n + 1)) +
        4 * (((n + 1) % 2 : ℕ) : ℝ) := by
      rw [sum_ite]
      simp only [sum_const, nsmul_eq_mul, hfull, hsingle]
      ring

end

end AronowAudit.P013.Wave1.PrintedWald
