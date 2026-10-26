import AronowAudit.P013.Wave1.PrintedWald.N8
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.PrintedWald

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- The other unit of the same pair, at the even size 2k+4. -/
private def evenMate (k : ℕ) (i : Fin (2 * k + 3 + 1)) : Fin (2 * k + 3 + 1) :=
  ⟨2 * (i.val / 2) + (1 - i.val % 2), by have hi := i.isLt; omega⟩

private theorem evenMate_pair (k : ℕ) (i : Fin (2 * k + 3 + 1)) :
    i.val / 2 = (evenMate k i).val / 2 := by
  dsimp [evenMate]
  omega

private theorem evenMate_ne (k : ℕ) (i : Fin (2 * k + 3 + 1)) : i ≠ evenMate k i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [evenMate] at hv
  omega

private theorem evenMate_unique (k : ℕ) (i j : Fin (2 * k + 3 + 1))
    (hpair : i.val / 2 = j.val / 2) (hne : i ≠ j) : j = evenMate k i := by
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  apply Fin.ext
  dsimp [evenMate]
  omega

/-- Group the even-size unit set into its k+2 ordered pairs. -/
private def evenUnitEquiv (k : ℕ) : Fin (k + 2) × Fin 2 ≃ Fin (2 * k + 3 + 1) :=
  (finProdFinEquiv : Fin (k + 2) × Fin 2 ≃ Fin ((k + 2) * 2)).trans
    (finCongr (by omega : (k + 2) * 2 = 2 * k + 3 + 1))

/-- On the split event the cross-exposure sum over positive joint probabilities
has one nonzero term per pair. -/
theorem n10_proof : N10 := by
  classical
  intro h1 h7 k z hz
  let q : ℝ := 1 / 2 - pairEpsilon (2 * k + 4)
  let C : ℝ := 1 / q - 4
  obtain ⟨he0, he1⟩ := pairEpsilon_even_bounds k
  have hq : 0 < q := by dsimp [q]; linarith
  have hbits : ∀ a b : Fin 2, a ≠ b → (a = 1 ↔ b = 0) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hbitcount : ∀ a b : Fin 2, a ≠ b →
      (if a = 1 then (1 : ℝ) else 0) + (if b = 1 then (1 : ℝ) else 0) = 1 := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  -- For fixed i, every term other than its mate has zero covariance numerator.
  have hrow : ∀ i : Fin (2 * k + 3 + 1),
      (∑ j ∈ univ.erase i, if 0 < jointPi (wPop (2 * k + 3)) i j 1 0 then
        pairTerm (wPop (2 * k + 3)) i j 1 0 z else 0) =
      C * indicator (wPop (2 * k + 3)).exposure i 1 z := by
    intro i
    calc
      (∑ j ∈ univ.erase i, if 0 < jointPi (wPop (2 * k + 3)) i j 1 0 then
          pairTerm (wPop (2 * k + 3)) i j 1 0 z else 0) =
          if 0 < jointPi (wPop (2 * k + 3)) i (evenMate k i) 1 0 then
            pairTerm (wPop (2 * k + 3)) i (evenMate k i) 1 0 z else 0 := by
        apply Finset.sum_eq_single (evenMate k i)
        · intro j hj hjmate
          have hij : i ≠ j := (mem_erase.mp hj).1.symm
          have hpair : i.val / 2 ≠ j.val / 2 := by
            intro hpair
            exact hjmate (evenMate_unique k i j hpair hij)
          have hJ : jointPi (wPop (2 * k + 3)) i j 1 0 = 1 / 4 := by
            rw [h7 k i j 1 0 hij, if_neg hpair]
          rw [if_pos (wDistinct_joint_pos h7 k i j 1 0 hij)]
          unfold pairTerm
          rw [hJ, h1 (2 * k + 3) i 1, h1 (2 * k + 3) j 0]
          norm_num
        · intro hm
          exact (hm (mem_erase.mpr ⟨(evenMate_ne k i).symm, mem_univ _⟩)).elim
      _ = C * indicator (wPop (2 * k + 3)).exposure i 1 z := by
        rw [if_pos (wDistinct_joint_pos h7 k i (evenMate k i) 1 0 (evenMate_ne k i))]
        have hJ : jointPi (wPop (2 * k + 3)) i (evenMate k i) 1 0 = q := by
          rw [h7 k i (evenMate k i) 1 0 (evenMate_ne k i),
            if_pos (evenMate_pair k i), if_neg (by decide : (1 : Fin 2) ≠ 0)]
        by_cases hi : (wPop (2 * k + 3)).exposure z i = 1
        · have hj : (wPop (2 * k + 3)).exposure z (evenMate k i) = 0 :=
            (hbits _ _ (hz i (evenMate k i) (evenMate_pair k i) (evenMate_ne k i))).mp hi
          simp only [pairTerm, hJ, h1 (2 * k + 3) i 1,
            h1 (2 * k + 3) (evenMate k i) 0, indicator, hi, hj, if_true,
            one_mul, mul_one]
          calc
            _ = (4 - 1 / q) * ((wPop (2 * k + 3)).outcome i 1 *
                (wPop (2 * k + 3)).outcome (evenMate k i) 0) := by
              field_simp [ne_of_gt hq] <;> ring
            _ = C := by
              rw [wOutcome_mul_same_pair (2 * k + 3) i (evenMate k i) 1 0
                (evenMate_pair k i) (evenMate_ne k i)]
              dsimp [C]
              ring
        · simp [pairTerm, indicator, hi]
  -- Each split pair contains exactly one treated unit.
  have htreated : (∑ i, indicator (wPop (2 * k + 3)).exposure i 1 z) = (k : ℝ) + 2 := by
    let e := evenUnitEquiv k
    calc
      (∑ i, indicator (wPop (2 * k + 3)).exposure i 1 z) = ∑ _b : Fin (k + 2), (1 : ℝ) := by
        rw [← Equiv.sum_comp e (fun i => indicator (wPop (2 * k + 3)).exposure i 1 z),
          Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro b _
        rw [Fin.sum_univ_two]
        have hpair : (e (b, 0)).val / 2 = (e (b, 1)).val / 2 := by
          change (0 + 2 * b.val) / 2 = (1 + 2 * b.val) / 2
          omega
        have hne : e (b, 0) ≠ e (b, 1) := by
          intro h
          have hsecond := congrArg (fun p : Fin (k + 2) × Fin 2 => p.2) (e.injective h)
          norm_num at hsecond
        simpa only [indicator] using hbitcount _ _ (hz (e (b, 0)) (e (b, 1)) hpair hne)
      _ = (k : ℝ) + 2 := by simp
  calc
    (∑ i, ∑ j ∈ univ.erase i, if 0 < jointPi (wPop (2 * k + 3)) i j 1 0 then
        pairTerm (wPop (2 * k + 3)) i j 1 0 z else 0) =
        ∑ i, C * indicator (wPop (2 * k + 3)).exposure i 1 z := by
      apply Finset.sum_congr rfl
      intro i _
      exact hrow i
    _ = C * ∑ i, indicator (wPop (2 * k + 3)).exposure i 1 z := (Finset.mul_sum _ _ _).symm
    _ = ((k : ℝ) + 2) * (1 / (1 / 2 - pairEpsilon (2 * k + 4)) - 4) := by
      rw [htreated]
      dsimp [C, q]
      ring

end

end AronowAudit.P013.Wave1.PrintedWald
