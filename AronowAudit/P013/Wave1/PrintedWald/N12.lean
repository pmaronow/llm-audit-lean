import AronowAudit.P013.Wave1.PrintedWaldBlueprint
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.PrintedWald

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- A union bound over the k+2 coordinates bounds failure of the all-split event. -/
theorem n12_proof : N12 := by
  classical
  intro k
  let n : ℕ := 2 * k + 3
  have hmax : max 4 (n + 1) = 2 * k + 4 := by dsimp [n]; omega
  have hcoords : wCoords n = k + 2 := by dsimp [wCoords, n]; omega
  have hbits : ∀ a : Fin 4, a ≠ 0 → a ≠ 3 →
      pairExposure a false ≠ pairExposure a true := by
    intro a h0 h3
    fin_cases a <;> simp_all [pairExposure]
  -- If every coordinate is 01 or 10, the two distinct units in any pair differ.
  have hcover : ∀ zs : Fin (wCoords n) → Fin 4,
      ¬ wSplit n ((wEquiv n) zs) → ∃ b, zs b = 0 ∨ zs b = 3 := by
    intro zs hfail
    by_contra hbad
    apply hfail
    intro i j hpair hij
    have hcoord : wIndex n i = wIndex n j := Fin.ext hpair
    have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have h0 : zs (wIndex n i) ≠ 0 := fun h => hbad ⟨wIndex n i, Or.inl h⟩
    have h3 : zs (wIndex n i) ≠ 3 := fun h => hbad ⟨wIndex n i, Or.inr h⟩
    change pairExposure (((wEquiv n).symm ((wEquiv n) zs)) (wIndex n i))
        (decide (i.val % 2 = 1)) ≠
      pairExposure (((wEquiv n).symm ((wEquiv n) zs)) (wIndex n j))
        (decide (j.val % 2 = 1))
    simp only [Equiv.symm_apply_apply]
    rw [← hcoord]
    by_cases hi : i.val % 2 = 1
    · have hj : j.val % 2 ≠ 1 := by omega
      simpa [hi, hj] using (hbits (zs (wIndex n i)) h0 h3).symm
    · have hj : j.val % 2 = 1 := by omega
      simpa [hi, hj] using hbits (zs (wIndex n i)) h0 h3
  -- Finite union bound, proved directly for the finite weighted probability.
  have hunion : probability (wBase n) (fun zs => ∃ b, zs b = 0 ∨ zs b = 3) ≤
      ∑ b : Fin (wCoords n), probability (wBase n) (fun zs => zs b = 0 ∨ zs b = 3) := by
    letI (zs : Fin (wCoords n) → Fin 4) : Decidable (∃ b, zs b = 0 ∨ zs b = 3) :=
      Classical.propDecidable _
    letI (zs : Fin (wCoords n) → Fin 4) (b : Fin (wCoords n)) :
        Decidable (zs b = 0 ∨ zs b = 3) := Classical.propDecidable _
    unfold probability
    calc
      (∑ zs, if (∃ b, zs b = 0 ∨ zs b = 3) then (wBase n).weight zs else 0) ≤
          ∑ zs, ∑ b : Fin (wCoords n),
            if zs b = 0 ∨ zs b = 3 then (wBase n).weight zs else 0 := by
        apply Finset.sum_le_sum
        intro zs _
        have hnonneg : ∀ b : Fin (wCoords n),
            0 ≤ (if zs b = 0 ∨ zs b = 3 then (wBase n).weight zs else 0) := by
          intro b
          split_ifs
          · exact ((wBase n).positive zs).le
          · exact le_rfl
        by_cases hbad : ∃ b, zs b = 0 ∨ zs b = 3
        · rw [if_pos hbad]
          obtain ⟨b, hb⟩ := hbad
          have hs : (if zs b = 0 ∨ zs b = 3 then (wBase n).weight zs else 0) ≤
              ∑ a : Fin (wCoords n),
                if zs a = 0 ∨ zs a = 3 then (wBase n).weight zs else 0 :=
            Finset.single_le_sum (fun a _ => hnonneg a) (mem_univ b)
          simpa only [if_pos hb] using hs
        · rw [if_neg hbad]
          exact Finset.sum_nonneg (fun b _ => hnonneg b)
      _ = ∑ b : Fin (wCoords n), ∑ zs,
          if zs b = 0 ∨ zs b = 3 then (wBase n).weight zs else 0 := Finset.sum_comm
  -- Each coordinate is unsplit with probability ε+ε; use the product marginal.
  have hmarg : ∀ b : Fin (wCoords n),
      probability (wBase n) (fun zs => zs b = 0 ∨ zs b = 3) =
        2 * pairEpsilon (2 * k + 4) := by
    intro b
    have hprob : probability (wBase n) (fun zs => zs b = 0 ∨ zs b = 3) =
        expectation (wBase n) (fun zs => if zs b = 0 ∨ zs b = 3 then (1 : ℝ) else 0) := by
      unfold probability expectation
      apply Finset.sum_congr rfl
      intro zs _
      by_cases h : zs b = 0 ∨ zs b = 3 <;> simp [h]
    rw [hprob]
    change expectation (replicateDesign (wAtom n) (wCoords n))
      (fun zs => if zs b = 0 ∨ zs b = 3 then (1 : ℝ) else 0) = _
    rw [replicate_marginal (wAtom n) (wCoords n) b
      (fun a : Fin 4 => if a = 0 ∨ a = 3 then (1 : ℝ) else 0)]
    norm_num [expectation, wAtom, hmax, pairAtomDesign, Fin.sum_univ_succ] <;> ring
  change probability (wDesign n) (fun z => ¬ wSplit n z) ≤ 1 / (2 * (k : ℝ) + 4)
  calc
    probability (wDesign n) (fun z => ¬ wSplit n z) =
        probability (wBase n) (fun zs => ¬ wSplit n ((wEquiv n) zs)) :=
      probability_relabel (wBase n) (wEquiv n) (fun z => ¬ wSplit n z)
    _ ≤ probability (wBase n) (fun zs => ∃ b, zs b = 0 ∨ zs b = 3) :=
      probability_mono (wBase n) _ _ hcover
    _ ≤ ∑ b : Fin (wCoords n), probability (wBase n) (fun zs => zs b = 0 ∨ zs b = 3) := hunion
    _ = ((k : ℝ) + 2) * (2 * pairEpsilon (2 * k + 4)) := by
      simp [hmarg, hcoords, nsmul_eq_mul]
    _ = 1 / (2 * (k : ℝ) + 4) := by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hN : 2 * (k : ℝ) + 4 ≠ 0 := by positivity
      unfold pairEpsilon
      push_cast
      field_simp [hN] <;> ring

end

end AronowAudit.P013.Wave1.PrintedWald
