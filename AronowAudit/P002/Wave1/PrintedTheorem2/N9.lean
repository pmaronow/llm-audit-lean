import AronowAudit.P002.Wave1.PrintedTheorem2Blueprint
import Mathlib.Algebra.BigOperators.Fin

namespace AronowAudit.P002.Wave1.PrintedTheorem2
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- The centered grid supplies a member of the fixed Xi class at every estimand. -/
theorem n9_proof : N9 := by
  intro n hn β
  let P := degenerateCovModel n β
  have hN2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hN : (n : ℝ) ≠ 0 := ne_of_gt hNpos
  have hTheta : Theta P.pop 0 (1/4) (1/2) :=
    (degenerate_model_admissible n hn β).1
  have hlate : late P.pop = β := (degenerate_model_admissible n hn β).2

  -- Real-valued Gauss sums avoid natural subtraction and division during casting.
  have hsumRange1 (m : ℕ) :
      (∑ i ∈ Finset.range m, (i : ℝ)) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hsumRange2 (m : ℕ) :
      (∑ i ∈ Finset.range m, (i : ℝ) ^ 2) =
        (m : ℝ) * ((m : ℝ) - 1) * (2 * (m : ℝ) - 1) / 6 := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hsum1 :
      (∑ i : Fin n, (i.val : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact hsumRange1 n
  have hsum2 :
      (∑ i : Fin n, (i.val : ℝ) ^ 2) =
        (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
    exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ℝ) ^ 2) n).trans
      (hsumRange2 n)
  have hx (i : Fin n) :
      gridX i 0 = (2 * (i.val : ℝ) + 1 - (n : ℝ)) / (n : ℝ) := by
    unfold gridX
    ring
  have hcenter : (∑ i : Fin n, gridX i 0) = 0 := by
    simp_rw [hx]
    rw [← Finset.sum_div]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum1]
    ring
  have hxsq (i : Fin n) :
      gridX i 0 ^ 2 =
        (4 * (i.val : ℝ) ^ 2 + 4 * (1 - (n : ℝ)) * (i.val : ℝ) +
          (1 - (n : ℝ)) ^ 2) / (n : ℝ) ^ 2 := by
    rw [hx, div_pow]
    congr 1
    ring
  have hsecond : mean (fun i : Fin n => gridX i 0 ^ 2) =
      ((n : ℝ) ^ 2 - 1) / (3 * (n : ℝ) ^ 2) := by
    unfold mean
    simp_rw [hxsq]
    rw [← Finset.sum_div]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum1, hsum2]
    field_simp [hN] <;> ring
  have hQ : (1 / 4 : ℝ) ≤ mean (fun i : Fin n => gridX i 0 ^ 2) := by
    rw [hsecond]
    apply (le_div_iff₀ (show (0 : ℝ) < 3 * (n : ℝ) ^ 2 by positivity)).2
    have hNsq : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith only [hN2, sq_nonneg ((n : ℝ) - 2)]
    nlinarith only [hNsq]

  have hfourthPoint (i : Fin n) : gridX i 0 ^ 4 ≤ 1 := by
    have hi0 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
    have hiN : (i.val : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt i.isLt
    have hxLo : (-1 : ℝ) ≤ gridX i 0 := by
      rw [hx]
      apply (le_div_iff₀ hNpos).2
      linarith
    have hxHi : gridX i 0 ≤ (1 : ℝ) := by
      rw [hx]
      apply (div_le_iff₀ hNpos).2
      linarith
    have hsq : gridX i 0 ^ 2 ≤ (1 : ℝ) := by
      nlinarith only [mul_nonneg (show 0 ≤ 1 - gridX i 0 by linarith)
        (show 0 ≤ 1 + gridX i 0 by linarith)]
    nlinarith only [mul_nonneg (show 0 ≤ 1 - gridX i 0 ^ 2 by linarith)
      (show 0 ≤ 1 + gridX i 0 ^ 2 by positivity)]
  have hfourth : mean (fun i : Fin n => gridX i 0 ^ 4) ≤ (1 : ℝ) := by
    unfold mean
    apply (div_le_iff₀ hNpos).2
    have hsum := Finset.sum_le_sum
      (fun (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) => hfourthPoint i)
    simpa using hsum
  have hrayleigh (b : Fin 1 → ℝ) :
      (1 / 4 : ℝ) * normSq b ≤ mean (fun i : Fin n => (dotProduct (gridX i) b) ^ 2) := by
    have hfactor : mean (fun i : Fin n => (dotProduct (gridX i) b) ^ 2) =
        mean (fun i : Fin n => gridX i 0 ^ 2) * b 0 ^ 2 := by
      simp only [mean, dotProduct, Fin.sum_univ_one, mul_pow]
      rw [← Finset.sum_mul]
      ring
    rw [hfactor]
    simpa only [normSq, Fin.sum_univ_one] using
      mul_le_mul_of_nonneg_right hQ (sq_nonneg (b 0))

  -- Only the population fit is used here; its Gram matrix is diagonal and invertible.
  have hgram : gram P.x Finset.univ =
      Matrix.diagonal (fun s : Option (Fin 1) =>
        if s = none then (1 : ℝ) else mean (fun i : Fin n => gridX i 0 ^ 2)) := by
    ext s t
    rcases s with _ | s <;> rcases t with _ | t
    · simp [gram, groupMean, augmented, Matrix.diagonal_apply, hN]
    · fin_cases t
      simp [gram, groupMean, augmented, P, degenerateCovModel,
        Matrix.diagonal_apply, hcenter]
    · fin_cases s
      simp [gram, groupMean, augmented, P, degenerateCovModel,
        Matrix.diagonal_apply, hcenter]
    · fin_cases s
      fin_cases t
      simp [gram, groupMean, augmented, P, degenerateCovModel,
        Matrix.diagonal_apply, mean, pow_two]
  have hdet : (gram P.x Finset.univ).det ≠ 0 := by
    rw [hgram, Matrix.det_diagonal]
    have hQpos : 0 < mean (fun i : Fin n => gridX i 0 ^ 2) := by linarith
    simpa [Fintype.prod_option, Fin.prod_univ_one] using ne_of_gt hQpos
  have hw (a : Bool) : w P.pop a (late P.pop) = 0 := by
    funext i
    rw [hlate]
    cases a <;> simp [w, binary, P, degenerateCovModel, degenerateModel]
  have hpsi (a : Bool) : psi P a (late P.pop) = 0 := by
    unfold psi
    rw [hw a]
    funext s
    simp [ols, hdet, Matrix.mulVec, dotProduct, score, groupMean]
  have hresidual (a : Bool) : residual P a (late P.pop) = 0 := by
    funext i
    simp [residual, hpsi, hw]

  rcases hTheta with ⟨hdesign, hreceipt, hcompliers, hallocLo, hallocHi, hcov, hmoment⟩
  refine ⟨?_, hlate⟩
  change Xi P 0 (1/4) 4 (1/2) (1/4)
  refine ⟨hdesign, hreceipt, hcompliers, hallocLo, hallocHi, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hresidual, popCov, popVar, mean]
  · intro a
    simp [hresidual, fourthNorm, popVar, mean]
  · intro s
    fin_cases s
    change (∑ i : Fin n, gridX i 0) = 0
    exact hcenter
  · intro s
    fin_cases s
    change mean (fun i : Fin n => gridX i 0 ^ 4) ≤ (4 : ℝ)
    exact hfourth.trans (by norm_num)
  · intro b
    change (1 / 4 : ℝ) * normSq b ≤
      mean (fun i : Fin n => (dotProduct (gridX i) b) ^ 2)
    exact hrayleigh b

end
end AronowAudit.P002.Wave1.PrintedTheorem2
