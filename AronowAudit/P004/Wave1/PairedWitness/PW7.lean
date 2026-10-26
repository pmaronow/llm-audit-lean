import AronowAudit.P004.Wave1.PairedWitness.PW4

namespace AronowAudit.P004.Wave1.PairedWitness

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators Classical

/-- A half-coin has mean one half, directly from the existing selection identity. -/
theorem pair_expect_bit {N : ℕ} (j : Fin N) :
    expect (fun _ => 1 / 2) (fun z => bit (z j)) = (1 / 2 : ℝ) := by
  have hp : ∀ k : Fin N, 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 := by
    intro k
    norm_num
  have h := bernoulli_positive_power (fun _ : Fin N => (1 / 2 : ℝ))
    (fun _ => (1 : ℝ)) j 1 (by omega) hp
  simpa only [pow_one, mul_one, expect_const] using h

/-- Both arm means, used by PW7 and PW8. -/
theorem pair_marginal {N : ℕ} (hE : Even N) (i : Fin N) (a : Bool) :
    marginal (fun _ => 1 / 2) (pairedTable N) i a = bit a - 1 / 2 := by
  have hp : ∀ k : Fin N, 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 := by
    intro k
    norm_num
  rw [marginal_is_marginalization _ _ i a hp]
  have hforced :
      (fun z : Assignment N => pairedTable N i (Function.update z i a)) =
        (fun z => bit a - bit (z (pairMate hE i))) := by
    funext z
    rw [pairedTable_even hE, Function.update_self,
      Function.update_of_ne (pairMate_ne hE i)]
  rw [hforced, expect_sub, expect_const, pair_expect_bit]

theorem pair_average_const (N : ℕ) (hN : 0 < N) (c : ℝ) :
    (∑ _i : Fin N, c) / (N : ℝ) = c := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hNr] <;> ring

theorem pair_information (N : ℕ) (hN : 0 < N) :
    information (fun _ => 1 / 2) (pairO N) =
      (fun _ _ : Fin 1 => (1 / 4 : ℝ)) := by
  ext a b
  change (∑ _i : Fin N, (1 / 2 : ℝ) * (1 - 1 / 2) * 1 * 1) / (N : ℝ) = 1 / 4
  convert pair_average_const N hN (1 / 4 : ℝ) using 1 <;> norm_num

theorem pair_information_inv (N : ℕ) (hN : 0 < N) :
    (information (fun _ => 1 / 2) (pairO N))⁻¹ =
      (fun _ _ : Fin 1 => (4 : ℝ)) := by
  rw [pair_information N hN]
  apply Matrix.inv_eq_left_inv
  show (Matrix.of fun _ _ => (4 : ℝ)) * Matrix.of (fun _ _ => (1 / 4 : ℝ)) = 1
  ext a b
  fin_cases a
  fin_cases b
  norm_num [Matrix.mul_apply]

theorem pair_beta {N : ℕ} (hE : Even N) (hN : 0 < N) (a : Bool) :
    beta (fun _ => 1 / 2) (pairedTable N) (pairO N) a =
      (fun _ => bit a - 1 / 2) := by
  have hrhs :
      (fun j : Fin 1 =>
        (∑ i : Fin N, marginal (fun _ => 1 / 2) (pairedTable N) i a *
          (1 / 2) * (1 - 1 / 2) * pairO N i j) / (N : ℝ)) =
        (fun _ => (bit a - 1 / 2) / 4) := by
    funext j
    simp only [pair_marginal hE, pairO]
    rw [pair_average_const N hN]
    ring
  unfold beta
  rw [pair_information_inv N hN, hrhs]
  funext j
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  ring

theorem pw7_proof : PW7 := by
  intro N hE hN
  funext i a
  unfold printedFits
  rw [pair_beta hE hN]
  cases a <;> norm_num [dot, pairO, pairFit, bit, Fin.sum_univ_one]

end
end AronowAudit.P004.Wave1.PairedWitness
