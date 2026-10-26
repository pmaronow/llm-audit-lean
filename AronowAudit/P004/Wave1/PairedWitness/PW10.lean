import AronowAudit.P004.Wave1.PairedWitness.PW9
import AronowAudit.P004.P004_VarianceComponentsCompletion

/-! Conditional residual moments for the literal unsigned printed formula.  In
particular, the second factor below retains `pairFit N i b`, as in the printed formula. -/

namespace AronowAudit.P004.Wave1.PairedWitness

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators Classical

namespace MomentCalculations

theorem centered_bit_mean {N : ℕ} (i : Fin N) :
    expect (fun _ : Fin N => 1/2) (fun z => 1/2 - bit (z i)) = 0 := by
  rw [expect_sub, expect_const, bit_mean]
  norm_num

theorem centered_bit_pair_mean {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    expect (fun _ : Fin N => 1/2)
      (fun z => (1/2 - bit (z i)) * (1/2 - bit (z j))) = 0 := by
  have he : (fun z : Assignment N => (1/2 - bit (z i)) * (1/2 - bit (z j))) =
      fun z => (sign i z * sign j z) / 4 := by
    funext z
    unfold sign
    ring
  rw [he, expect_div, sign_pair_mean i j hij, zero_div]

/-- The observed-arm residual is a centered mate coin. -/
theorem residual_eq {N : ℕ} (hE : Even N) (i : Fin N) (z : Assignment N) :
    pairedTable N i z - pairFit N i (z i) = 1/2 - bit (z (mate hE i)) := by
  rw [table_eq hE]
  cases hi : z i <;> norm_num [pairFit, bit, hi] <;> ring

theorem forced_residual {N : ℕ} (hE : Even N) (i : Fin N) (a : Bool)
    (z : Assignment N) :
    pairedTable N i (Function.update z i a) - pairFit N i a =
      1/2 - bit (z (mate hE i)) := by
  have hr := residual_eq hE i (Function.update z i a)
  simpa only [Function.update_self, Function.update_of_ne (mate_ne hE i)] using hr

/-- This also supplies the zero marginal residual means used by PW11. -/
theorem marginal_eq_fit {N : ℕ} (hE : Even N) (i : Fin N) (a : Bool) :
    marginal (fun _ : Fin N => 1/2) (pairedTable N) i a = pairFit N i a := by
  have hp : ∀ j : Fin N, 0 < (1/2 : ℝ) ∧ (1/2 : ℝ) < 1 := fun _ => by norm_num
  apply sub_eq_zero.mp
  calc
    marginal (fun _ : Fin N => 1/2) (pairedTable N) i a - pairFit N i a =
        expect (fun _ : Fin N => 1/2)
          (fun z => pairedTable N i (Function.update z i a) - pairFit N i a) := by
      rw [expect_sub, expect_const,
        marginal_is_marginalization (fun _ : Fin N => 1/2) (pairedTable N) i a hp]
    _ = expect (fun _ : Fin N => 1/2) (fun z => 1/2 - bit (z (mate hE i))) := by
      congr 1
      funext z
      exact forced_residual hE i a z
    _ = 0 := centered_bit_mean (mate hE i)

theorem marginal_residual_square {N : ℕ} (hE : Even N) (i : Fin N) (a : Bool) :
    marginal (fun _ : Fin N => 1/2)
      (fun j z => (pairedTable N j z - pairFit N j a)^2) i a = 1/4 := by
  have hp : ∀ j : Fin N, 0 < (1/2 : ℝ) ∧ (1/2 : ℝ) < 1 := fun _ => by norm_num
  rw [marginal_is_marginalization (fun _ : Fin N => 1/2) _ i a hp]
  have he : (fun z : Assignment N =>
      (pairedTable N i (Function.update z i a) - pairFit N i a)^2) =
        fun _ => (1/4 : ℝ) := by
    funext z
    rw [forced_residual hE i a z]
    cases hz : z (mate hE i) <;> norm_num [bit, hz]
  rw [he, expect_const]

/-- Both own coordinates are forced, while the residuals still read their mate coins. -/
theorem forced_product_eq {N : ℕ} (hE : Even N) (i j : Fin N) (hij : i ≠ j)
    (a b : Bool) (z : Assignment N) :
    (pairedTable N i (Function.update (Function.update z j b) i a) - pairFit N i a) *
      (pairedTable N j (Function.update (Function.update z j b) i a) - pairFit N i b) =
    (1/2 - bit ((Function.update (Function.update z j b) i a) (mate hE i))) *
      (1/2 - bit ((Function.update (Function.update z j b) i a) (mate hE j))) := by
  have hri := residual_eq hE i (Function.update (Function.update z j b) i a)
  have hrj := residual_eq hE j (Function.update (Function.update z j b) i a)
  have hui : (Function.update (Function.update z j b) i a) i = a := by simp
  have huj : (Function.update (Function.update z j b) i a) j = b := by
    simp [hij.symm]
  rw [hui] at hri
  rw [huj] at hrj
  change pairedTable N j (Function.update (Function.update z j b) i a) - pairFit N i b =
    1/2 - bit ((Function.update (Function.update z j b) i a) (mate hE j)) at hrj
  rw [hri, hrj]

/-- A matched pair gives a deterministic product of forced arm residuals.  For
different blocks, two distinct unforced mate coins have centered product mean zero. -/
theorem pair_residual_marginal {N : ℕ} (hE : Even N) (i j : Fin N) (hij : i ≠ j)
    (a b : Bool) :
    pairMarginal (fun _ : Fin N => 1/2)
      (fun z => (pairedTable N i z - pairFit N i a) *
        (pairedTable N j z - pairFit N i b)) i j a b =
      if mate hE i = j then (1/2 - bit b) * (1/2 - bit a) else 0 := by
  have hp : ∀ k : Fin N, 0 < (1/2 : ℝ) ∧ (1/2 : ℝ) < 1 := fun _ => by norm_num
  rw [ComponentCompletion.pair_marginal_forced (fun _ : Fin N => 1/2) hp _ i j hij a b]
  have he : (fun z : Assignment N =>
      (pairedTable N i (Function.update (Function.update z j b) i a) - pairFit N i a) *
        (pairedTable N j (Function.update (Function.update z j b) i a) - pairFit N i b)) =
      fun z =>
        (1/2 - bit ((Function.update (Function.update z j b) i a) (mate hE i))) *
          (1/2 - bit ((Function.update (Function.update z j b) i a) (mate hE j))) := by
    funext z
    exact forced_product_eq hE i j hij a b z
  rw [he]
  by_cases hm : mate hE i = j
  · rw [if_pos hm]
    have hmj : mate hE j = i := by
      rw [← hm, mate_invol]
    have hc : (fun z : Assignment N =>
        (1/2 - bit ((Function.update (Function.update z j b) i a) (mate hE i))) *
          (1/2 - bit ((Function.update (Function.update z j b) i a) (mate hE j)))) =
        fun _ => (1/2 - bit b) * (1/2 - bit a) := by
      funext z
      simp only [hm, hmj, Function.update_of_ne hij.symm, Function.update_self]
    rw [hc, expect_const]
  · rw [if_neg hm]
    have hmji : mate hE j ≠ i := by
      intro h
      apply hm
      have hh := congrArg (mate hE) h
      have hh' : j = mate hE i := by simpa only [mate_invol] using hh
      exact hh'.symm
    have hmij : mate hE i ≠ mate hE j := by
      intro h
      exact hij (mate_injective hE h)
    have hc : (fun z : Assignment N =>
        (1/2 - bit ((Function.update (Function.update z j b) i a) (mate hE i))) *
          (1/2 - bit ((Function.update (Function.update z j b) i a) (mate hE j)))) =
        fun z => (1/2 - bit (z (mate hE i))) * (1/2 - bit (z (mate hE j))) := by
      funext z
      simp only [Function.update_of_ne (mate_ne hE i), Function.update_of_ne hm,
        Function.update_of_ne hmji, Function.update_of_ne (mate_ne hE j)]
    rw [hc]
    exact centered_bit_pair_mean (mate hE i) (mate hE j) hmij

theorem unsigned_pair_sum {N : ℕ} (hE : Even N) (i j : Fin N) (hij : i ≠ j) :
    (∑ a : Bool, ∑ b : Bool,
      pairMarginal (fun _ : Fin N => 1/2)
        (fun z => (pairedTable N i z - pairFit N i a) *
          (pairedTable N j z - pairFit N i b)) i j a b) = 0 := by
  simp_rw [pair_residual_marginal hE i j hij]
  by_cases hm : mate hE i = j <;> norm_num [hm, Fintype.sum_bool, bit]

theorem diagonal_sum {N : ℕ} (hE : Even N) :
    (∑ i : Fin N,
      (marginal (fun _ : Fin N => 1/2)
          (fun j z => (pairedTable N j z - pairFit N j true)^2) i true / (1/2) +
        marginal (fun _ : Fin N => 1/2)
          (fun j z => (pairedTable N j z - pairFit N j false)^2) i false / (1 - 1/2))) =
      (N : ℝ) := by
  calc
    _ = ∑ _i : Fin N, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [marginal_residual_square hE i true, marginal_residual_square hE i false]
      norm_num
    _ = (N : ℝ) := by simp

theorem unsigned_neighborhood_sum {N : ℕ} (hE : Even N)
    (B : Fin N → Finset (Fin N)) :
    (∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool,
      pairMarginal (fun _ : Fin N => 1/2)
        (fun z => (pairedTable N i z - pairFit N i a) *
          (pairedTable N j z - pairFit N i b)) i j a b) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  exact unsigned_pair_sum hE i j (Finset.ne_of_mem_erase hj).symm

end MomentCalculations

open MomentCalculations

theorem pw10_proof : PW10 := by
  intro N hE hN B
  unfold printedSecondMomentBound
  rw [diagonal_sum hE, unsigned_neighborhood_sum hE B, add_zero]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hNr]
  <;> ring

end
end AronowAudit.P004.Wave1.PairedWitness
