import AronowAudit.P004.Wave1.PairedWitnessBlueprint
import AronowAudit.P004.P004_FiniteGraphCompletion

/-! Exact finite moments of the paired witness.  The elementary matching and sign
calculations in `MomentCalculations` are also used by PW10 and PW11. -/

namespace AronowAudit.P004.Wave1.PairedWitness

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators Classical

namespace MomentCalculations

/-- Exchange the two indices in each consecutive block of size two. -/
def mate {N : ℕ} (hE : Even N) (i : Fin N) : Fin N :=
  ⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1, by
    have hi := i.isLt
    obtain ⟨k, hk⟩ := hE
    split_ifs <;> omega⟩

theorem mate_ne {N : ℕ} (hE : Even N) (i : Fin N) : mate hE i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  change (if i.val % 2 = 0 then i.val + 1 else i.val - 1) = i.val at hv
  split_ifs at hv <;> omega

theorem mate_block {N : ℕ} (hE : Even N) (i : Fin N) :
    (mate hE i).val / 2 = i.val / 2 := by
  change (if i.val % 2 = 0 then i.val + 1 else i.val - 1) / 2 = i.val / 2
  split_ifs <;> omega

theorem mate_unique {N : ℕ} (hE : Even N) (i j : Fin N)
    (hji : j ≠ i) (hblock : j.val / 2 = i.val / 2) : j = mate hE i := by
  have hv : j.val ≠ i.val := by
    intro h
    exact hji (Fin.ext h)
  apply Fin.ext
  change j.val = (if i.val % 2 = 0 then i.val + 1 else i.val - 1)
  split_ifs <;> omega

theorem mate_invol {N : ℕ} (hE : Even N) (i : Fin N) :
    mate hE (mate hE i) = i := by
  symm
  exact mate_unique hE (mate hE i) i (mate_ne hE i).symm (mate_block hE i).symm

theorem mate_injective {N : ℕ} (hE : Even N) : Function.Injective (mate hE) := by
  intro i j hij
  have h := congrArg (mate hE) hij
  simpa only [mate_invol] using h

/-- The sum in the paired table contains precisely its one mate term. -/
theorem table_eq {N : ℕ} (hE : Even N) (i : Fin N) (z : Assignment N) :
    pairedTable N i z = bit (z i) - bit (z (mate hE i)) := by
  unfold pairedTable
  rw [if_pos hE]
  congr 1
  rw [Finset.sum_eq_single (mate hE i)]
  · simp [mate_ne hE i, mate_block hE i]
  · intro j _ hj
    have hn : ¬ (j ≠ i ∧ j.val / 2 = i.val / 2) := by
      intro h
      exact hj (mate_unique hE i j h.1 h.2)
    exact if_neg hn
  · intro hm
    exact False.elim (hm (Finset.mem_univ _))

def sign {N : ℕ} (i : Fin N) (z : Assignment N) : ℝ := 2 * bit (z i) - 1

theorem sign_sq {N : ℕ} (i : Fin N) (z : Assignment N) : (sign i z)^2 = 1 := by
  cases hz : z i <;> norm_num [sign, bit, hz]

theorem bit_mean {N : ℕ} (i : Fin N) :
    expect (fun _ : Fin N => 1/2) (fun z => bit (z i)) = 1/2 := by
  have hp : ∀ j : Fin N, 0 < (1/2 : ℝ) ∧ (1/2 : ℝ) < 1 := fun _ => by norm_num
  simpa only [pow_one, mul_one, expect_const] using
    (bernoulli_positive_power (fun _ : Fin N => 1/2) (fun _ => 1) i 1
      (by norm_num) hp)

theorem sign_mean {N : ℕ} (i : Fin N) :
    expect (fun _ : Fin N => 1/2) (sign i) = 0 := by
  unfold sign
  rw [expect_sub, expect_mul, bit_mean, expect_const]
  norm_num

theorem sign_pair_mean {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    expect (fun _ : Fin N => 1/2) (fun z => sign i z * sign j z) = 0 := by
  have hi : DependsOn (sign i) ({i} : Set (Fin N)) := by
    intro x y hxy
    unfold sign
    rw [hxy i (by simp)]
  have hj : DependsOn (sign j) (({i} : Set (Fin N))ᶜ) := by
    intro x y hxy
    unfold sign
    rw [hxy j (by simp [hij.symm])]
  rw [GraphCompletion.expect_mul_of_disjoint_depends
    (fun _ : Fin N => 1/2) ({i} : Set (Fin N)) (sign i) (sign j) hi hj,
    sign_mean, sign_mean, zero_mul]

def pairSign {N : ℕ} (hE : Even N) (i : Fin N) (z : Assignment N) : ℝ :=
  sign i z * sign (mate hE i) z

theorem pairSign_mean {N : ℕ} (hE : Even N) (i : Fin N) :
    expect (fun _ : Fin N => 1/2) (pairSign hE i) = 0 := by
  exact sign_pair_mean i (mate hE i) (mate_ne hE i).symm

theorem pairSign_sq {N : ℕ} (hE : Even N) (i : Fin N) (z : Assignment N) :
    (pairSign hE i z)^2 = 1 := by
  unfold pairSign
  rw [mul_pow, sign_sq, sign_sq, one_mul]

theorem pairSign_mate {N : ℕ} (hE : Even N) (i : Fin N) (z : Assignment N) :
    pairSign hE (mate hE i) z = pairSign hE i z := by
  unfold pairSign
  rw [mate_invol]
  exact mul_comm _ _

/-- Equal blocks contribute one; disjoint blocks have independent centered products. -/
theorem pairSign_product_mean {N : ℕ} (hE : Even N) (i j : Fin N) :
    expect (fun _ : Fin N => 1/2) (fun z => pairSign hE i z * pairSign hE j z) =
      if j = i ∨ j = mate hE i then 1 else 0 := by
  by_cases hji : j = i
  · subst j
    rw [if_pos (Or.inl rfl)]
    have he : (fun z => pairSign hE i z * pairSign hE i z) = fun _ => (1 : ℝ) := by
      funext z
      simpa only [pow_two] using pairSign_sq hE i z
    rw [he, expect_const]
  by_cases hjm : j = mate hE i
  · subst j
    rw [if_pos (Or.inr rfl)]
    have he : (fun z => pairSign hE i z * pairSign hE (mate hE i) z) =
        fun _ => (1 : ℝ) := by
      funext z
      rw [pairSign_mate]
      simpa only [pow_two] using pairSign_sq hE i z
    rw [he, expect_const]
  rw [if_neg (not_or.mpr ⟨hji, hjm⟩)]
  have hmji : mate hE j ≠ i := by
    intro h
    apply hjm
    have hh := congrArg (mate hE) h
    simpa only [mate_invol] using hh
  have hmjm : mate hE j ≠ mate hE i := by
    intro h
    exact hji (mate_injective hE h)
  have hi : DependsOn (pairSign hE i) ({i, mate hE i} : Set (Fin N)) := by
    intro x y hxy
    unfold pairSign sign
    rw [hxy i (by simp), hxy (mate hE i) (by simp)]
  have hj : DependsOn (pairSign hE j) (({i, mate hE i} : Set (Fin N))ᶜ) := by
    intro x y hxy
    unfold pairSign sign
    rw [hxy j (by simp [hji, hjm]), hxy (mate hE j) (by simp [hmji, hmjm])]
  rw [GraphCompletion.expect_mul_of_disjoint_depends
    (fun _ : Fin N => 1/2) ({i, mate hE i} : Set (Fin N))
    (pairSign hE i) (pairSign hE j) hi hj, pairSign_mean, pairSign_mean, zero_mul]

theorem augmented_eq {N : ℕ} (hE : Even N) :
    augmented (fun _ : Fin N => 1/2) (pairedTable N) (pairFit N) =
      fun z => (∑ i, (1 - pairSign hE i z)) / N := by
  funext z
  unfold augmented
  apply congrArg (fun t : ℝ => t / (N : ℝ))
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [table_eq hE]
  cases hi : z i <;> cases hm : z (mate hE i) <;>
    norm_num [pairFit, pairSign, sign, bit, hi, hm]

end MomentCalculations

open MomentCalculations

theorem pw9_proof : PW9 := by
  intro N hE hN
  have hmean (i : Fin N) :
      expect (fun _ : Fin N => 1/2) (fun z => 1 - pairSign hE i z) = 1 := by
    rw [expect_sub, expect_const, pairSign_mean]
    ring
  have hcov (i j : Fin N) :
      cov (fun _ : Fin N => 1/2) (fun z => 1 - pairSign hE i z)
        (fun z => 1 - pairSign hE j z) =
          if j = i ∨ j = mate hE i then 1 else 0 := by
    calc
      _ = expect (fun _ : Fin N => 1/2)
          (fun z => pairSign hE i z * pairSign hE j z) := by
        rw [cov_centered, hmean i, hmean j]
        congr 1
        funext z
        ring
      _ = _ := pairSign_product_mean hE i j
  have hrow (i : Fin N) :
      (∑ j, cov (fun _ : Fin N => 1/2) (fun z => 1 - pairSign hE i z)
        (fun z => 1 - pairSign hE j z)) = 2 := by
    calc
      _ = ∑ j : Fin N,
          ((if j = i then (1 : ℝ) else 0) + (if j = mate hE i then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hcov]
        by_cases hji : j = i
        · subst j
          simp [(mate_ne hE i).symm]
        · simp [hji]
      _ = 2 := by
        rw [Finset.sum_add_distrib]
        simp
        norm_num
  rw [augmented_eq hE, variance_div, variance_sum]
  simp_rw [hrow]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hNr]
  <;> ring

end
end AronowAudit.P004.Wave1.PairedWitness
