import AronowAudit.P004.Wave1.ObservationalCoverageBlueprint
import AronowAudit.P004.Wave1.ObservationalCoverage.O4

/-! Second moments for the actual active-population design.  The elementary helpers in
this file are also used by O10--O12. -/

namespace AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical

theorem oc_admissible : AdmissibleSeq (fun N => propensities (activeO N) activeTheta) := by
  intro N i
  simp only [o4_proof N]
  split_ifs <;> norm_num

theorem oc_nH_sum (N : ℕ) :
    nH N = ∑ i : Fin N, if activeGroup N i then (1 : ℝ) else 0 := by
  unfold nH
  rw [Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Nat.cast_one, Finset.sum_filter, Nat.cast_ite, Nat.cast_zero]

theorem oc_nL_sum (N : ℕ) :
    nL N = ∑ i : Fin N, if activeGroup N i then (0 : ℝ) else 1 := by
  unfold nL
  rw [Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Nat.cast_one, Finset.sum_filter, ite_not, Nat.cast_ite,
    Nat.cast_zero]

theorem oc_nH_nonneg (N : ℕ) : 0 ≤ nH N := by unfold nH; positivity

theorem oc_nL_nonneg (N : ℕ) : 0 ≤ nL N := by unfold nL; positivity

theorem oc_nH_pos (N : ℕ) (hN : 0 < N) : 0 < nH N := by
  have hmem : (⟨0, hN⟩ : Fin N) ∈ Finset.univ.filter (fun i => activeGroup N i) := by
    simp [activeGroup]
  have hcard := Finset.card_pos.mpr ⟨(⟨0, hN⟩ : Fin N), hmem⟩
  unfold nH
  exact_mod_cast hcard

theorem oc_nH_le (N : ℕ) : nH N ≤ N := by
  have hcard := Finset.card_le_card
    (Finset.filter_subset (fun i : Fin N => activeGroup N i) Finset.univ)
  have hcard' : (Finset.univ.filter (fun i : Fin N => activeGroup N i)).card ≤ N := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hcard
  unfold nH
  exact_mod_cast hcard'

theorem oc_group_partition (N : ℕ) : nH N + nL N = N := by
  rw [oc_nH_sum, oc_nL_sum, ← Finset.sum_add_distrib]
  have hterm : ∀ i : Fin N,
      (if activeGroup N i then (1 : ℝ) else 0) +
        (if activeGroup N i then (0 : ℝ) else 1) = 1 := by
    intro i
    split_ifs <;> norm_num
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]

theorem oc_nH_succ (N : ℕ) :
    nH (N + 1) = nH N + if N % 8 < 2 then (1 : ℝ) else 0 := by
  simp only [oc_nH_sum, Fin.sum_univ_castSucc, activeGroup, Fin.val_castSucc, Fin.val_last]
  congr 1
  all_goals congr

/-- This formula includes the incomplete last block. -/
theorem oc_nH_count (N : ℕ) :
    nH N = ((2 * (N / 8) + min (N % 8) 2 : ℕ) : ℝ) := by
  induction N with
  | zero => simp [nH]
  | succ N ih =>
      have hstep : 2 * ((N + 1) / 8) + min ((N + 1) % 8) 2 =
          2 * (N / 8) + min (N % 8) 2 + if N % 8 < 2 then 1 else 0 := by
        have hmod := Nat.mod_lt N (by norm_num : 0 < 8)
        have hmod' := Nat.mod_lt (N + 1) (by norm_num : 0 < 8)
        have hdiv := Nat.mod_add_div N 8
        have hdiv' := Nat.mod_add_div (N + 1) 8
        split_ifs <;> omega
      rw [oc_nH_succ, ih]
      by_cases h : N % 8 < 2
      · rw [if_pos h] at hstep ⊢
        exact_mod_cast hstep.symm
      · rw [if_neg h] at hstep ⊢
        exact_mod_cast hstep.symm

theorem oc_nH_count_error (N : ℕ) : |nH N - (N : ℝ) / 4| ≤ 2 := by
  have hdiv : (N : ℝ) = 8 * ((N / 8 : ℕ) : ℝ) + ((N % 8 : ℕ) : ℝ) := by
    have hdivNat : N = 8 * (N / 8) + N % 8 := by omega
    exact_mod_cast hdivNat
  have hr0 : (0 : ℝ) ≤ ((N % 8 : ℕ) : ℝ) := by positivity
  have hr8 : ((N % 8 : ℕ) : ℝ) < 8 := by
    exact_mod_cast Nat.mod_lt N (by norm_num : 0 < 8)
  have hm0 : (0 : ℝ) ≤ ((min (N % 8) 2 : ℕ) : ℝ) := by positivity
  have hm2 : ((min (N % 8) 2 : ℕ) : ℝ) ≤ 2 := by
    exact_mod_cast min_le_right (N % 8) 2
  rw [oc_nH_count]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem oc_sAct_succ (N : ℕ) :
    sAct (N + 1) = sAct N +
      (if N % 8 = 0 then (1 : ℝ) else if N % 8 = 1 then -1 else 0) := by
  simp only [sAct, Fin.sum_univ_castSucc, activeSign, Fin.val_castSucc, Fin.val_last]

theorem oc_sAct_exact (N : ℕ) : sAct N = if N % 8 = 1 then (1 : ℝ) else 0 := by
  induction N with
  | zero => simp [sAct]
  | succ N ih =>
      have hr := Nat.mod_lt N (by norm_num : 0 < 8)
      have hnext : (N + 1) % 8 = (N % 8 + 1) % 8 := by omega
      rw [oc_sAct_succ, ih, hnext]
      interval_cases h : N % 8 <;> norm_num [h]

theorem oc_sAct_sq_le (N : ℕ) : (sAct N)^2 ≤ 1 := by
  rw [oc_sAct_exact]
  split_ifs <;> norm_num

theorem oc_sign_sq (N : ℕ) (i : Fin N) :
    (activeSign N i)^2 = if activeGroup N i then (1 : ℝ) else 0 := by
  by_cases h0 : i.val % 8 = 0
  · simp [activeSign, activeGroup, h0]
  by_cases h1 : i.val % 8 = 1
  · simp [activeSign, activeGroup, h0, h1]
  have hg : ¬ activeGroup N i := by unfold activeGroup; omega
  simp [activeSign, h0, h1, hg]

theorem oc_sign_eq_zero (N : ℕ) (i : Fin N) (hi : ¬ activeGroup N i) :
    activeSign N i = 0 := by
  have hs := oc_sign_sq N i
  rw [if_neg hi] at hs
  exact sq_eq_zero_iff.mp hs

theorem oc_clip_bounds (q : ℝ) : (1 : ℝ) / 20 ≤ clip q ∧ clip q ≤ 19 / 20 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem oc_clip_contract (q : ℝ) : |1 - 2 * clip q| ≤ |1 - 2 * q| := by
  unfold clip
  by_cases hl : q ≤ 1 / 20
  · rw [min_eq_right (by linarith : q ≤ 19 / 20), max_eq_left hl]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 - 2 * (1 / 20)),
      abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * q)]
    linarith
  by_cases hu : 19 / 20 ≤ q
  · rw [min_eq_left hu, max_eq_right (by norm_num : (1 : ℝ) / 20 ≤ 19 / 20)]
    rw [abs_of_nonpos (by norm_num : (1 : ℝ) - 2 * (19 / 20) ≤ 0),
      abs_of_nonpos (by linarith : 1 - 2 * q ≤ 0)]
    linarith
  · rw [min_eq_right (by linarith : q ≤ 19 / 20),
      max_eq_right (by linarith : (1 : ℝ) / 20 ≤ q)]

theorem oc_bit_mean {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (i : Fin N) : expect p (fun z => bit (z i)) = p i := by
  simpa only [pow_one, mul_one, expect_const] using
    bernoulli_positive_power p (fun _ => 1) i 1 (by norm_num) hp

theorem oc_bit_second {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (i : Fin N) : expect p (fun z => (bit (z i))^2) = p i := by
  simpa only [mul_one, expect_const] using
    bernoulli_positive_power p (fun _ => 1) i 2 (by norm_num) hp

theorem oc_bit_pair {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (i j : Fin N) (hij : i ≠ j) :
    expect p (fun z => bit (z i) * bit (z j)) = p i * p j := by
  simpa only [pow_one, mul_one, expect_const] using
    bernoulli_pair_positive_powers p (fun _ => 1) i j hij 1 1
      (by norm_num) (by norm_num) hp

theorem oc_centered_coin_product {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (i j : Fin N) :
    expect p (fun z => (bit (z i) - p i) * (bit (z j) - p j)) =
      if i = j then p i * (1 - p i) else 0 := by
  by_cases hij : i = j
  · subst j
    have he : (fun z : Assignment N => (bit (z i) - p i) * (bit (z i) - p i)) =
        fun z => (bit (z i))^2 - (2 * p i) * bit (z i) + (p i)^2 := by
      funext z; ring
    rw [he, expect_add, expect_sub, expect_mul, oc_bit_second p hp,
      oc_bit_mean p hp, expect_const]
    rw [if_pos rfl]
    ring
  · have he : (fun z : Assignment N => (bit (z i) - p i) * (bit (z j) - p j)) =
        fun z => bit (z i) * bit (z j) - p j * bit (z i) -
          p i * bit (z j) + p i * p j := by
      funext z; ring
    rw [he, expect_add, expect_sub, expect_sub, expect_mul, expect_mul,
      oc_bit_pair p hp i j hij, oc_bit_mean p hp, oc_bit_mean p hp, expect_const,
      if_neg hij]
    ring

theorem oc_weighted_mean {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (a : Fin N → ℝ) :
    expect p (fun z => ∑ i, a i * bit (z i)) = ∑ i, a i * p i := by
  rw [expect_sum]
  simp_rw [expect_mul, oc_bit_mean p hp]

theorem oc_weighted_centered_second {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (a : Fin N → ℝ) :
    expect p (fun z => ((∑ i, a i * bit (z i)) - ∑ i, a i * p i)^2) =
      ∑ i, (a i)^2 * p i * (1 - p i) := by
  have he : (fun z : Assignment N => ((∑ i, a i * bit (z i)) - ∑ i, a i * p i)^2) =
      fun z => ∑ i, ∑ j, (a i * a j) * ((bit (z i) - p i) * (bit (z j) - p j)) := by
    funext z
    rw [← Finset.sum_sub_distrib]
    simp only [← mul_sub, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, expect_sum]
  simp_rw [expect_sum, expect_mul, oc_centered_coin_product p hp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
    ring
  · intro j _ hji
    simp only [if_neg (Ne.symm hji), mul_zero]
  · simp

theorem oc_weighted_second {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (a : Fin N → ℝ) :
    expect p (fun z => (∑ i, a i * bit (z i))^2) =
      (∑ i, (a i)^2 * p i * (1 - p i)) + (∑ i, a i * p i)^2 := by
  have hc := oc_weighted_centered_second p hp a
  have he : (fun z : Assignment N => ((∑ i, a i * bit (z i)) - ∑ i, a i * p i)^2) =
      fun z => (∑ i, a i * bit (z i))^2 -
        (2 * ∑ i, a i * p i) * (∑ i, a i * bit (z i)) + (∑ i, a i * p i)^2 := by
    funext z; ring
  rw [he, expect_add, expect_sub, expect_mul, oc_weighted_mean p hp, expect_const] at hc
  nlinarith only [hc]

theorem oc_S_weighted_mean (N : ℕ) :
    (∑ i, activeSign N i * propensities (activeO N) activeTheta i) = sAct N / 2 := by
  rw [sAct, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [o4_proof N]
  dsimp only
  by_cases hi : activeGroup N i
  · rw [if_pos hi]; ring
  · rw [if_neg hi, oc_sign_eq_zero N i hi]
    ring

theorem oc_S_variance_sum (N : ℕ) :
    (∑ i, (activeSign N i)^2 * propensities (activeO N) activeTheta i *
      (1 - propensities (activeO N) activeTheta i)) = nH N / 4 := by
  rw [oc_nH_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [oc_sign_sq, o4_proof N]
  dsimp only
  split_ifs <;> norm_num

theorem oc_S_mean (N : ℕ) :
    expect (propensities (activeO N) activeTheta) (SAct N) = sAct N / 2 := by
  unfold SAct
  rw [oc_weighted_mean _ (oc_admissible N), oc_S_weighted_mean]

theorem oc_S_second (N : ℕ) :
    expect (propensities (activeO N) activeTheta) (fun z => (SAct N z)^2) =
      nH N / 4 + (sAct N / 2)^2 := by
  unfold SAct
  rw [oc_weighted_second _ (oc_admissible N), oc_S_weighted_mean, oc_S_variance_sum]

theorem oc_K_centered_second (N : ℕ) :
    expect (propensities (activeO N) activeTheta)
      (fun z => (KAct N z - nH N / 2)^2) = nH N / 4 := by
  let a : Fin N → ℝ := fun i => if activeGroup N i then 1 else 0
  have hK : ∀ z : Assignment N, (∑ i, a i * bit (z i)) = KAct N z := by
    intro z
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [a]
    split_ifs <;> simp
  have hm : (∑ i, a i * propensities (activeO N) activeTheta i) = nH N / 2 := by
    rw [oc_nH_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [o4_proof N]
    dsimp only [a]
    split_ifs <;> norm_num
  have hv : (∑ i, (a i)^2 * propensities (activeO N) activeTheta i *
      (1 - propensities (activeO N) activeTheta i)) = nH N / 4 := by
    rw [oc_nH_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [o4_proof N]
    dsimp only [a]
    split_ifs <;> norm_num
  simpa only [hK, hm, hv] using
    oc_weighted_centered_second _ (oc_admissible N) a

theorem oc_J_centered_second (N : ℕ) :
    expect (propensities (activeO N) activeTheta)
      (fun z => (JAct N z - nL N / 10)^2) = (9 / 100 : ℝ) * nL N := by
  let a : Fin N → ℝ := fun i => if activeGroup N i then 0 else 1
  have hJ : ∀ z : Assignment N, (∑ i, a i * bit (z i)) = JAct N z := by
    intro z
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [a]
    split_ifs <;> simp
  have hm : (∑ i, a i * propensities (activeO N) activeTheta i) = nL N / 10 := by
    rw [oc_nL_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [o4_proof N]
    dsimp only [a]
    split_ifs <;> norm_num
  have hv : (∑ i, (a i)^2 * propensities (activeO N) activeTheta i *
      (1 - propensities (activeO N) activeTheta i)) = (9 / 100 : ℝ) * nL N := by
    rw [oc_nL_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [o4_proof N]
    dsimp only [a]
    split_ifs <;> norm_num
  simpa only [hJ, hm, hv] using
    oc_weighted_centered_second _ (oc_admissible N) a

theorem oc_phat_second_bound (N : ℕ) (hN : 0 < N) :
    expect (propensities (activeO N) activeTheta)
      (fun z => (1 - 2 * pHatH N z)^2) ≤ 1 / nH N := by
  have hn : nH N ≠ 0 := ne_of_gt (oc_nH_pos N hN)
  have hmono := expect_mono _ (oc_admissible N)
    (fun z => (1 - 2 * pHatH N z)^2)
    (fun z => (1 - 2 * (KAct N z / nH N))^2)
    (fun z => sq_le_sq.mpr (oc_clip_contract (KAct N z / nH N)))
  have he : (fun z : Assignment N => (1 - 2 * (KAct N z / nH N))^2) =
      fun z => (4 / (nH N)^2) * (KAct N z - nH N / 2)^2 := by
    funext z
    field_simp [hn] <;> ring
  rw [he, expect_mul, oc_K_centered_second] at hmono
  calc
    expect (propensities (activeO N) activeTheta) (fun z => (1 - 2 * pHatH N z)^2) ≤
        (4 / (nH N)^2) * (nH N / 4) := hmono
    _ = 1 / nH N := by field_simp [hn] <;> ring

theorem o9_proof : O9 := by
  intro N hN
  constructor
  · rw [oc_S_second]
    have hn := oc_nH_le N
    have hs := oc_sAct_sq_le N
    have hN1 : (1 : ℝ) ≤ N := by
      exact_mod_cast (show 1 ≤ N by omega)
    nlinarith
  · exact oc_phat_second_bound N hN

end
end AronowAudit.P004.Wave1.ObservationalCoverage
