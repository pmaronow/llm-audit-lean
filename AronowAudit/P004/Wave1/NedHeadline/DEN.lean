import AronowAudit.P004.Wave1.NedHeadlineBlueprint

universe u

namespace AronowAudit.P004.Wave1.NedHeadline

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators

private theorem normalized_count_second {N : ℕ} (p : Fin N → ℝ)
    (X : Assignment N → ℝ) (c : ℝ) (hc : c ≠ 0) (hm : expect p X = c) :
    expect p (fun z => (X z / c - 1)^2) = variance p X / c^2 := by
  calc
    _ = variance p (fun z => X z / c) := by
      rw [variance, cov_centered, expect_div, hm, div_self hc]
      congr 1
      funext z
      ring
    _ = _ := variance_div p X c

theorem den_proof : DEN := by
  intro N p hN hp
  classical
  let π : Fin N → ℝ := fun _ => p
  let T : Assignment N → ℝ := fun z => ∑ i, bit (z i)
  have hπ : ∀ i, 0 < π i ∧ π i < 1 := fun _ => hp
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hq : 0 < 1 - p := sub_pos.mpr hp.2
  have hbit (i : Fin N) : expect π (fun z => bit (z i)) = p := by
    simpa only [pow_one, mul_one, expect_const, mul_one] using
      bernoulli_positive_power π (fun _ => 1) i 1 (by decide) hπ
  have hbit2 (i : Fin N) : expect π (fun z => (bit (z i))^2) = p := by
    simpa only [mul_one, expect_const, mul_one] using
      bernoulli_positive_power π (fun _ => 1) i 2 (by decide) hπ
  have hpair (i j : Fin N) (hij : i ≠ j) :
      expect π (fun z => bit (z i) * bit (z j)) = p * p := by
    simpa only [pow_one, mul_one, expect_const, mul_one] using
      bernoulli_pair_positive_powers π (fun _ => 1) i j hij 1 1
        (by decide) (by decide) hπ
  have hT : expect π T = N * p := by
    change expect π (fun z => ∑ i, bit (z i)) = _
    rw [expect_sum]
    simp only [hbit, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hvT : variance π T = N * p * (1 - p) := by
    change variance π (fun z => ∑ i, bit (z i)) = _
    rw [variance_sum]
    have hc (i j : Fin N) : cov π (fun z => bit (z i)) (fun z => bit (z j)) =
        if i = j then p * (1 - p) else 0 := by
      by_cases hij : i = j
      · subst j
        rw [if_pos rfl, cov, hbit]
        have hs : expect π (fun z => bit (z i) * bit (z i)) = p := by
          simpa only [pow_two] using hbit2 i
        rw [hs]
        ring
      · rw [if_neg hij, cov, hpair i j hij, hbit, hbit]
        ring
    simp_rw [hc]
    simp [mul_assoc]
  have htrue (z : Assignment N) : armCount z true = T z := by
    apply Finset.sum_congr rfl
    intro i _
    cases hz : z i <;> simp [bit, hz]
  have hfalse (z : Assignment N) : armCount z false = (N : ℝ) - T z := by
    have he (i : Fin N) : (if z i = false then (1 : ℝ) else 0) = 1 - bit (z i) := by
      cases hz : z i <;> simp [bit, hz]
    simp only [armCount, he, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, T]
  have hF : expect π (fun z => armCount z false) = N * (1 - p) := by
    simp_rw [hfalse]
    rw [expect_sub, expect_const, hT]
    ring
  have hvF : variance π (fun z => armCount z false) = N * p * (1 - p) := by
    calc
      _ = variance π T := by
        simp_rw [hfalse]
        simp only [variance, cov_centered, expect_sub, expect_const]
        congr 1
        funext z
        ring
      _ = _ := hvT
  constructor
  · have hm : expect π (fun z => armCount z true) = N * p := by
      simpa only [htrue] using hT
    rw [normalized_count_second π _ (N * p) (mul_ne_zero hn hp.1.ne') hm]
    have hv : variance π (fun z => armCount z true) = N * p * (1 - p) := by
      simpa only [htrue] using hvT
    rw [hv]
    field_simp [hn, hp.1.ne'] <;> ring
  · rw [normalized_count_second π _ (N * (1 - p)) (mul_ne_zero hn hq.ne') hF, hvF]
    field_simp [hn, hq.ne'] <;> ring

end
end AronowAudit.P004.Wave1.NedHeadline
