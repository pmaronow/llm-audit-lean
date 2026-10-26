import AronowAudit.P046.Wave1.PropositionThreeBlueprint

set_option autoImplicit false

namespace AronowAudit.P046.Wave1.PropositionThree

open AronowAudit.P046 AronowAudit.P046.IntervalExample MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

noncomputable section

theorem n5_proof : N5 := by
  classical
  intro a ha hc
  have hk : countK a ≤ 100 := by
    simpa only [countK, card_univ, Fintype.card_fin] using
      (card_filter_le (s := (univ : Finset (Fin 100))) (p := fun i => cat (a i) ≠ 2))
  have hs : countS a ≤ countK a := by
    apply card_le_card
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    rw [hi]
    decide
  have hlow (i : Fin 100) : (cat (a i) ≠ 2) ↔ (a i).1 ≤ (3 / 5 : ℝ) := by
    by_cases h : (a i).1 ≤ (3 / 5 : ℝ)
    · cases hx : (a i).2.1 <;> simp [cat, h, hx]
    · simp [cat, h]
  have hsum (c d : ℝ) :
      (∑ i : Fin 100, if (a i).1 ≤ (3 / 5 : ℝ) then c else d) =
        (countK a : ℝ) * c + (100 - (countK a : ℝ)) * d := by
    have hcard : (univ.filter (fun i : Fin 100 => (a i).1 ≤ (3 / 5 : ℝ))).card =
        countK a := by
      congr 1
      ext i
      simp only [mem_filter, mem_univ, true_and, hlow]
    have hcompl := card_filter_add_card_filter_not
      (s := (univ : Finset (Fin 100))) (p := fun i => (a i).1 ≤ (3 / 5 : ℝ))
    have hcard' : (univ.filter (fun i : Fin 100 => ¬ (a i).1 ≤ (3 / 5 : ℝ))).card =
        100 - countK a := by
      rw [hcard, card_univ, Fintype.card_fin] at hcompl
      omega
    simp only [sum_ite, sum_const, nsmul_eq_mul, hcard, hcard', Nat.cast_sub hk,
      Nat.cast_ofNat]
  have hterm (i : Fin 100) :
      htTerm (IntervalExample.study.pi (W (a i))) (X (a i)) (Y (a i)) =
        if cat (a i) = 0 then (20 / 13 : ℝ) else 0 := by
    have hy1 : (a i).2.2.2 = decide ((a i).1 ≤ (3 / 5 : ℝ)) :=
      congrArg Prod.snd (ha i)
    simp only [htTerm, consistency_treated]
    by_cases h : (a i).1 ≤ (3 / 5 : ℝ) <;>
      cases hx : (a i).2.1 <;>
        norm_num [IntervalExample.study, score, W, X, Y1, bit, cat, h, hx, hy1]
  have hht : ht IntervalExample.study a = (countS a : ℝ) / 65 := by
    simp only [ht, hterm]
    simp only [sum_ite, sum_const, nsmul_eq_mul, sum_const_zero, mul_zero, add_zero]
    change ((countS a : ℝ) * (20 / 13)) / 100 = _
    ring
  have hxiterm (i : Fin 100) : (IntervalExample.study.pi (W (a i)))⁻¹ ^ 2 =
      if (a i).1 ≤ (3 / 5 : ℝ) then (400 / 169 : ℝ) else 10000 / 9801 := by
    by_cases h : (a i).1 ≤ (3 / 5 : ℝ) <;>
      norm_num [IntervalExample.study, score, W, h]
  have hxi : xi IntervalExample.study a = xiK (countK a) := by
    simp only [xi, hxiterm, hsum, xiK]
    ring
  have hrad : printedRadius IntervalExample.study (1 / 10000000) a =
      Real.sqrt (xiK (countK a) * Real.log 20000000 / 200) := by
    simp only [printedRadius, hxi]
    norm_num
  have hsq := cutoff_implies_squared_exclusion (countK a) (countS a) hk hs hc
  have hnonneg : 0 ≤ xiK (countK a) * Real.log 20000000 / 200 := by
    have hkR : (countK a : ℝ) ≤ 100 := by exact_mod_cast hk
    have hkR' : 0 ≤ 100 - (countK a : ℝ) := sub_nonneg.mpr hkR
    have hx : 0 ≤ xiK (countK a) := by
      unfold xiK
      positivity
    exact div_nonneg (mul_nonneg hx (Real.log_nonneg (by norm_num))) (by norm_num)
  rw [hrad, hht, IntervalExample.probability_continuity_mean.2.2]
  have heq : ((countS a : ℝ) - 39) ^ 2 / 65 ^ 2 =
      ((countS a : ℝ) / 65 - 3 / 5) ^ 2 := by ring
  rw [heq] at hsq
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_lt_sqrt hnonneg hsq

end

end AronowAudit.P046.Wave1.PropositionThree
