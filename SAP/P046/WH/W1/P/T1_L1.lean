import SAP.P046.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Finset
open AronowAudit.P046 AronowAudit.P046.IntervalExample
open scoped BigOperators ENNReal

noncomputable section

theorem SAP.P046.WH.W1.T1_L1_proof : SAP.P046.WH.W1.T1_L1 := by
  classical
  intro a ha
  have hk : wholeK a ≤ 100 := (counts_feasible a).2
  have hs : wholeS a ≤ wholeK a := (counts_feasible a).1
  have hlow (i : Fin 100) :
      wholeCat (a i) ≠ 2 ↔ (a i).1 ≤ (3 / 5 : ℝ) := by
    by_cases h : (a i).1 ≤ (3 / 5 : ℝ)
    · cases hx : (a i).2.1 <;> simp [wholeCat, h, hx]
    · simp [wholeCat, h]
  have hsum (c d : ℝ) :
      (∑ i : Fin 100, if (a i).1 ≤ (3 / 5 : ℝ) then c else d) =
        (wholeK a : ℝ) * c + (100 - (wholeK a : ℝ)) * d := by
    have hcard :
        (univ.filter (fun i : Fin 100 => (a i).1 ≤ (3 / 5 : ℝ))).card = wholeK a := by
      congr 1
      ext i
      simp only [mem_filter, mem_univ, true_and, hlow]
    have hcompl := card_filter_add_card_filter_not
      (s := (univ : Finset (Fin 100)))
      (p := fun i => (a i).1 ≤ (3 / 5 : ℝ))
    have hcard' :
        (univ.filter (fun i : Fin 100 => ¬ (a i).1 ≤ (3 / 5 : ℝ))).card =
          100 - wholeK a := by
      rw [hcard, card_univ, Fintype.card_fin] at hcompl
      omega
    simp only [sum_ite, sum_const, nsmul_eq_mul, hcard, hcard', Nat.cast_sub hk,
      Nat.cast_ofNat]
  have hterm (i : Fin 100) :
      htTerm (IntervalExample.study.pi (W (a i))) (X (a i)) (Y (a i)) =
        if wholeCat (a i) = 0 then (20 / 13 : ℝ) else 0 := by
    have hy1 : (a i).2.2.2 = decide ((a i).1 ≤ (3 / 5 : ℝ)) :=
      congrArg Prod.snd (ha i)
    simp only [htTerm]
    by_cases h : (a i).1 ≤ (3 / 5 : ℝ) <;>
      cases hx : (a i).2.1 <;>
        norm_num [IntervalExample.study, IntervalExample.score, W, X, Y, Y0, Y1,
          bit, wholeCat, h, hx, hy1]
  have hht : ht IntervalExample.study a = (wholeS a : ℝ) / 65 := by
    simp only [ht, hterm]
    simp only [sum_ite, sum_const, nsmul_eq_mul, mul_zero, add_zero]
    change ((wholeS a : ℝ) * (20 / 13)) / 100 = _
    ring
  have hxiterm (i : Fin 100) :
      (IntervalExample.study.pi (W (a i)))⁻¹ ^ 2 =
        if (a i).1 ≤ (3 / 5 : ℝ) then (400 / 169 : ℝ) else 10000 / 9801 := by
    by_cases h : (a i).1 ≤ (3 / 5 : ℝ) <;>
      norm_num [IntervalExample.study, IntervalExample.score, W, h]
  have hxi : xi IntervalExample.study a = IntervalExample.xiK (wholeK a) := by
    simp only [xi, hxiterm, hsum, IntervalExample.xiK]
    ring
  have hmean : mu IntervalExample.study = 3 / 5 := by
    change AronowAudit.P046.mu
      (SAP.P046.Bridge.toStudy SAP.P046.IntervalExample.study) = 3 / 5
    rw [SAP.P046.Bridge.interval_study]
    exact AronowAudit.P046.IntervalExample.probability_continuity_mean.2.2
  refine ⟨hht, ?_, hxi⟩
  rw [hht, hmean]
  ring

end
