import AronowAudit.P005.Wave1.Lib.ArmDebiasedOrderTailC

/-! Exact debiased linear expansions, using the unconditional arm order. -/

namespace AronowAudit.P005.Wave1

noncomputable section
open scoped BigOperators Matrix
open Finset Filter
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

theorem tailC_mean_residual {n d : ℕ} (P : Population n d)
    (S : Finset (Fin n)) (hS : S.Nonempty) (y : Fin n → ℝ) (v : Fin d → ℝ) :
    mean S (fun i => centered y i - dot (P.x i) v) =
      mean S y - popMean y - dot (xMean P S) v := by
  rw [mean_sub, mean_dot]
  unfold centered
  rw [mean_sub, mean_const S hS]

theorem tailC_dot_sub_left {d : ℕ} (a b v : Fin d → ℝ) :
    dot (a-b) v = dot a v - dot b v := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem tailC_dot_weighted_right {d : ℕ} (x u v : Fin d → ℝ) (p q : ℝ) :
    dot x (p • u + q • v) = p * dot x u + q * dot x v := by
  simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

/-- An arm remainder, with the integrand of P005-T11(c). -/
def tailC_arm_remainder {n d : ℕ} (P : Population n d) (t : Arm)
    (S : Finset (Fin n)) : ℝ :=
  let A := armSet t S
  let y := if t = .treated then P.yT else P.yC
  armDebiased P A y - (mean A y - dot (xMean P A) (populationSlope P y))

theorem tailC_weighted_remainder {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0)
    (S : Finset (Fin n)) (hS : S ∈ design n m) (hinv : (Lhat P m S).det ≠ 0) :
    debiasedATE P m S - ate P - commonLeading P m S =
      (pT n m / pC n m) * tailC_arm_remainder P .treated S -
      (pC n m / pT n m) * tailC_arm_remainder P .control S := by
  have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
  have hc : (control S).card = n-m := by
    rw [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp [hs]
  have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
  have hCn : (control S).Nonempty := Finset.card_pos.mp (by omega)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hnm : (n : ℝ)-m ≠ 0 := by
    have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
    exact ne_of_gt (sub_pos.mpr hmnR)
  have hn2 : (n : ℝ)-2 ≠ 0 := by
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hdiff := complement_x_mean_identity P (by omega) hm hmn hx S hS
  have hproj : ∀ v : Fin d → ℝ,
      dot (xMean P S-xMean P (control S)) v =
        (1/pC n m) * dot (xMean P S) v := by
    intro v
    rw [hdiff]
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hprojC : ∀ v : Fin d → ℝ,
      dot (xMean P S-xMean P (control S)) v =
        -(1/pT n m) * dot (xMean P (control S)) v := by
    intro v
    have h₁ := hproj v
    have h₂ := tailC_dot_sub_left (xMean P S) (xMean P (control S)) v
    have h₂n := congrArg (fun z : ℝ => (n : ℝ)*z) h₂
    dsimp only [pT, pC] at h₁ ⊢
    field_simp [hn0, hm0, hnm] at h₁ ⊢
    nlinarith [h₂n]
  have hw : ∀ u v : Fin d → ℝ,
      dot (xMean P S-xMean P (control S))
        (pT n m • u + pC n m • v) =
      (pT n m/pC n m)*dot (xMean P S) u -
        (pC n m/pT n m)*dot (xMean P (control S)) v := by
    intro u v
    rw [tailC_dot_weighted_right, hproj u, hprojC v]
    ring
  have hexp := (noninteracted_debiased_expansion P m S (N P m)
    hn hm hmn hS hinv).1
  have hlead : commonLeading P m S =
      mean S P.yT - mean (control S) P.yC - ate P -
        dot (xMean P S-xMean P (control S)) (N P m) := by
    change mean S (fun i => centered P.yT i - dot (P.x i) (N P m)) -
      mean (control S) (fun i => centered P.yC i - dot (P.x i) (N P m)) = _
    rw [tailC_mean_residual P S hSn,
      tailC_mean_residual P (control S) hCn, tailC_dot_sub_left]
    unfold ate
    ring
  rw [hexp, hlead]
  simp only [Nhat, N, hw, tailC_arm_remainder, armSet, armDebiased, hs, hc,
    if_true, reduceCtorEq, if_false,
    Nat.cast_sub (le_of_lt hmn)]
  dsimp only [pT, pC]
  field_simp [hn0, hm0, hnm, hn2]
  <;> ring

theorem tailC_ratio_bounds (lo hi p q : ℝ)
    (hlo : 0 < lo) (hhi : hi < 1) (hlp : lo < p) (hph : p < hi)
    (hpq : p+q=1) :
    |p/q| ≤ 1/lo + 1/(1-hi) ∧ |q/p| ≤ 1/lo + 1/(1-hi) := by
  have hp : 0 < p := lt_trans hlo hlp
  have hq : 0 < q := by linarith
  have hqlo : 1-hi ≤ q := by linarith
  have hp1 : p ≤ 1 := by linarith
  have hq1 : q ≤ 1 := by linarith
  have hloinv : 0 ≤ 1/lo := le_of_lt (one_div_pos.2 hlo)
  have hhi0 : 0 < 1-hi := sub_pos.mpr hhi
  have hhiinv : 0 ≤ 1/(1-hi) := (one_div_pos.2 hhi0).le
  have hab : p/q ≤ 1/(1-hi) := by
    apply (div_le_iff₀ hq).2
    have heq : (1/(1-hi))*(1-hi) = 1 := one_div_mul_cancel (ne_of_gt hhi0)
    have hh := mul_le_mul_of_nonneg_left hqlo hhiinv
    nlinarith
  have hba : q/p ≤ 1/lo := by
    apply (div_le_iff₀ hp).2
    have heq : (1/lo)*lo = 1 := one_div_mul_cancel (ne_of_gt hlo)
    have hh := mul_le_mul_of_nonneg_left hlp.le hloinv
    nlinarith
  rw [abs_of_nonneg (div_nonneg hp.le hq.le), abs_of_nonneg (div_nonneg hq.le hp.le)]
  constructor <;> linarith

theorem noninteracted_debiased_linear_expansion_proof
    (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) (h : standingAssumptions d m P)
    (hinv : ∀ᶠ n in atTop, noninteractedRegular (P n) (m n))
    (hκ : Tendsto (fun n => kappa (P n)) atTop (nhds 0)) :
    stochasticLittleO m
      (fun n S => debiasedATE (P n) (m n) S - ate (P n) - commonLeading (P n) (m n) S)
      (fun n => Real.sqrt (1/(n : ℝ))) := by
  classical
  obtain ⟨lo, hi, hlo, hlohi, hhi, halloc⟩ := h.2.2.2
  have hB : 0 < 1/lo+1/(1-hi) :=
    add_pos (one_div_pos.2 hlo) (one_div_pos.2 (sub_pos.mpr hhi))
  have hT := tailC_arm_debiased_order d m P h Arm.treated
  have hC := tailC_arm_debiased_order d m P h Arm.control
  change stochasticO m (fun n S => tailC_arm_remainder (P n) .treated S)
    (fun n => Real.sqrt (kappa (P n)/n)) at hT
  change stochasticO m (fun n S => tailC_arm_remainder (P n) .control S)
    (fun n => Real.sqrt (kappa (P n)/n)) at hC
  have horder := tailC_order_combine m _ _
    (fun n S => debiasedATE (P n) (m n) S-ate (P n)-commonLeading (P n) (m n) S)
    (fun n => Real.sqrt (kappa (P n)/n))
    (fun n => pT n (m n)/pC n (m n))
    (fun n => pC n (m n)/pT n (m n)) hT hC _ hB (by
      filter_upwards [h.2.2.1, hinv, eventually_ge_atTop 3] with n hP hninv hn
      obtain ⟨hd, hdn, hm, hmn⟩ := h.1 n hn
      obtain ⟨hlo', hhi'⟩ := halloc n hn
      have hpq : pT n (m n)+pC n (m n)=1 := by
        dsimp [pT, pC]
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        field_simp [hn0]
        <;> ring
      have hb := tailC_ratio_bounds lo hi _ _ hlo hhi hlo' hhi' hpq
      intro S hS
      exact ⟨tailC_weighted_remainder (P n) hn hm hmn hP.1 S hS (hninv S hS), hb⟩)
  refine small_scale_littleO m _ _ horder ?_ hκ
  filter_upwards [h.2.2.1, eventually_ge_atTop 3] with n hP hn
  have hb := (kappa_bounds (P n) (by omega) hP.2).1
  exact le_trans (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hb


/-!
P005-T27: the interacted debiased remainder as a difference of arm remainders.
-/

theorem tailC_arm_remainder_difference {n d m : ℕ} (P : Population n d)
    (hm : 0 < m) (hmn : m < n) (S : Finset (Fin n)) (hS : S ∈ design n m) :
    interactedDebiasedATE P m S-ate P-armLeading P S =
      tailC_arm_remainder P .treated S-tailC_arm_remainder P .control S := by
  have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
  have hc : (control S).card = n-m := by
    rw [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp [hs]
  have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
  have hCn : (control S).Nonempty := Finset.card_pos.mp (by omega)
  rw [interacted_debiased_cancellation]
  have hTr : mean S (armResidual P P.yT) =
      mean S P.yT - popMean P.yT - dot (xMean P S) (populationSlope P P.yT) :=
    tailC_mean_residual P S hSn P.yT (populationSlope P P.yT)
  have hCr : mean (control S) (armResidual P P.yC) =
      mean (control S) P.yC - popMean P.yC - dot (xMean P (control S)) (populationSlope P P.yC) :=
    tailC_mean_residual P (control S) hCn P.yC (populationSlope P P.yC)
  simp only [armLeading, hTr, hCr, tailC_mean_residual P S hSn,
    tailC_mean_residual P (control S) hCn, tailC_arm_remainder, armSet,
    armDebiased, hs, hc, if_true, reduceCtorEq, if_false,
    Nat.cast_sub (le_of_lt hmn), ate]
  ring

theorem interacted_debiased_linear_expansion_proof
    (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) (h : standingAssumptions d m P)
    (hinv : ∀ᶠ n in atTop, interactedRegular (P n) (m n))
    (hκ : Tendsto (fun n => kappa (P n)) atTop (nhds 0)) :
    stochasticLittleO m
      (fun n S => interactedDebiasedATE (P n) (m n) S - ate (P n) - armLeading (P n) S)
      (fun n => Real.sqrt (1/(n : ℝ))) := by
  classical
  have hT := tailC_arm_debiased_order d m P h Arm.treated
  have hC := tailC_arm_debiased_order d m P h Arm.control
  change stochasticO m (fun n S => tailC_arm_remainder (P n) .treated S)
    (fun n => Real.sqrt (kappa (P n)/n)) at hT
  change stochasticO m (fun n S => tailC_arm_remainder (P n) .control S)
    (fun n => Real.sqrt (kappa (P n)/n)) at hC
  have horder := tailC_order_combine m _ _
    (fun n S => interactedDebiasedATE (P n) (m n) S-ate (P n)-armLeading (P n) S)
    (fun n => Real.sqrt (kappa (P n)/n)) (fun _ => 1) (fun _ => 1) hT hC 1
    (by norm_num) (by
      filter_upwards [eventually_ge_atTop 3] with n hn
      obtain ⟨hd, hdn, hm, hmn⟩ := h.1 n hn
      intro S hS
      refine ⟨?_, by norm_num, by norm_num⟩
      simpa only [one_mul] using tailC_arm_remainder_difference (P n) hm hmn S hS)
  refine small_scale_littleO m _ _ horder ?_ hκ
  filter_upwards [h.2.2.1, eventually_ge_atTop 3] with n hP hn
  exact le_trans (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (kappa_bounds (P n) (by omega) hP.2).1


end
end AronowAudit.P005.Wave1
