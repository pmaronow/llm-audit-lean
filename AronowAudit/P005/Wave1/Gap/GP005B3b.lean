import AronowAudit.P005.Wave1.Gap.GP005B1
import AronowAudit.P005.Wave1.ExactDecomposition

namespace AronowAudit.P005.Wave1

noncomputable section
open scoped BigOperators Matrix
open Finset Filter
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

lemma GP005B3b_T21_expectation_add {n : ℕ} (m : ℕ) (f g : Finset (Fin n) → ℝ) :
    expectation m (fun S => f S + g S) = expectation m f + expectation m g := by
  simp only [expectation, Finset.sum_add_distrib, add_div]

lemma GP005B3b_T21_expectation_sub {n : ℕ} (m : ℕ) (f g : Finset (Fin n) → ℝ) :
    expectation m (fun S => f S - g S) = expectation m f - expectation m g := by
  simp only [expectation, Finset.sum_sub_distrib, sub_div]

lemma GP005B3b_T21_card {n m : ℕ} {S : Finset (Fin n)} (hS : S ∈ design n m) :
    S.card = m := (Finset.mem_powersetCard.mp hS).2

lemma GP005B3b_T21_control_card {n m : ℕ} {S : Finset (Fin n)} (hS : S ∈ design n m) :
    (control S).card = n - m := by
  rw [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  simp only [Finset.card_univ, Fintype.card_fin, GP005B3b_T21_card hS]

lemma GP005B3b_T21_control_control {n : ℕ} (S : Finset (Fin n)) : control (control S) = S := by
  ext i
  simp [control]

lemma GP005B3b_T21_control_mem {n m : ℕ} {S : Finset (Fin n)} (hS : S ∈ design n m) :
    control S ∈ design n (n-m) :=
  Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, GP005B3b_T21_control_card hS⟩

lemma GP005B3b_T21_expectation_control {n m : ℕ} (hmn : m ≤ n)
    (f : Finset (Fin n) → ℝ) :
    expectation m (fun S => f (control S)) = expectation (n-m) f := by
  have hs : (∑ S ∈ design n m, f (control S)) = ∑ S ∈ design n (n-m), f S := by
    refine Finset.sum_bij (fun S _ => control S) (fun S hS => GP005B3b_T21_control_mem hS) ?_ ?_ ?_
    · intro S hS U hU hSU
      simpa only [GP005B3b_T21_control_control] using congrArg control hSU
    · intro U hU
      refine ⟨control U, ?_, GP005B3b_T21_control_control U⟩
      have hh := GP005B3b_T21_control_mem hU
      simpa only [show n-(n-m) = m by omega] using hh
    · intro S hS
      rfl
  unfold expectation
  rw [hs]
  simp only [design, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    Nat.choose_symm hmn]

lemma GP005B3b_T21_mean_control_unbiased {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hmn : m < n) (a : Fin n → ℝ) :
    expectation m (fun S => mean (control S) a) = popMean a := by
  rw [GP005B3b_T21_expectation_control (le_of_lt hmn) (fun A => mean A a)]
  exact mean_unbiased hn (Nat.sub_pos_of_lt hmn) (Nat.sub_le _ _) a

lemma GP005B3b_T21_sum_centered {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    ∑ i, centered a i = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp only [centered, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, popMean, mean]
  field_simp [hn0]
  <;> ring

lemma GP005B3b_T21_sum_x {n d : ℕ} (P : Population n d) (hx : xMean P univ = 0)
    (k : Fin d) : ∑ i, P.x i k = 0 := by
  have h : (∑ i, P.x i k)/(n : ℝ) = 0 := by
    simpa only [xMean, mean, Finset.card_univ, Fintype.card_fin, Pi.zero_apply] using
      congrArg (fun v : Fin d → ℝ => v k) hx
  by_cases hn : (n : ℝ) = 0
  · have hn' : n = 0 := by exact_mod_cast hn
    subst n
    simp
  · exact (div_eq_zero_iff.mp h).resolve_right hn

lemma GP005B3b_T21_dot_add {d : ℕ} (u v w : Fin d → ℝ) :
    dot u (v+w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma GP005B3b_T21_dot_sub {d : ℕ} (u v w : Fin d → ℝ) :
    dot u (v-w) = dot u v - dot u w := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma GP005B3b_T21_dot_smul {d : ℕ} (u v : Fin d → ℝ) (c : ℝ) :
    dot u (c • v) = c*dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma GP005B3b_T21_dot_smul_left {d : ℕ} (u v : Fin d → ℝ) (c : ℝ) :
    dot (c • u) v = c*dot u v := by
  rw [dot_comm, GP005B3b_T21_dot_smul, dot_comm v u]

lemma GP005B3b_T21_arm_unbiased {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (y : Fin n → ℝ) :
    expectation m (fun S => armDebiased P S y) = popMean y := by
  exact control_arm_unbiased_any_size P hn hm (le_of_lt hmn) hP.1 y

lemma GP005B3b_T21_control_arm_unbiased {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (y : Fin n → ℝ) :
    expectation m (fun S => armDebiased P (control S) y) = popMean y := by
  rw [GP005B3b_T21_expectation_control (le_of_lt hmn) (fun A => armDebiased P A y)]
  exact GP005B3b_T21_arm_unbiased P hn (Nat.sub_pos_of_lt hmn) (Nat.sub_lt (by omega) hm) hP y

/-- Exact inverse cancellation expresses the pooled debiased estimator through the two arms. -/
lemma GP005B3b_T21_inverse_free_identity {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (hinv : noninteractedRegular P m) (S : Finset (Fin n)) (hS : S ∈ design n m) :
    debiasedATE P m S = mean S P.yT-mean (control S) P.yC+
      (pT n m/pC n m)*(armDebiased P S P.yT-mean S P.yT)-
      (pC n m/pT n m)*(armDebiased P (control S) P.yC-mean (control S) P.yC) := by
  have hW := control_minus_treated_mean_identities P (by omega) hm hmn hP.1 S hS
  have hbase := (noninteracted_debiased_expansion P m S (N P m) hn hm hmn hS (hinv S hS)).1
  have hdot : dot (xMean P S-xMean P (control S)) (Nhat P m S) =
      (pT n m/pC n m)*dot (xMean P S) (armN P S P.yT)-
        (pC n m/pT n m)*dot (xMean P (control S)) (armN P (control S) P.yC) := by
    have hT : dot (xMean P S-xMean P (control S)) (armN P S P.yT) =
        (1/pC n m)*dot (xMean P S) (armN P S P.yT) := by
      rw [complement_x_mean_identity P (by omega) hm hmn hP.1 S hS, GP005B3b_T21_dot_smul_left]
    have hC : dot (xMean P S-xMean P (control S)) (armN P (control S) P.yC) =
        -(1/pT n m)*dot (xMean P (control S)) (armN P (control S) P.yC) := by
      have hneg : xMean P S-xMean P (control S) =
          (-1/pT n m) • xMean P (control S) := by
        have hh := congrArg Neg.neg hW.1
        simpa only [neg_sub, neg_smul, neg_div] using hh
      rw [hneg, GP005B3b_T21_dot_smul_left]
      ring
    simp only [Nhat, GP005B3b_T21_dot_add, GP005B3b_T21_dot_smul, hT, hC]
    ring
  rw [hbase, hdot]
  simp only [armDebiased, GP005B3b_T21_card hS, GP005B3b_T21_control_card hS]
  rw [Nat.cast_sub (le_of_lt hmn)]
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hc0 : (n : ℝ)-m ≠ 0 := by linarith
  have hn2 : (n : ℝ)-2 ≠ 0 := by linarith
  dsimp only [pT, pC]
  field_simp [hn0, hm0, hc0, hn2]
  <;> ring

theorem noninteracted_exact_unbiasedness_proof {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (hinv : noninteractedRegular P m) :
    expectation m (biasEstimate P m) = expectation m (adjustedATE P m) - ate P ∧
    expectation m (debiasedATE P m) = ate P := by
  have hD : expectation m (debiasedATE P m) = ate P := by
    have hh := expectation_congr m (debiasedATE P m) _
      (GP005B3b_T21_inverse_free_identity P hn hm hmn hP hinv)
    simp only [GP005B3b_T21_expectation_add, GP005B3b_T21_expectation_sub, expectation_mul,
      GP005B3b_T21_arm_unbiased P hn hm hmn hP P.yT,
      GP005B3b_T21_control_arm_unbiased P hn hm hmn hP P.yC,
      mean_unbiased (by omega : 0 < n) hm (le_of_lt hmn) P.yT,
      GP005B3b_T21_mean_control_unbiased (by omega : 0 < n) hm hmn P.yC,
      sub_self, mul_zero, add_zero, sub_zero] at hh
    exact hh
  have hsub : expectation m (debiasedATE P m) =
      expectation m (adjustedATE P m)-expectation m (biasEstimate P m) :=
    GP005B3b_T21_expectation_sub m _ _
  exact ⟨by linarith, hD⟩

lemma GP005B3b_T22_inverse_free_identity {n d m : ℕ} (P : Population n d)
    (hmn : m < n) (S : Finset (Fin n)) (hS : S ∈ design n m) :
    interactedDebiasedATE P m S = armDebiased P S P.yT-armDebiased P (control S) P.yC := by
  rw [interacted_debiased_cancellation]
  simp only [armDebiased, GP005B3b_T21_card hS, GP005B3b_T21_control_card hS]
  rw [Nat.cast_sub (le_of_lt hmn)]
  ring

theorem interacted_exact_unbiasedness_proof {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (hinv : interactedRegular P m) :
    expectation m (interactedBiasEstimate P m) = expectation m (interactedATE P) - ate P ∧
    expectation m (interactedDebiasedATE P m) = ate P ∧
    expectation m (fun S => armDebiased P S P.yT) = popMean P.yT ∧
    expectation m (fun S => armDebiased P (control S) P.yC) = popMean P.yC := by
  have hT := GP005B3b_T21_arm_unbiased P hn hm hmn hP P.yT
  have hC := GP005B3b_T21_control_arm_unbiased P hn hm hmn hP P.yC
  have hD : expectation m (interactedDebiasedATE P m) = ate P := by
    rw [expectation_congr m _ _ (GP005B3b_T22_inverse_free_identity P hmn),
      GP005B3b_T21_expectation_sub, hT, hC]
    rfl
  have hsub : expectation m (interactedDebiasedATE P m) =
      expectation m (interactedATE P)-expectation m (interactedBiasEstimate P m) :=
    GP005B3b_T21_expectation_sub m _ _
  exact ⟨by linarith, hD, hT, hC⟩

lemma GP005B3b_T23_dot_sub_left {d : ℕ} (u v w : Fin d → ℝ) :
    dot (u-v) w = dot u w-dot v w := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem interacted_exact_decomposition_proof {n d m : ℕ} (P : Population n d)
    (hn : 2 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (hinv : interactedRegular P m) :
    (∀ S ∈ design n m,
      armBetaHat P S P.yT = populationSlope P P.yT + armNu1 P S P.yT + armNu2 P S P.yT + armNu3 P S P.yT ∧
      armBetaHat P (control S) P.yC = populationSlope P P.yC + armNu1 P (control S) P.yC +
        armNu2 P (control S) P.yC + armNu3 P (control S) P.yC) ∧
    expectation m (fun S => interactedATE P S - ate P) =
      expectation m (fun S => dot (xMean P (control S))
        (armNu1 P (control S) P.yC + armNu2 P (control S) P.yC + armNu3 P (control S) P.yC)) -
      expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT + armNu2 P S P.yT + armNu3 P S P.yT)) ∧
    expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT)) =
      ((n : ℝ)-m)/((n-1 : ℝ)*m)*leverageCov P P.yT ∧
    expectation m (fun S => dot (xMean P (control S)) (armNu1 P (control S) P.yC)) =
      (m : ℝ)/((n-1 : ℝ)*(n-m))*leverageCov P P.yC ∧
    expectation m (fun S => dot (xMean P (control S)) (armNu1 P (control S) P.yC)) -
      expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT)) =
      (m : ℝ)/((n-1 : ℝ)*(n-m))*leverageCov P P.yC -
        ((n : ℝ)-m)/((n-1 : ℝ)*m)*leverageCov P P.yT := by
  exact interacted_exact_decomposition_completion P hn hm hmn hP hinv


lemma GP005B3b_T21_second_centered_left {n m : ℕ} (hn : 3 ≤ n) (hm : 0 < m)
    (hmn : m < n) (a b : Fin n → ℝ) (ha : ∑ i, a i = 0) :
    expectation m (fun S => mean S a*mean S b) =
      ((n : ℝ)-m)/((m : ℝ)*(n-1))*popMean (fun i => a i*b i) := by
  apply control_arm_centered_mean_product hn hm (le_of_lt hmn) a b
  simp only [popMean, mean, ha, zero_div]

lemma GP005B3b_T25_allocation {n m : ℕ} (hn : 0 < n) : pT n m+pC n m = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  dsimp only [pT, pC]
  field_simp [hn0]
  <;> ring

lemma GP005B3b_T25_control_mean {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0)
    (S : Finset (Fin n)) (hS : S ∈ design n m) :
    xMean P (control S) = (-(pT n m/pC n m)) • xMean P S := by
  have hh := complement_x_mean_identity P hn hm hmn hx S hS
  have hq : pC n m ≠ 0 := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
    exact ne_of_gt (div_pos (sub_pos.mpr hmnR) hnR)
  have hpq := GP005B3b_T25_allocation (m := m) hn
  have hp : pT n m = 1-pC n m := by linarith
  have hcoef : 1-1/pC n m = -(pT n m/pC n m) := by
    rw [hp]
    field_simp [hq]
    <;> ring
  funext k
  have hk := congrArg (fun v : Fin d → ℝ => v k) hh
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
  calc
    _ = (1-1/pC n m)*xMean P S k := by linarith [hk]
    _ = _ := by rw [hcoef]

/-- Centering gives a rank-one formula for the pooled normal matrix. -/
lemma GP005B3b_T25_rank_one {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0)
    (S : Finset (Fin n)) (hS : S ∈ design n m) :
    Lhat P m S = 1-(pT n m/pC n m) • Matrix.vecMulVec (xMean P S) (xMean P S) := by
  have hC := GP005B3b_T25_control_mean P hn hm hmn hx S hS
  have hpq := GP005B3b_T25_allocation (m := m) hn
  have hq : pC n m ≠ 0 := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
    exact ne_of_gt (div_pos (sub_pos.mpr hmnR) hnR)
  rw [Lhat, hC]
  ext k l
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.smul_apply, smul_eq_mul]
  have hp : pT n m = 1-pC n m := by linarith
  rw [hp]
  field_simp [hq]
  <;> ring

lemma GP005B3b_T25_rank_one_row {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0)
    (S : Finset (Fin n)) (hS : S ∈ design n m) (v : Fin d → ℝ) :
    dot (xMean P S) (Lhat P m S *ᵥ v) =
      (1-(pT n m/pC n m)*dot (xMean P S) (xMean P S))*dot (xMean P S) v := by
  rw [GP005B3b_T25_rank_one P hn hm hmn hx S hS, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  change dot (xMean P S) (v-(pT n m/pC n m) •
    (fun k => xMean P S k*dot (xMean P S) v)) = _
  simp only [GP005B3b_T21_dot_sub, GP005B3b_T21_dot_smul]
  have hh : dot (xMean P S) (fun k => xMean P S k*dot (xMean P S) v) =
      dot (xMean P S) (xMean P S)*dot (xMean P S) v := by
    simp only [dot, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hh]
  ring

lemma GP005B3b_T25_inverse_row {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0)
    (S : Finset (Fin n)) (hS : S ∈ design n m) (hinv : (Lhat P m S).det ≠ 0)
    (hgood : (pT n m/pC n m)*dot (xMean P S) (xMean P S) ≤ 1/2)
    (v : Fin d → ℝ) :
    dot (xMean P S) ((Lhat P m S)⁻¹ *ᵥ v) =
      dot (xMean P S) v/(1-(pT n m/pC n m)*dot (xMean P S) (xMean P S)) := by
  have hden : 1-(pT n m/pC n m)*dot (xMean P S) (xMean P S) ≠ 0 := by linarith
  have hsolve : Lhat P m S *ᵥ ((Lhat P m S)⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hinv),
      Matrix.one_mulVec]
  have hh := GP005B3b_T25_rank_one_row P hn hm hmn hx S hS ((Lhat P m S)⁻¹ *ᵥ v)
  rw [hsolve] at hh
  apply (eq_div_iff hden).2
  nlinarith [hh]

lemma GP005B3b_T25_inverse_factor_bound {a : ℝ} (ha : a ≤ 1/2) :
    0 < 1-a ∧ (1/(1-a) : ℝ) ≤ 2 := by
  have hden : 0 < 1-a := by linarith
  exact ⟨hden, (div_le_iff₀ hden).2 (by linarith)⟩

lemma GP005B3b_T25_remainder_slope {n d m : ℕ} (P : Population n d)
    (hm : 0 < m) (hmn : m < n) (S : Finset (Fin n)) (hS : S ∈ design n m) :
    adjustedATE P m S-ate P-commonLeading P m S =
      -dot (xMean P S-xMean P (control S)) (betaHat P m S-N P m) := by
  have hT : S.Nonempty := Finset.card_pos.mp (by rw [GP005B3b_T21_card hS]; exact hm)
  have hC : (control S).Nonempty := Finset.card_pos.mp
    (by rw [GP005B3b_T21_control_card hS]; exact Nat.sub_pos_of_lt hmn)
  have hmean : ∀ (A : Finset (Fin n)), A.Nonempty → ∀ y : Fin n → ℝ,
      mean A (commonResidual P m y) = mean A y-popMean y-dot (xMean P A) (N P m) := by
    intro A hA y
    change mean A (fun i => (y i-popMean y)-dot (P.x i) (N P m)) = _
    rw [mean_sub, mean_sub, mean_const A hA, mean_dot]
  rw [adjustedATE, commonLeading, hmean S hT P.yT, hmean (control S) hC P.yC]
  simp only [ate, GP005B3b_T21_dot_sub, GP005B3b_T23_dot_sub_left]
  ring

lemma GP005B3b_T25_remainder_inverse {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0)
    (S : Finset (Fin n)) (hS : S ∈ design n m) (hinv : (Lhat P m S).det ≠ 0)
    (hgood : (pT n m/pC n m)*dot (xMean P S) (xMean P S) ≤ 1/2) :
    adjustedATE P m S-ate P-commonLeading P m S =
      -(1/pC n m)*
        (dot (xMean P S) (Nhat P m S-Lhat P m S *ᵥ N P m)/
          (1-(pT n m/pC n m)*dot (xMean P S) (xMean P S))) := by
  have hslope : betaHat P m S-N P m =
      (Lhat P m S)⁻¹ *ᵥ (Nhat P m S-Lhat P m S *ᵥ N P m) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hinv), Matrix.one_mulVec]
    rfl
  rw [GP005B3b_T25_remainder_slope P hm hmn S hS, hslope,
    complement_x_mean_identity P hn hm hmn hx S hS, GP005B3b_T21_dot_smul_left,
    GP005B3b_T25_inverse_row P hn hm hmn hx S hS hinv hgood]
  ring

lemma GP005B3b_T25_xmean_second_moment {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P) :
    expectation m (fun S => dot (xMean P S) (xMean P S)) =
      ((n : ℝ)-m)/((m : ℝ)*(n-1))*d := by
  unfold dot xMean
  rw [expectation_sum]
  simp_rw [GP005B3b_T21_second_centered_left hn hm hmn _ _ (GP005B3b_T21_sum_x P hP.1 _)]
  rw [← Finset.mul_sum]
  have hh : (∑ k, popMean (fun i => P.x i k*P.x i k)) = (d : ℝ) := by
    have hg : ∀ k : Fin d, popMean (fun i => P.x i k*P.x i k) = 1 := by
      intro k
      simpa only [gram, Matrix.one_apply_eq] using
        congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M k k) hP.2
    simp only [hg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hh]


lemma GP005B3b_T25_dot_nonneg {d : ℕ} (v : Fin d → ℝ) : 0 ≤ dot v v := by
  unfold dot
  exact Finset.sum_nonneg (fun k _ => mul_self_nonneg _)

lemma GP005B3b_T25_dot_cauchy {d : ℕ} (u v : Fin d → ℝ) :
    (dot u v)^2 ≤ dot u u*dot v v := by
  simpa only [dot, ← sq] using Finset.sum_mul_sq_le_sq_mul_sq univ u v

lemma GP005B3b_T25_mean_cauchy {n : ℕ} (a b : Fin n → ℝ) :
    (popMean (fun i => a i*b i))^2 ≤
      popMean (fun i => a i^2)*popMean (fun i => b i^2) := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq univ a b
  have hd := div_le_div_of_nonneg_right hh (sq_nonneg (n : ℝ))
  convert hd using 1 <;>
    simp only [popMean, mean, Finset.card_univ, Fintype.card_fin, div_pow] <;> ring

lemma GP005B3b_T25_projection_square {n d : ℕ} (P : Population n d)
    (hG : gram P = 1) (v : Fin d → ℝ) :
    popMean (fun i => (dot v (P.x i))^2) = dot v v := by
  have hp := populationSlope_projection P hG v
  have hh := dot_population_slope P v (fun i => dot (P.x i) v)
  rw [hp] at hh
  have hf : (fun i => dot v (P.x i)*dot (P.x i) v) =
      (fun i => (dot v (P.x i))^2) := by
    funext i
    rw [dot_comm (P.x i) v, sq]
  rw [hf] at hh
  exact hh.symm

lemma GP005B3b_T25_population_projection_bound {n d : ℕ} (P : Population n d)
    (hG : gram P = 1) (v : Fin d → ℝ) (y : Fin n → ℝ) :
    (dot v (populationSlope P y))^2 ≤ dot v v*popMean (fun i => y i^2) := by
  rw [dot_population_slope]
  have hh := GP005B3b_T25_mean_cauchy (fun i => dot v (P.x i)) y
  rwa [GP005B3b_T25_projection_square P hG v] at hh

lemma GP005B3b_T25_mean_sq_le {n : ℕ} (A : Finset (Fin n)) (hA : A.Nonempty)
    (y : Fin n → ℝ) : (mean A y)^2 ≤ mean A (fun i => y i^2) := by
  have hh := (mean_square_centering A hA y).1
  have h0 := mean_nonneg A (fun i => (y i-mean A y)^2) (fun i _ => sq_nonneg _)
  linarith

lemma GP005B3b_T25_centered_square_bound {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (K : ℝ) (hy : popMean (fun i => y i^2) ≤ K) :
    popMean (fun i => (centered y i)^2) ≤ K := by
  have hu : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  exact le_trans (by simpa only [centered, popMean] using (mean_square_centering univ hu y).2) hy

lemma GP005B3b_T25_scalar_fluctuation_bound {n m : ℕ} (hn : 3 ≤ n) (hm : 0 < m)
    (hmn : m < n) (b : Fin n → ℝ) :
    expectation m (fun S => (mean S b-popMean b)^2) ≤
      ((n : ℝ)-m)/((m : ℝ)*(n-1))*popMean (fun i => b i^2) := by
  have hf : ∀ S ∈ design n m, (mean S b-popMean b)^2 =
      mean S (centered b)*mean S (centered b) := by
    intro S hS
    have hne : S.Nonempty := Finset.card_pos.mp (by rw [GP005B3b_T21_card hS]; exact hm)
    change (mean S b-popMean b)^2 =
      mean S (fun i => b i-popMean b)*mean S (fun i => b i-popMean b)
    rw [mean_sub, mean_const S hne, sq]
  rw [expectation_congr m _ _ hf,
    GP005B3b_T21_second_centered_left hn hm hmn _ _ (GP005B3b_T21_sum_centered (by omega) b)]
  have hu : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  have hcent : popMean (fun i => centered b i*centered b i) ≤ popMean (fun i => b i^2) := by
    simpa only [centered, popMean, sq] using (mean_square_centering univ hu b).2
  have hρ : 0 ≤ ((n : ℝ)-m)/((m : ℝ)*(n-1)) := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
    exact div_nonneg (by linarith) (mul_nonneg hmR.le (by linarith))
  exact mul_le_mul_of_nonneg_left hcent hρ

lemma GP005B3b_T25_nu1_energy_bound {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (y : Fin n → ℝ) (K : ℝ)
    (hy : popMean (fun i => y i^2) ≤ K) :
    expectation m (fun S => dot (armNu1 P S y) (armNu1 P S y)) ≤
      (((n : ℝ)-m)/((m : ℝ)*(n-1)))*n*kappa P*K := by
  have hn0 : 0 < n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
  let ρ : ℝ := ((n : ℝ)-m)/((m : ℝ)*(n-1))
  have hρ : 0 ≤ ρ := by
    dsimp only [ρ]
    exact div_nonneg (by linarith) (mul_nonneg hmR.le (by linarith))
  have hκ : 0 ≤ (n : ℝ)*kappa P := by
    exact le_trans (leverage_nonneg P ⟨0, hn0⟩) (leverage_le_maximum P hn0 ⟨0, hn0⟩)
  have hY := GP005B3b_T25_centered_square_bound hn0 y K hy
  have he : expectation m (fun S => dot (armNu1 P S y) (armNu1 P S y)) ≤
      ρ*(∑ k, popMean (fun i => (centered y i*P.x i k)^2)) := by
    simp only [dot, armNu1]
    rw [expectation_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    simpa only [sq] using GP005B3b_T25_scalar_fluctuation_bound hn hm hmn
      (fun i => centered y i*P.x i k)
  have hsum : (∑ k, popMean (fun i => (centered y i*P.x i k)^2)) =
      popMean (fun i => leverage P i*(centered y i)^2) := by
    rw [← popMean_sum]
    congr 1
    funext i
    simp only [leverage, dot, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsum] at he
  calc
    _ ≤ ρ*popMean (fun i => leverage P i*(centered y i)^2) := he
    _ ≤ ρ*popMean (fun i => ((n : ℝ)*kappa P)*(centered y i)^2) := by
      apply mul_le_mul_of_nonneg_left _ hρ
      apply mean_mono
      intro i hi
      exact mul_le_mul_of_nonneg_right (leverage_le_maximum P hn0 i) (sq_nonneg _)
    _ = ρ*((n : ℝ)*kappa P)*popMean (fun i => (centered y i)^2) := by
      change ρ*mean univ (fun i => ((n : ℝ)*kappa P)*(centered y i)^2) =
        ρ*((n : ℝ)*kappa P)*mean univ (fun i => (centered y i)^2)
      rw [mean_mul]
      ring
    _ ≤ ρ*((n : ℝ)*kappa P)*K := mul_le_mul_of_nonneg_left hY (mul_nonneg hρ hκ)
    _ = _ := by dsimp only [ρ] <;> ring

lemma GP005B3b_T25_rho_bound {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) (hmn : m < n)
    {c : ℝ} (hc : 0 < c) (halloc : c ≤ pT n m) :
    ((n : ℝ)-m)/((m : ℝ)*(n-1)) ≤ 2/(c*n) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnpos : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < n-1 := by linarith
  have hmc : c*(n : ℝ) ≤ m := (le_div_iff₀ hnpos).mp halloc
  apply (div_le_div_iff₀ (mul_pos hmR hn1) (mul_pos hc hnpos)).2
  calc
    ((n : ℝ)-m)*(c*n) ≤ n*(c*n) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ ≤ (2*(n-1))*(c*n) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 2*(c*n)*(n-1) := by ring
    _ ≤ 2*m*(n-1) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmc (by norm_num : (0 : ℝ) ≤ 2)) hn1.le
    _ = _ := by ring

lemma GP005B3b_T25_energy_moments {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (K : ℝ) (hK : 0 ≤ K) (hT : popMean (fun i => P.yT i^2) ≤ K)
    (hC : popMean (fun i => P.yC i^2) ≤ K)
    (c : ℝ) (hc : 0 < c) (hp : c ≤ pT n m) (hq : c ≤ pC n m) :
    expectation m (fun S => dot (xMean P S) (xMean P S)) ≤ (2/c)*((d : ℝ)/n) ∧
    expectation m (fun S => dot (armNu1 P S P.yT) (armNu1 P S P.yT)) ≤ (2*K/c)*kappa P ∧
    expectation m (fun S => dot (armNu1 P (control S) P.yC) (armNu1 P (control S) P.yC)) ≤
      (2*K/c)*kappa P ∧
    expectation m (fun S => (mean S (centered P.yT))^2) ≤ K ∧
    expectation m (fun S => (mean (control S) (centered P.yC))^2) ≤ K := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hρ := GP005B3b_T25_rho_bound (by omega : 2 ≤ n) hm hmn hc hp
  have hρC := GP005B3b_T25_rho_bound (n := n) (m := n-m) (by omega)
    (Nat.sub_pos_of_lt hmn) (Nat.sub_lt (by omega) hm) hc
    (by simpa only [pT, pC, Nat.cast_sub (le_of_lt hmn)] using hq)
  have hκ : 0 ≤ kappa P := le_trans (div_nonneg (Nat.cast_nonneg d) hnpos.le)
    (kappa_bounds P (by omega) hP.2).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [GP005B3b_T25_xmean_second_moment P (by omega) hm hmn hP]
    calc
      _ ≤ (2/(c*n))*d := mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _)
      _ = _ := by ring
  · calc
      _ ≤ (((n : ℝ)-m)/((m : ℝ)*(n-1)))*n*kappa P*K :=
        GP005B3b_T25_nu1_energy_bound P (by omega) hm hmn P.yT K hT
      _ ≤ (2/(c*n))*n*kappa P*K := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg n)) hκ) hK
      _ = _ := by field_simp [ne_of_gt hc, ne_of_gt hnpos] <;> ring
  · rw [GP005B3b_T21_expectation_control (le_of_lt hmn)
      (fun A => dot (armNu1 P A P.yC) (armNu1 P A P.yC))]
    calc
      _ ≤ (((n : ℝ)-(n-m : ℕ))/(((n-m : ℕ) : ℝ)*(n-1)))*n*kappa P*K :=
        GP005B3b_T25_nu1_energy_bound P (by omega) (Nat.sub_pos_of_lt hmn)
          (Nat.sub_lt (by omega) hm) P.yC K hC
      _ ≤ (2/(c*n))*n*kappa P*K := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρC (Nat.cast_nonneg n)) hκ) hK
      _ = _ := by field_simp [ne_of_gt hc, ne_of_gt hnpos] <;> ring
  · calc
      _ ≤ expectation m (fun S => mean S (fun i => (centered P.yT i)^2)) := by
        unfold expectation
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro S hS
        exact GP005B3b_T25_mean_sq_le S (Finset.card_pos.mp (by rw [GP005B3b_T21_card hS]; exact hm)) _
      _ = popMean (fun i => (centered P.yT i)^2) := mean_unbiased (by omega) hm (le_of_lt hmn) _
      _ ≤ K := GP005B3b_T25_centered_square_bound (by omega) _ K hT
  · calc
      _ ≤ expectation m (fun S => mean (control S) (fun i => (centered P.yC i)^2)) := by
        unfold expectation
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro S hS
        exact GP005B3b_T25_mean_sq_le (control S) (Finset.card_pos.mp
          (by rw [GP005B3b_T21_control_card hS]; exact Nat.sub_pos_of_lt hmn)) _
      _ = popMean (fun i => (centered P.yC i)^2) := GP005B3b_T21_mean_control_unbiased (by omega) hm hmn _
      _ ≤ K := GP005B3b_T25_centered_square_bound (by omega) _ K hC

lemma GP005B3b_T25_probability_mono {n m : ℕ} (A B : Finset (Fin n) → Prop)
    (hAB : ∀ S ∈ design n m, A S → B S) : probability m A ≤ probability m B := by
  unfold probability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show (design n m).filter A ⊆ (design n m).filter B by
    intro S hS
    obtain ⟨hS, hA⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨hS, hAB S hS hA⟩)

lemma GP005B3b_T25_markov {n m : ℕ} (F : Finset (Fin n) → ℝ)
    (hF : ∀ S ∈ design n m, 0 ≤ F S) {H : ℝ} (hH : 0 < H) :
    probability m (fun S => H < F S) ≤ expectation m F/H := by
  have hsum : H*((((design n m).filter (fun S => H < F S)).card : ℕ) : ℝ) ≤
      ∑ S ∈ design n m, F S := by
    calc
      _ = H*(∑ S ∈ design n m, if H < F S then (1 : ℝ) else 0) := by
        rw [Finset.sum_boole]
      _ = ∑ S ∈ design n m, if H < F S then H else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        split_ifs <;> simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro S hS
        split_ifs with h
        · exact le_of_lt h
        · exact hF S hS
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg (design n m).card)
  apply (le_div_iff₀ hH).2
  dsimp only [probability, expectation]
  convert hdiv using 1 <;> ring

lemma GP005B3b_T25_abs_of_square {z B : ℝ} (hB : 0 ≤ B) (h : z^2 ≤ B^2) : |z| ≤ B := by
  apply (sq_le_sq₀ (abs_nonneg z) hB).mp
  simpa only [sq_abs] using h

lemma GP005B3b_T25_Nhat_decomposition {n d m : ℕ} (P : Population n d)
    (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (S : Finset (Fin n)) (hS : S ∈ design n m) :
    Nhat P m S = N P m+nu1 P m S+nu3 P m S := by
  have hT : S.Nonempty := Finset.card_pos.mp (by rw [GP005B3b_T21_card hS]; exact hm)
  have hC : (control S).Nonempty := Finset.card_pos.mp
    (by rw [GP005B3b_T21_control_card hS]; exact Nat.sub_pos_of_lt hmn)
  rw [Nhat, armN_decomposition P hP S hT P.yT,
    armN_decomposition P hP (control S) hC P.yC]
  funext k
  simp only [N, nu1, nu3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma GP005B3b_T25_pointwise_bound {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (K : ℝ) (hK : 0 ≤ K) (hT : popMean (fun i => P.yT i^2) ≤ K)
    (hC : popMean (fun i => P.yC i^2) ≤ K)
    (c H : ℝ) (hc : 0 < c) (hH : 1 ≤ H) (hq : c ≤ pC n m)
    (S : Finset (Fin n)) (hS : S ∈ design n m) (hinv : (Lhat P m S).det ≠ 0)
    (hV : dot (xMean P S) (xMean P S) ≤ H*((d : ℝ)/n))
    (hV1 : dot (xMean P S) (xMean P S) ≤ 1)
    (hU₁ : dot (armNu1 P S P.yT) (armNu1 P S P.yT) ≤ H*kappa P)
    (hU₂ : dot (armNu1 P (control S) P.yC) (armNu1 P (control S) P.yC) ≤ H*kappa P)
    (hY₁ : (mean S (centered P.yT))^2 ≤ H)
    (hY₂ : (mean (control S) (centered P.yC))^2 ≤ H)
    (hgood : (pT n m/pC n m)*dot (xMean P S) (xMean P S) ≤ 1/2) :
    |adjustedATE P m S-ate P-commonLeading P m S| ≤
      ((2/c)*(2*H+2*H^2+2*H*(K+1)/c))*Real.sqrt (kappa P*(d : ℝ)/n) := by
  let X := xMean P S
  let V := dot X X
  let t : ℝ := (d : ℝ)/n
  let r := Real.sqrt (kappa P*t)
  let a := (pT n m/pC n m)*V
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
  have hp0 : 0 ≤ pT n m := by dsimp only [pT]; positivity
  have hq0 : 0 < pC n m := lt_of_lt_of_le hc hq
  have hpq := GP005B3b_T25_allocation (m := m) (by omega : 0 < n)
  have hp1 : pT n m ≤ 1 := by linarith
  have hq1 : pC n m ≤ 1 := by linarith
  have hH0 : 0 < H := by linarith
  have ht0 : 0 ≤ t := div_nonneg (Nat.cast_nonneg _) hnR.le
  have hκ := (kappa_bounds P (by omega) hP.2).1
  have hκ0 : 0 ≤ kappa P := le_trans ht0 hκ
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r^2 = kappa P*t := Real.sq_sqrt (mul_nonneg hκ0 ht0)
  have htr : t ≤ r := by
    have hh := mul_le_mul_of_nonneg_right hκ ht0
    have hs : t^2 ≤ r^2 := by nlinarith
    have ha := GP005B3b_T25_abs_of_square hr0 hs
    simpa only [abs_of_nonneg ht0] using ha
  have hV0 : 0 ≤ V := GP005B3b_T25_dot_nonneg X
  have hpair : ∀ u : Fin d → ℝ, dot u u ≤ H*kappa P → |dot X u| ≤ H*r := by
    intro u hu
    apply GP005B3b_T25_abs_of_square (mul_nonneg hH0.le hr0)
    calc
      (dot X u)^2 ≤ V*dot u u := GP005B3b_T25_dot_cauchy X u
      _ ≤ (H*t)*(H*kappa P) := mul_le_mul hV hu (GP005B3b_T25_dot_nonneg u) (by positivity)
      _ = (H*r)^2 := by rw [mul_pow, hrsq] <;> ring
  have hAT := hpair (armNu1 P S P.yT) hU₁
  have hAC := hpair (armNu1 P (control S) P.yC) hU₂
  have hA : |dot X (nu1 P m S)| ≤ 2*H*r := by
    rw [nu1, GP005B3b_T21_dot_add, GP005B3b_T21_dot_smul, GP005B3b_T21_dot_smul]
    calc
      _ ≤ |pT n m*dot X (armNu1 P S P.yT)|+
          |pC n m*dot X (armNu1 P (control S) P.yC)| := abs_add_le _ _
      _ = pT n m*|dot X (armNu1 P S P.yT)|+
          pC n m*|dot X (armNu1 P (control S) P.yC)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg hq0.le]
      _ ≤ H*r+H*r := add_le_add
        (le_trans (mul_le_mul_of_nonneg_left hAT hp0) (mul_le_of_le_one_left (by positivity) hp1))
        (le_trans (mul_le_mul_of_nonneg_left hAC hq0.le) (mul_le_of_le_one_left (by positivity) hq1))
      _ = _ := by ring
  have hYT : |mean S (centered P.yT)| ≤ H :=
    GP005B3b_T25_abs_of_square hH0.le (le_trans hY₁ (by nlinarith))
  have hYC : |mean (control S) (centered P.yC)| ≤ H :=
    GP005B3b_T25_abs_of_square hH0.le (le_trans hY₂ (by nlinarith))
  have hν₃ : nu3 P m S =
      (-pT n m*(mean S (centered P.yT)-mean (control S) (centered P.yC))) • X := by
    have hcomp := GP005B3b_T25_control_mean P (by omega) hm hmn hP.1 S hS
    funext k
    simp only [nu3, armNu3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcomp]
    change _ = (-pT n m*(mean S (centered P.yT)-mean (control S) (centered P.yC)))*X k
    field_simp [ne_of_gt hq0]
    <;> ring
  have hB : |dot X (nu3 P m S)| ≤ 2*H^2*r := by
    rw [hν₃, GP005B3b_T21_dot_smul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hp0,
      abs_of_nonneg hV0]
    have hdiff : |mean S (centered P.yT)-mean (control S) (centered P.yC)| ≤ 2*H :=
      le_trans (abs_sub _ _) (by linarith)
    calc
      _ ≤ 1*(2*H)*(H*t) := mul_le_mul
        (mul_le_mul hp1 hdiff (abs_nonneg _) (by norm_num)) hV hV0 (by positivity)
      _ ≤ 2*H^2*r := by nlinarith [mul_le_mul_of_nonneg_left htr (by positivity : 0 ≤ 2*H^2)]
  have hpop : ∀ y : Fin n → ℝ, popMean (fun i => y i^2) ≤ K →
      |dot X (populationSlope P y)| ≤ K+1 := by
    intro y hy
    apply GP005B3b_T25_abs_of_square (by linarith)
    calc
      _ ≤ V*popMean (fun i => y i^2) := GP005B3b_T25_population_projection_bound P hP.2 X y
      _ ≤ V*K := mul_le_mul_of_nonneg_left hy hV0
      _ ≤ K := mul_le_of_le_one_left hK hV1
      _ ≤ (K+1)^2 := by nlinarith
  have hNX : |dot X (N P m)| ≤ 2*(K+1) := by
    rw [N, GP005B3b_T21_dot_add, GP005B3b_T21_dot_smul, GP005B3b_T21_dot_smul]
    calc
      _ ≤ |pT n m*dot X (populationSlope P P.yT)|+
          |pC n m*dot X (populationSlope P P.yC)| := abs_add_le _ _
      _ = pT n m*|dot X (populationSlope P P.yT)|+
          pC n m*|dot X (populationSlope P P.yC)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg hq0.le]
      _ ≤ (K+1)+(K+1) := add_le_add
        (le_trans (mul_le_mul_of_nonneg_left (hpop P.yT hT) hp0)
          (mul_le_of_le_one_left (by linarith) hp1))
        (le_trans (mul_le_mul_of_nonneg_left (hpop P.yC hC) hq0.le)
          (mul_le_of_le_one_left (by linarith) hq1))
      _ = _ := by ring
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have haV : a ≤ V/c := by
    dsimp only [a]
    have hratio : pT n m/pC n m ≤ 1/c := by
      calc
        _ ≤ 1/pC n m := div_le_div_of_nonneg_right hp1 hq0.le
        _ ≤ 1/c := one_div_le_one_div_of_le hc hq
    calc
      _ ≤ (1/c)*V := mul_le_mul_of_nonneg_right hratio hV0
      _ = _ := by ring
  have hD : |a*dot X (N P m)| ≤ (2*H*(K+1)/c)*r := by
    rw [abs_mul, abs_of_nonneg ha0]
    calc
      _ ≤ (V/c)*(2*(K+1)) := mul_le_mul haV hNX (abs_nonneg _) (by positivity)
      _ ≤ ((H*t)/c)*(2*(K+1)) := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hV hc.le) (by positivity)
      _ = (2*H*(K+1)/c)*t := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htr (by positivity)
  have hnum : dot X (Nhat P m S-Lhat P m S *ᵥ N P m) =
      dot X (nu1 P m S)+dot X (nu3 P m S)+a*dot X (N P m) := by
    rw [GP005B3b_T21_dot_sub, GP005B3b_T25_Nhat_decomposition P hm hmn hP S hS,
      GP005B3b_T21_dot_add, GP005B3b_T21_dot_add, GP005B3b_T25_rank_one_row P (by omega) hm hmn hP.1 S hS]
    dsimp only [a, V, X]
    ring
  have hden := GP005B3b_T25_inverse_factor_bound hgood
  have hpref : (1/pC n m)*(1/(1-a)) ≤ 2/c := by
    calc
      _ ≤ (1/c)*2 := mul_le_mul (one_div_le_one_div_of_le hc hq) hden.2
        (one_div_pos.mpr hden.1).le (by positivity)
      _ = _ := by ring
  rw [GP005B3b_T25_remainder_inverse P (by omega) hm hmn hP.1 S hS hinv hgood]
  change |-(1/pC n m)*(dot X (Nhat P m S-Lhat P m S *ᵥ N P m)/(1-a))| ≤ _
  rw [hnum, abs_mul, abs_neg, abs_of_pos (one_div_pos.mpr hq0), abs_div,
    abs_of_pos hden.1]
  calc
    _ = ((1/pC n m)*(1/(1-a)))*
        |dot X (nu1 P m S)+dot X (nu3 P m S)+a*dot X (N P m)| := by ring
    _ ≤ (2/c)*(|dot X (nu1 P m S)|+|dot X (nu3 P m S)|+|a*dot X (N P m)|) := by
      apply mul_le_mul hpref _ (abs_nonneg _) (by positivity)
      exact le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (2/c)*(2*H*r+2*H^2*r+(2*H*(K+1)/c)*r) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hA hB) hD) (by positivity)
    _ = _ := by
      dsimp only [r, t]
      have he : kappa P*((d : ℝ)/n) = kappa P*d/n := by ring
      rw [he]
      ring

/-- A single nonnegative envelope replaces a union bound for five events. -/
def GP005B3b_T25_energy {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  (1/((d : ℝ)/n))*dot (xMean P S) (xMean P S)+
    (1/kappa P)*dot (armNu1 P S P.yT) (armNu1 P S P.yT)+
    (1/kappa P)*dot (armNu1 P (control S) P.yC) (armNu1 P (control S) P.yC)+
    (mean S (centered P.yT))^2+(mean (control S) (centered P.yC))^2

lemma GP005B3b_T25_energy_nonneg {n d : ℕ} (P : Population n d) (m : ℕ)
    (ht : 0 < (d : ℝ)/n) (hκ : 0 < kappa P) (S : Finset (Fin n)) :
    0 ≤ GP005B3b_T25_energy P m S := by
  unfold GP005B3b_T25_energy
  have hV := GP005B3b_T25_dot_nonneg (xMean P S)
  have hT := GP005B3b_T25_dot_nonneg (armNu1 P S P.yT)
  have hC := GP005B3b_T25_dot_nonneg (armNu1 P (control S) P.yC)
  positivity

lemma GP005B3b_T25_energy_components {n d : ℕ} (P : Population n d) (m : ℕ)
    (ht : 0 < (d : ℝ)/n) (hκ : 0 < kappa P) (S : Finset (Fin n))
    {H : ℝ} (hZ : GP005B3b_T25_energy P m S ≤ H) :
    dot (xMean P S) (xMean P S) ≤ H*((d : ℝ)/n) ∧
    dot (armNu1 P S P.yT) (armNu1 P S P.yT) ≤ H*kappa P ∧
    dot (armNu1 P (control S) P.yC) (armNu1 P (control S) P.yC) ≤ H*kappa P ∧
    (mean S (centered P.yT))^2 ≤ H ∧ (mean (control S) (centered P.yC))^2 ≤ H := by
  have hV := mul_nonneg (le_of_lt (one_div_pos.mpr ht)) (GP005B3b_T25_dot_nonneg (xMean P S))
  have hT := mul_nonneg (le_of_lt (one_div_pos.mpr hκ)) (GP005B3b_T25_dot_nonneg (armNu1 P S P.yT))
  have hC := mul_nonneg (le_of_lt (one_div_pos.mpr hκ))
    (GP005B3b_T25_dot_nonneg (armNu1 P (control S) P.yC))
  have hYT := sq_nonneg (mean S (centered P.yT))
  have hYC := sq_nonneg (mean (control S) (centered P.yC))
  dsimp only [GP005B3b_T25_energy] at hZ
  refine ⟨?_, ?_, ?_, by linarith, by linarith⟩
  · apply (div_le_iff₀ ht).mp
    have hh : (1/((d : ℝ)/n))*dot (xMean P S) (xMean P S) ≤ H := by linarith
    simpa only [one_div_mul_eq_div] using hh
  · apply (div_le_iff₀ hκ).mp
    have hh : (1/kappa P)*dot (armNu1 P S P.yT) (armNu1 P S P.yT) ≤ H := by linarith
    simpa only [one_div_mul_eq_div] using hh
  · apply (div_le_iff₀ hκ).mp
    have hh : (1/kappa P)*dot (armNu1 P (control S) P.yC) (armNu1 P (control S) P.yC) ≤ H := by linarith
    simpa only [one_div_mul_eq_div] using hh

lemma GP005B3b_T25_energy_expectation {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (hd : 0 < d) (K : ℝ) (hK : 0 ≤ K)
    (hT : popMean (fun i => P.yT i^2) ≤ K) (hC : popMean (fun i => P.yC i^2) ≤ K)
    (c : ℝ) (hc : 0 < c) (hp : c ≤ pT n m) (hq : c ≤ pC n m) :
    expectation m (GP005B3b_T25_energy P m) ≤ 2/c+4*K/c+2*K := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : 0 < (d : ℝ)/n := div_pos hdR hnR
  have hκ : 0 < kappa P := lt_of_lt_of_le ht (kappa_bounds P (by omega) hP.2).1
  obtain ⟨hV, hU₁, hU₂, hY₁, hY₂⟩ :=
    GP005B3b_T25_energy_moments P hn hm hmn hP K hK hT hC c hc hp hq
  have hV' : (1/((d : ℝ)/n))*expectation m (fun S => dot (xMean P S) (xMean P S)) ≤ 2/c := by
    calc
      _ ≤ (1/((d : ℝ)/n))*((2/c)*((d : ℝ)/n)) :=
        mul_le_mul_of_nonneg_left hV (by positivity)
      _ = _ := by field_simp [ne_of_gt ht, ne_of_gt hκ] <;> ring
  have hU₁' : (1/kappa P)*expectation m
      (fun S => dot (armNu1 P S P.yT) (armNu1 P S P.yT)) ≤ 2*K/c := by
    calc
      _ ≤ (1/kappa P)*((2*K/c)*kappa P) := mul_le_mul_of_nonneg_left hU₁ (by positivity)
      _ = _ := by field_simp [ne_of_gt ht, ne_of_gt hκ] <;> ring
  have hU₂' : (1/kappa P)*expectation m
      (fun S => dot (armNu1 P (control S) P.yC) (armNu1 P (control S) P.yC)) ≤ 2*K/c := by
    calc
      _ ≤ (1/kappa P)*((2*K/c)*kappa P) := mul_le_mul_of_nonneg_left hU₂ (by positivity)
      _ = _ := by field_simp [ne_of_gt ht, ne_of_gt hκ] <;> ring
  change expectation m (fun S =>
    (1/((d : ℝ)/n))*dot (xMean P S) (xMean P S)+
    (1/kappa P)*dot (armNu1 P S P.yT) (armNu1 P S P.yT)+
    (1/kappa P)*dot (armNu1 P (control S) P.yC) (armNu1 P (control S) P.yC)+
    (mean S (centered P.yT))^2+(mean (control S) (centered P.yC))^2) ≤ _
  simp only [GP005B3b_T21_expectation_add, expectation_mul]
  calc
    _ ≤ 2/c+2*K/c+2*K/c+K+K :=
      add_le_add (add_le_add (add_le_add (add_le_add hV' hU₁') hU₂') hY₁) hY₂
    _ = _ := by ring

/-- A finite-sum Markov bound controls one envelope for the five required moments. -/
theorem noninteracted_stochastic_expansion_proof (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) (h : standingAssumptions d m P)
    (hinv : ∀ᶠ n in atTop, noninteractedRegular (P n) (m n))
    (hd : Tendsto (fun n => (d n : ℝ)/n) atTop (nhds 0)) :
    stochasticO m (fun n S => adjustedATE (P n) (m n) S - ate (P n) - commonLeading (P n) (m n) S)
      (fun n => Real.sqrt (kappa (P n)*(d n)/n)) := by
  rcases h with ⟨hsize, ⟨K, hK, hY⟩, hstd, ⟨lo, hi, hlo, hlohi, hhi, halloc⟩⟩
  let c : ℝ := min lo (1-hi)
  have hc : 0 < c := lt_min hlo (by linarith)
  have hc1 : c ≤ 1 := le_trans (min_le_left _ _) (by linarith)
  have halloc' : ∀ n, 3 ≤ n → c ≤ pT n (m n) ∧ c ≤ pC n (m n) := by
    intro n hn
    have hh := halloc n hn
    have hpq := GP005B3b_T25_allocation (m := m n) (by omega : 0 < n)
    constructor
    · exact le_trans (min_le_left _ _) (le_of_lt hh.1)
    · have hh' : c ≤ 1-hi := min_le_right _ _
      linarith [hh.2]
  intro ε hε
  let B : ℝ := 2/c+4*K/c+2*K
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let H : ℝ := 1+(B+1)/ε
  have hH : 1 ≤ H := by
    have hh : 0 ≤ (B+1)/ε := by positivity
    dsimp only [H]
    linarith
  have hH0 : 0 < H := by linarith
  have hBH : B/H < ε := by
    apply (div_lt_iff₀ hH0).2
    have hmul : ε*H = ε+B+1 := by
      dsimp only [H]
      field_simp [ne_of_gt hε]
      <;> ring
    linarith
  let M : ℝ := (2/c)*(2*H+2*H^2+2*H*(K+1)/c)
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨M, hM, ?_⟩
  have hsmall : ∀ᶠ n in atTop, (d n : ℝ)/n < c/(2*H) :=
    hd.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < c/(2*H)))
  have htail : ∀ᶠ n in atTop,
      probability (m n) (fun S =>
        |adjustedATE (P n) (m n) S-ate (P n)-commonLeading (P n) (m n) S| >
          M*Real.sqrt (kappa (P n)*(d n)/n)) < ε := by
    filter_upwards [eventually_ge_atTop 3, hstd, hinv, hsmall] with n hn hP hreg hs
    obtain ⟨hdpos, hdle, hm, hmn⟩ := hsize n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hdR : (0 : ℝ) < d n := by exact_mod_cast (show 0 < d n by omega)
    have ht : 0 < (d n : ℝ)/n := div_pos hdR hnR
    have hκ : 0 < kappa (P n) := lt_of_lt_of_le ht (kappa_bounds (P n) (by omega) hP.2).1
    obtain ⟨hp, hq⟩ := halloc' n hn
    obtain ⟨hT, hC, hx⟩ := hY n hn
    have hHt : H*((d n : ℝ)/n) ≤ c/2 := by
      have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2*H)).mp hs
      nlinarith
    have hZexp : expectation (m n) (GP005B3b_T25_energy (P n) (m n)) ≤ B :=
      GP005B3b_T25_energy_expectation (P n) hn hm hmn hP (by omega) K hK hT hC c hc hp hq
    calc
      _ ≤ probability (m n) (fun S => H < GP005B3b_T25_energy (P n) (m n) S) := by
        apply GP005B3b_T25_probability_mono
        intro S hS hbad
        by_contra hnot
        have hZ : GP005B3b_T25_energy (P n) (m n) S ≤ H := le_of_not_gt hnot
        obtain ⟨hV, hU₁, hU₂, hY₁, hY₂⟩ := GP005B3b_T25_energy_components (P n) (m n) ht hκ S hZ
        have hV0 := GP005B3b_T25_dot_nonneg (xMean (P n) S)
        have hVsmall : dot (xMean (P n) S) (xMean (P n) S) ≤ c/2 := le_trans hV hHt
        have hV1 : dot (xMean (P n) S) (xMean (P n) S) ≤ 1 := by linarith
        have hp0 : 0 ≤ pT n (m n) := by dsimp only [pT]; positivity
        have hq0 : 0 < pC n (m n) := lt_of_lt_of_le hc hq
        have hpq := GP005B3b_T25_allocation (m := m n) (by omega : 0 < n)
        have hp1 : pT n (m n) ≤ 1 := by linarith
        have hratio : pT n (m n)/pC n (m n) ≤ 1/c := by
          exact le_trans (div_le_div_of_nonneg_right hp1 hq0.le)
            (one_div_le_one_div_of_le hc hq)
        have hgood : (pT n (m n)/pC n (m n))*
            dot (xMean (P n) S) (xMean (P n) S) ≤ 1/2 := by
          calc
            _ ≤ (1/c)*(c/2) := mul_le_mul hratio hVsmall hV0 (by positivity)
            _ = _ := by field_simp [ne_of_gt hc] <;> ring
        have hbound := GP005B3b_T25_pointwise_bound (P n) hn hm hmn hP K hK hT hC c H hc hH hq
          S hS (hreg S hS) hV hV1 hU₁ hU₂ hY₁ hY₂ hgood
        exact not_lt_of_ge hbound hbad
      _ ≤ expectation (m n) (GP005B3b_T25_energy (P n) (m n))/H :=
        GP005B3b_T25_markov _ (fun S _ => GP005B3b_T25_energy_nonneg (P n) (m n) ht hκ S) hH0
      _ ≤ B/H := div_le_div_of_nonneg_right hZexp hH0.le
      _ < ε := hBH
  exact Filter.eventually_atTop.mp htail

end

end AronowAudit.P005.Wave1
