import AronowAudit.P005.Wave1.Gap.GP005B2
import AronowAudit.P005.Wave1.Gap.GP005B5

namespace AronowAudit.P005.Wave1

noncomputable section
open scoped BigOperators Matrix
open Finset Filter
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

lemma GP005B1b_markov {n : ℕ} (s : ℕ) (F : Finset (Fin n) → ℝ)
    (hF : ∀ S ∈ design n s, 0 ≤ F S) (u : ℝ) (hu : 0 < u) :
    probability s (fun S => u < F S) ≤ expectation s F / u := by
  classical
  have hsum : (((design n s).filter (fun S => u < F S)).card : ℝ) * u ≤
      ∑ S ∈ design n s, F S := by
    calc
      _ = ∑ S ∈ design n s, if u < F S then u else 0 := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro S hS
        by_cases hSu : u < F S
        · simpa only [if_pos hSu] using hSu.le
        · simpa only [if_neg hSu] using hF S hS
  apply (le_div_iff₀ hu).mpr
  change (((((design n s).filter (fun S => u < F S)).card : ℝ) /
    ((design n s).card : ℝ)) * u) ≤
      (∑ S ∈ design n s, F S) / ((design n s).card : ℝ)
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

def GP005B1b_fourthKernel {n : ℕ} (p : ℕ → ℝ) (i j k l : Fin n) : ℝ :=
  p 4 + (p 3 - p 4) *
        ((if i=j then 1 else 0) + (if i=k then 1 else 0) + (if i=l then 1 else 0) +
         (if j=k then 1 else 0) + (if j=l then 1 else 0) + (if k=l then 1 else 0)) +
      (p 2 - 3*p 3 + 2*p 4) *
        ((if i=j ∧ j=k then 1 else 0) + (if i=j ∧ j=l then 1 else 0) +
         (if i=k ∧ k=l then 1 else 0) + (if j=k ∧ k=l then 1 else 0)) +
      (p 2 - 2*p 3 + p 4) *
        ((if i=j ∧ k=l then 1 else 0) + (if i=k ∧ j=l then 1 else 0) +
         (if i=l ∧ j=k then 1 else 0)) +
      (p 1 - 7*p 2 + 12*p 3 - 6*p 4) * (if i=j ∧ j=k ∧ k=l then 1 else 0)

/-- Fourth inclusion moment, expressed through the lattice of equality patterns. -/
lemma GP005B1b_indicator_fourth {n s : ℕ} (hsn : s ≤ n) (i j k l : Fin n) :
    let p := fun r => (s.choose r : ℝ) / (n.choose r : ℝ)
    expectation s (fun S => indicator S i * indicator S j * indicator S k * indicator S l) =
      GP005B1b_fourthKernel p i j k l := by
  classical
  have hf : (fun S => indicator S i * indicator S j * indicator S k * indicator S l) =
      (fun S => if ({i,j,k,l} : Finset (Fin n)) ⊆ S then (1 : ℝ) else 0) := by
    funext S
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      by_cases hk : k ∈ S <;> by_cases hl : l ∈ S <;>
      simp [indicator, Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj, hk, hl]
  rw [hf, t4_inclusion_ratio hsn]
  dsimp only
  by_cases hij : i=j <;> by_cases hik : i=k <;> by_cases hil : i=l <;>
    by_cases hjk : j=k <;> by_cases hjl : j=l <;> by_cases hkl : k=l <;>
    simp_all [GP005B1b_fourthKernel] <;> ring


lemma GP005B1b_fourth_contraction {n : ℕ} (H : Fin n → Fin n → ℝ)
    (hrow : ∀ i, ∑ j, H i j = 0) (hsym : ∀ i j, H i j = H j i)
    (htrace : ∑ i, H i i = 0) (p : ℕ → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, H i j * H k l * GP005B1b_fourthKernel p i j k l) =
      (p 1 - 7*p 2 + 12*p 3 - 6*p 4) * (∑ i, (H i i)^2) +
      2*(p 2 - 2*p 3 + p 4) * (∑ i, ∑ j, (H i j)^2) := by
  classical
  have hcol : ∀ j, ∑ i, H i j = 0 := by
    intro j
    simp_rw [hsym _ j]
    exact hrow j
  have hd (c : ℝ) : (∑ i, ∑ j, H i j * (H j j * c)) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol, zero_mul, Finset.sum_const_zero]
  have hsquare (c : ℝ) : (∑ i, ∑ j, H i j * (H i j * c)) =
      c * (∑ i, ∑ j, (H i j)^2) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcross (c : ℝ) : (∑ i, ∑ j, H i j * (H j i * c)) =
      c * (∑ i, ∑ j, (H i j)^2) := by
    calc
      _ = ∑ i, ∑ j, H i j * (H i j * c) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hsym j i]
      _ = _ := hsquare c
  have hdsquare (c : ℝ) : (∑ i, H i i * (H i i * c)) =
      c * (∑ i, (H i i)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [GP005B1b_fourthKernel, mul_add, mul_ite, mul_zero, mul_one,
    ite_and, Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [mul_assoc, ← Finset.sum_mul, ← Finset.mul_sum, hrow, hcol, htrace,
    mul_zero, zero_mul, Finset.sum_const_zero]
  simp only [hd, hsquare, hcross, hdsquare]
  ring

lemma GP005B1b_N_decomposition {n d : ℕ} (P : Population n d)
    (hn : 0 < n) (hx : xMean P univ = 0)
    (S : Finset (Fin n)) (hS : S.Nonempty) (y : Fin n → ℝ) :
    armN P S y = populationSlope P y + armNu1 P S y + armNu3 P S y := by
  funext k
  have hxk : popMean (fun i => P.x i k) = 0 := congrFun hx k
  have hf : (fun i => centered y i * P.x i k) =
      (fun i => y i * P.x i k - popMean y * P.x i k) := by
    funext i
    dsimp [centered]
    ring
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  have hcent : mean S (centered y) = mean S y - popMean y := by
    change mean S (fun i => y i - popMean y) = _
    rw [mean_sub, mean_const S hS]
  simp only [armN, populationSlope, armNu1, armNu3, Pi.add_apply, hf, popMean,
    mean_sub, mean_mul, hcent, xMean] at hxk ⊢
  rw [hxk]
  ring

lemma GP005B1b_remainder_identity {n d s : ℕ} (P : Population n d)
    (hn : 0 < n) (hs : 0 < s) (hx : xMean P univ = 0)
    (S : Finset (Fin n)) (hS : S ∈ design n s) (y : Fin n → ℝ) :
    armDebiased P S y - (mean S y - dot (xMean P S) (populationSlope P y)) =
      -dot (xMean P S) (armNu1 P S y) - dot (xMean P S) (armNu3 P S y) +
        (((n : ℝ) - s) / ((n - 2 : ℝ) * s)) * sampleCov S (leverage P) y := by
  have hne : S.Nonempty := Finset.card_pos.mp (by rw [(Finset.mem_powersetCard.mp hS).2]; exact hs)
  rw [armDebiased, (Finset.mem_powersetCard.mp hS).2, GP005B1b_N_decomposition P hn hx S hne y]
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring


lemma GP005B1b_centered_remainder {n d s : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hs : 0 < s) (hsn : s < n) (hx : xMean P univ = 0)
    (y : Fin n → ℝ) (S : Finset (Fin n)) (hS : S ∈ design n s) :
    let Q := fun A => dot (xMean P A) (armNu1 P A y)
    let T := fun A => -dot (xMean P A) (armNu3 P A y)
    let C := fun A => sampleCov A (leverage P) y
    let w := ((n : ℝ) - s) / ((n - 2 : ℝ) * s)
    armDebiased P S y - (mean S y - dot (xMean P S) (populationSlope P y)) =
      -(Q S - expectation s Q) + (T S - expectation s T) + w * (C S - expectation s C) := by
  dsimp only
  rw [GP005B1b_remainder_identity P (by omega) hs hx S hS y,
    t13_E_neg, t13_nu1_E P hn hs hsn hx y,
    t13_nu3_E P hn hs hsn hx y, t13_cov_E hn hs hsn]
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have n1 : (n : ℝ)-1 ≠ 0 := by linarith
  have n2 : (n : ℝ)-2 ≠ 0 := by linarith
  dsimp only [NTTT, leverageCov]
  field_simp [n1, n2, ne_of_gt hs']
  <;> ring


lemma GP005B1b_quadratic_tracefree_second {n s : ℕ} (hsn : s ≤ n)
    (H : Fin n → Fin n → ℝ) (hrow : ∀ i, ∑ j, H i j = 0)
    (hsym : ∀ i j, H i j = H j i) (htrace : ∑ i, H i i = 0) :
    expectation s (fun S => (∑ i, ∑ j, H i j * indicator S i * indicator S j)^2) =
      let p := fun r => (s.choose r : ℝ)/(n.choose r : ℝ)
      (p 1-7*p 2+12*p 3-6*p 4)*(∑ i, (H i i)^2) +
        2*(p 2-2*p 3+p 4)*(∑ i, ∑ j, (H i j)^2) := by
  have hf (S : Finset (Fin n)) :
      (∑ i, ∑ j, H i j * indicator S i * indicator S j)^2 =
      ∑ i, ∑ j, ∑ k, ∑ l, (H i j * H k l) *
        (indicator S i * indicator S j * indicator S k * indicator S l) := by
    rw [pow_two]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [hf, expectation_sum, expectation_mul, GP005B1b_indicator_fourth hsn]
  exact GP005B1b_fourth_contraction H hrow hsym htrace _


/-- A coarse second-moment bound for the trace-zero kernel. -/
lemma GP005B1b_quadratic_tracefree_bound {n s : ℕ} (hsn : s ≤ n)
    (H : Fin n → Fin n → ℝ) (hrow : ∀ i, ∑ j, H i j = 0)
    (hsym : ∀ i j, H i j = H j i) (htrace : ∑ i, H i i = 0) :
    expectation s (fun S => (∑ i, ∑ j, H i j * indicator S i * indicator S j)^2) ≤
      17 * (∑ i, ∑ j, (H i j)^2) := by
  classical
  let p := fun r => (s.choose r : ℝ)/(n.choose r : ℝ)
  have hp0 (r : ℕ) : 0 ≤ p r := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hp1 (r : ℕ) : p r ≤ 1 := by
    by_cases hz : n.choose r = 0
    · simp only [p, hz, Nat.cast_zero, div_zero, zero_le_one]
    · have hpos : (0 : ℝ) < n.choose r := by exact_mod_cast (Nat.pos_of_ne_zero hz)
      apply (div_le_one₀ hpos).mpr
      exact_mod_cast Nat.choose_le_choose r hsn
  let D := ∑ i, (H i i)^2
  let F := ∑ i, ∑ j, (H i j)^2
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hF : 0 ≤ F := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hDF : D ≤ F := by
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (fun j _ => sq_nonneg (H i j)) (Finset.mem_univ i)
  have ha : p 1 - 7*p 2 + 12*p 3 - 6*p 4 ≤ 13 := by
    linarith [hp0 2, hp0 4, hp1 1, hp1 3]
  have hb : p 2 - 2*p 3 + p 4 ≤ 2 := by
    linarith [hp1 2, hp0 3, hp1 4]
  calc
    _ = (p 1 - 7*p 2 + 12*p 3 - 6*p 4)*D + 2*(p 2 - 2*p 3+p 4)*F :=
      GP005B1b_quadratic_tracefree_second hsn H hrow hsym htrace
    _ ≤ 13*D + 4*F := add_le_add (mul_le_mul_of_nonneg_right ha hD)
      (mul_le_mul_of_nonneg_right (by linarith : 2*(p 2-2*p 3+p 4) ≤ 4) hF)
    _ ≤ 17*F := by linarith


/-- Matrix of the orthogonal projection onto the constants' orthogonal complement. -/
def GP005B1b_projection (n : ℕ) (i j : Fin n) : ℝ :=
  (if i = j then 1 else 0) - 1 / n

lemma GP005B1b_projection_sums {n : ℕ} (hn : 1 < n) :
    (∀ i, ∑ j, GP005B1b_projection n i j = 0) ∧
    (∑ i, GP005B1b_projection n i i) = (n : ℝ) - 1 ∧
    (∑ i, ∑ j, (GP005B1b_projection n i j)^2) = (n : ℝ) - 1 := by
  classical
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hN : (∑ _i : Fin n, (1 : ℝ)) = n := by simp
  have he (i j : Fin n) : (GP005B1b_projection n i j)^2 =
      (if i = j then 1 - 2/(n : ℝ) else 0) + (1/(n : ℝ))^2 := by
    by_cases h : i = j <;> simp only [GP005B1b_projection, h, ite_true, ite_false] <;> ring
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp [GP005B1b_projection, Finset.sum_sub_distrib, n0]
  · simp [GP005B1b_projection, Finset.sum_sub_distrib, n0]
  · simp_rw [he, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    <;> ring

lemma GP005B1b_projection_cross {n : ℕ} (H : Fin n → Fin n → ℝ)
    (hrow : ∀ i, ∑ j, H i j = 0) :
    (∑ i, ∑ j, H i j * GP005B1b_projection n i j) = ∑ i, H i i := by
  classical
  simp only [GP005B1b_projection, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    ← Finset.sum_mul, hrow, zero_mul, Finset.sum_const_zero, sub_zero]

lemma GP005B1b_projection_quad {n s : ℕ} (hn : 1 < n)
    (S : Finset (Fin n)) (hS : S ∈ design n s) :
    (∑ i, ∑ j, GP005B1b_projection n i j * indicator S i * indicator S j) =
      (s : ℝ) - (s : ℝ)^2 / n := by
  classical
  have hcard : S.card = s := (Finset.mem_powersetCard.mp hS).2
  have hsum : (∑ i, indicator S i) = (s : ℝ) := by
    simpa only [mul_one, Finset.sum_const, nsmul_eq_mul, hcard, mul_one] using
      indicator_sum S (fun _ => (1 : ℝ))
  have hid (i : Fin n) : indicator S i * indicator S i = indicator S i := by
    by_cases hi : i ∈ S <;> simp [indicator, hi]
  have he (i j : Fin n) : GP005B1b_projection n i j * indicator S i * indicator S j =
      (if i = j then indicator S i else 0) - (1/(n : ℝ))*indicator S i*indicator S j := by
    by_cases h : i = j
    · subst j; simp only [GP005B1b_projection, ite_true]; rw [sub_mul, sub_mul, one_mul, hid]
    · simp only [GP005B1b_projection, if_neg h]; ring
  simp_rw [he, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum,
    ← Finset.sum_mul, hsum]
  ring

/-- General centered fixed-size quadratic-form estimate, including nonzero trace. -/
lemma GP005B1b_quadratic_variance {n s : ℕ} (hn : 1 < n) (hsn : s ≤ n)
    (H : Fin n → Fin n → ℝ) (hrow : ∀ i, ∑ j, H i j = 0)
    (hsym : ∀ i j, H i j = H j i) :
    variance s (fun S => ∑ i, ∑ j, H i j * indicator S i * indicator S j) ≤
      17 * (∑ i, ∑ j, (H i j)^2) := by
  classical
  let tr := ∑ i, H i i
  let c := tr / ((n : ℝ) - 1)
  let K := fun i j => H i j - c * GP005B1b_projection n i j
  have n1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  obtain ⟨hpRow, hpTr, hpSq⟩ := GP005B1b_projection_sums hn
  have hKrow (i) : ∑ j, K i j = 0 := by
    simp only [K, Finset.sum_sub_distrib, ← Finset.mul_sum, hrow, hpRow, mul_zero, sub_self]
  have hKsym (i j) : K i j = K j i := by
    dsimp [K, GP005B1b_projection]
    rw [hsym i j]
    simp only [eq_comm]
  have hKtr : ∑ i, K i i = 0 := by
    simp only [K, Finset.sum_sub_distrib, ← Finset.mul_sum, hpTr]
    dsimp [c, tr]
    field_simp
    <;> ring
  have hKnorm : (∑ i, ∑ j, (K i j)^2) ≤ ∑ i, ∑ j, (H i j)^2 := by
    have hexp (i j) : (K i j)^2 = (H i j)^2 -
        2*c*(H i j * GP005B1b_projection n i j) + c^2*(GP005B1b_projection n i j)^2 := by
      dsimp [K]; ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.mul_sum, GP005B1b_projection_cross H hrow, hpSq]
    have hnon : 0 ≤ tr^2 / ((n : ℝ)-1) := div_nonneg (sq_nonneg _) (by
      have : (1 : ℝ) < n := by exact_mod_cast hn
      linarith)
    have heq : -2*c*tr+c^2*((n : ℝ)-1) = -(tr^2/((n : ℝ)-1)) := by
      dsimp [c]
      field_simp [n1]
      <;> ring
    change (∑ i, ∑ j, (H i j)^2) - 2*c*tr + c^2*((n : ℝ)-1) ≤ _
    nlinarith only [heq, hnon]
  let q := fun S => ∑ i, ∑ j, H i j * indicator S i * indicator S j
  let qK := fun S => ∑ i, ∑ j, K i j * indicator S i * indicator S j
  let b := c * ((s : ℝ) - (s : ℝ)^2/n)
  have heq (S) (hS : S ∈ design n s) : qK S = q S - b := by
    have he (i j) : K i j * indicator S i * indicator S j =
        H i j * indicator S i * indicator S j -
        c*(GP005B1b_projection n i j * indicator S i * indicator S j) := by
      dsimp [K]; ring
    dsimp only [qK, q]
    simp_rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [GP005B1b_projection_quad hn S hS]
  have hE : expectation s qK = expectation s q - b := by
    rw [expectation_congr s _ _ heq, t4_expectation_sub, t4_expectation_const hsn]
  have hV : variance s q = variance s qK := by
    unfold variance
    rw [hE]
    apply expectation_congr
    intro S hS
    rw [heq S hS]
    ring
  calc
    _ = variance s qK := hV
    _ ≤ expectation s (fun S => (qK S)^2) := t4_variance_le_second hsn qK
    _ ≤ 17 * (∑ i, ∑ j, (K i j)^2) :=
      GP005B1b_quadratic_tracefree_bound hsn K hKrow hKsym hKtr
    _ ≤ _ := mul_le_mul_of_nonneg_left hKnorm (by norm_num)

lemma GP005B1b_quadratic_variance_nonsym {n s : ℕ} (hn : 1 < n) (hsn : s ≤ n)
    (B : Fin n → Fin n → ℝ) (hrow : ∀ i, ∑ j, B i j = 0)
    (hcol : ∀ j, ∑ i, B i j = 0) :
    variance s (fun S => ∑ i, ∑ j, B i j * indicator S i * indicator S j) ≤
      17 * (∑ i, ∑ j, (B i j)^2) := by
  let H := fun i j => (B i j + B j i)/2
  have hHr (i) : ∑ j, H i j = 0 := by
    simp only [H, ← Finset.sum_div, Finset.sum_add_distrib, hrow, hcol, add_zero, zero_div]
  have hHs (i j) : H i j = H j i := by dsimp [H]; ring
  have hnorm : (∑ i, ∑ j, (H i j)^2) ≤ ∑ i, ∑ j, (B i j)^2 := by
    calc
      _ ≤ ∑ i, ∑ j, ((B i j)^2 + (B j i)^2)/2 := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        dsimp [H]
        nlinarith [sq_nonneg (B i j - B j i)]
      _ = _ := by
        simp only [← Finset.sum_div, Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j => (B j i)^2)]
        ring
  have hquad (S : Finset (Fin n)) :
      (∑ i, ∑ j, H i j * indicator S i * indicator S j) =
      (∑ i, ∑ j, B i j * indicator S i * indicator S j) := by
    have he (i j) : H i j * indicator S i * indicator S j =
        (B i j * indicator S i * indicator S j + B j i * indicator S j * indicator S i)/2 := by
      dsimp [H]; ring
    simp_rw [he, ← Finset.sum_div, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => B j i * indicator S j * indicator S i)]
    ring
  simpa only [hquad] using (GP005B1b_quadratic_variance hn hsn H hHr hHs).trans
    (mul_le_mul_of_nonneg_left hnorm (by norm_num))

lemma GP005B1b_expectation_cs {n s : ℕ} (f g : Finset (Fin n) → ℝ) :
    (expectation s (fun S => f S * g S))^2 ≤
      expectation s (fun S => (f S)^2) * expectation s (fun S => (g S)^2) := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (design n s) f g
  unfold expectation
  simpa only [div_pow, ← mul_div_mul_comm, ← pow_two] using
    div_le_div_of_nonneg_right hh (sq_nonneg ((design n s).card : ℝ))

lemma GP005B1b_abs_expectation_sq {n s : ℕ} (hsn : s ≤ n)
    (f : Finset (Fin n) → ℝ) :
    (expectation s (fun S => |f S|))^2 ≤ expectation s (fun S => (f S)^2) := by
  simpa only [mul_one, one_pow, sq_abs, t4_expectation_const hsn] using
    GP005B1b_expectation_cs (s := s) (fun S => |f S|) (fun _ => 1)

lemma GP005B1b_abs_centered {n s : ℕ} (hsn : s ≤ n) (f : Finset (Fin n) → ℝ) :
    expectation s (fun S => |f S - expectation s f|) ≤
      2 * expectation s (fun S => |f S|) := by
  have hE : |expectation s f| ≤ expectation s (fun S => |f S|) := by
    unfold expectation
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (design n s).card from Nat.cast_nonneg _)]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
  calc
    _ ≤ expectation s (fun S => |f S| + |expectation s f|) :=
      t4_expectation_mono _ _ (fun S _ => abs_sub _ _)
    _ = expectation s (fun S => |f S|) + |expectation s f| := by
      rw [t4_expectation_add, t4_expectation_const hsn]
    _ ≤ _ := by linarith

lemma GP005B1b_first_of_sq {x A r : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hr : 0 ≤ r)
    (h : x^2 ≤ A*r^2) : x ≤ (A+1)*r := by
  have hh : A ≤ (A+1)^2 := by nlinarith [sq_nonneg A]
  have hmul := mul_le_mul_of_nonneg_right hh (sq_nonneg r)
  have hpos : 0 ≤ (A+1)*r := mul_nonneg (by linarith) hr
  nlinarith [sq_nonneg (x+(A+1)*r)]

lemma GP005B1b_bilinear_means {n d s : ℕ} (a b : Fin n → Fin d → ℝ)
    (S : Finset (Fin n)) (hS : S ∈ design n s) :
    (∑ i, ∑ j, dot (a i) (b j) * indicator S i * indicator S j)/(s : ℝ)^2 =
      dot (fun k => mean S (fun i => a i k)) (fun k => mean S (fun j => b j k)) := by
  have hc : S.card = s := (Finset.mem_powersetCard.mp hS).2
  have hm (f : Fin n → ℝ) : mean S f = (∑ i, indicator S i*f i)/(s : ℝ) := by
    rw [indicator_sum, mean, hc]
  have he : (∑ i, ∑ j, dot (a i) (b j)*indicator S i*indicator S j) =
      ∑ k, (∑ i, indicator S i*a i k)*(∑ j, indicator S j*b j k) := by
    simp only [dot, Finset.sum_mul]
    calc
      _ = ∑ i, ∑ k, ∑ j, a i k*b j k*indicator S i*indicator S j := by
        apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring
  rw [he]
  simp only [dot, hm]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro k _; ring

/-- The quadratic term in the arm expansion. -/
lemma GP005B1b_arm_quadratic_variance {n d s : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hs : 0 < s) (hsn : s < n) (hP : standardized P)
    (y : Fin n → ℝ) (K : ℝ) (hY : popMean (fun i => y i^2) ≤ K) :
    variance s (fun S => dot (xMean P S) (armNu1 P S y)) ≤
      17 * ((n : ℝ)^3 * kappa P * K) / (s : ℝ)^4 := by
  classical
  let v := centered y
  let μ := populationSlope P v
  let B := fun i j => dot (P.x i) (fun k => P.x j k * v j - μ k)
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn0⟩, mem_univ _⟩
  have hb (i j) : B i j = dot (P.x i) (P.x j) * v j - dot (P.x i) μ := by
    simp only [B, dot, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl; intro k _; ring
  have hrow (i) : ∑ j, B i j = 0 := by
    simp_rw [hb, Finset.sum_sub_distrib]
    have he := dot_population_slope P (P.x i) v
    simp only [popMean, mean, Finset.card_univ, Fintype.card_fin] at he
    change dot (P.x i) μ = (∑ j, dot (P.x i) (P.x j)*v j)/(n : ℝ) at he
    have he' := (eq_div_iff (ne_of_gt hn')).mp he
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith only [he']
  have hcol (j) : ∑ i, B i j = 0 := by
    dsimp only [B, dot]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, t13_x_sum P hP.1, zero_mul, Finset.sum_const_zero]
  have hnorm : (∑ i, ∑ j, (B i j)^2) ≤ (n : ℝ)^3 * kappa P * K := by
    calc
      _ ≤ ∑ i, ∑ j, (dot (P.x i) (P.x j) * v j)^2 := by
        apply Finset.sum_le_sum; intro i _
        exact (corrected_contraction_chain P (by omega) hs hsn hP.2 v).1 i
      _ = (n : ℝ) * ∑ j, v j^2 * leverage P j := covariate_contraction P hn0 hP.2 v
      _ ≤ (n : ℝ) * ∑ j, v j^2 * ((n : ℝ)*kappa P) := by
        apply mul_le_mul_of_nonneg_left _ hn'.le
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (leverage_le_maximum P hn0 j) (sq_nonneg _)
      _ = (n : ℝ)^3 * kappa P * popMean (fun j => v j^2) := by
        simp only [popMean, mean, Finset.card_univ, Fintype.card_fin, ← Finset.sum_mul]
        field_simp <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((mean_square_centering univ hne y).2.trans hY) (by
          have : 0 ≤ kappa P := (kappa_bounds P hn0 hP.2).1.trans' (by positivity)
          positivity)
  have hquad (S) (hS : S ∈ design n s) :
      dot (xMean P S) (armNu1 P S y) =
        (∑ i, ∑ j, B i j * indicator S i * indicator S j) / (s : ℝ)^2 := by
    have hc : S.card = s := (Finset.mem_powersetCard.mp hS).2
    have hneS : S.Nonempty := Finset.card_pos.mp (by omega)
    rw [GP005B1b_bilinear_means P.x (fun j k => P.x j k*v j-μ k) S hS]
    unfold dot xMean armNu1
    apply Finset.sum_congr rfl; intro k _
    congr 1
    change mean S (fun i => centered y i * P.x i k) - popMean (fun i => centered y i * P.x i k) =
      mean S (fun j => P.x j k * v j - μ k)
    rw [mean_sub, mean_const S hneS]
    congr 1
    apply mean_congr; intro j _; exact mul_comm _ _
  have hV : variance s (fun S => dot (xMean P S) (armNu1 P S y)) =
      variance s (fun S => (∑ i, ∑ j, B i j * indicator S i * indicator S j)/(s : ℝ)^2) := by
    unfold variance
    rw [expectation_congr s _ _ hquad]
    apply expectation_congr; intro S hS
    dsimp only
    rw [hquad S hS]
  rw [hV, t4_variance_div]
  have hbound := (GP005B1b_quadratic_variance_nonsym (by omega) hsn.le B hrow hcol).trans
    (mul_le_mul_of_nonneg_left hnorm (by norm_num))
  convert div_le_div_of_nonneg_right hbound (sq_nonneg ((s : ℝ)^2)) using 1 <;> ring

lemma GP005B1b_xMean_moments {n d s : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hs : 0 < s) (hsn : s < n) (hP : standardized P) :
    expectation s (fun S => dot (xMean P S) (xMean P S)) =
      ((n : ℝ)-s)/((s : ℝ)*(n-1))*d ∧
    variance s (fun S => dot (xMean P S) (xMean P S)) ≤
      17*(n : ℝ)^2*d/(s : ℝ)^4 := by
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hmean : expectation s (fun S => dot (xMean P S) (xMean P S)) =
      ((n : ℝ)-s)/((s : ℝ)*(n-1))*d := by
    unfold dot xMean
    rw [expectation_sum]
    simp_rw [t13_second hn hs hsn, show ∀ k, popMean (fun i => P.x i k) = 0 from
      fun k => congrFun hP.1 k, mul_zero, add_zero, ← Finset.mul_sum]
    have he : (∑ k, popMean (fun i => P.x i k * P.x i k)) = (d : ℝ) := by
      rw [← leverage_population_mean P hP.2]
      simp only [popMean, leverage, dot, mean, Finset.sum_div]
      exact Finset.sum_comm
    rw [he]
  refine ⟨hmean, ?_⟩
  let H := fun i j => dot (P.x i) (P.x j)
  have hr (i) : ∑ j, H i j = 0 := by
    dsimp only [H, dot]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, t13_x_sum P hP.1, mul_zero, Finset.sum_const_zero]
  have hsym (i j) : H i j = H j i := dot_comm _ _
  have hnorm : (∑ i, ∑ j, (H i j)^2) = (n : ℝ)^2*d := by
    have hh := covariate_contraction P hn0 hP.2 (fun _ => 1)
    simp only [mul_one, one_pow, one_mul] at hh
    have hm := leverage_population_mean P hP.2
    simp only [popMean, mean, Finset.card_univ, Fintype.card_fin] at hm
    change (∑ i, leverage P i)/(n : ℝ) = (d : ℝ) at hm
    have hm' := (div_eq_iff (ne_of_gt hn')).mp hm
    dsimp only [H]
    rw [hh, hm']
    ring
  have he (S) (hS : S ∈ design n s) : dot (xMean P S) (xMean P S) =
      (∑ i, ∑ j, H i j * indicator S i * indicator S j)/(s : ℝ)^2 :=
    (GP005B1b_bilinear_means P.x P.x S hS).symm
  have hV : variance s (fun S => dot (xMean P S) (xMean P S)) =
      variance s (fun S => (∑ i, ∑ j, H i j * indicator S i * indicator S j)/(s : ℝ)^2) := by
    unfold variance
    rw [expectation_congr s _ _ he]
    apply expectation_congr; intro S hS
    dsimp only
    rw [he S hS]
  rw [hV, t4_variance_div]
  have hb := GP005B1b_quadratic_variance (by omega) hsn.le H hr hsym
  rw [hnorm] at hb
  convert div_le_div_of_nonneg_right hb (sq_nonneg ((s : ℝ)^2)) using 1 <;> ring

lemma GP005B1b_allocation_bounds (N s L : ℝ) (hN : 3 ≤ N) (hs : 0 < s)
    (hsN : s ≤ N) (hL : 1 ≤ L) (hNs : N/s ≤ L) :
    0 ≤ (N-s)/(s*(N-1)) ∧ (N-s)/(s*(N-1)) ≤ 2*L/N ∧
    0 ≤ (N-s)/((N-2)*s) ∧ (N-s)/((N-2)*s) ≤ 3*L/N := by
  have hN0 : 0 < N := by linarith
  have hNs0 : 0 ≤ N-s := sub_nonneg.mpr hsN
  have hNm1 : 0 < N-1 := by linarith
  have hNm2 : 0 < N-2 := by linarith
  have hI : 1/s ≤ L/N := (div_le_div_iff₀ hs hN0).mpr (by
    have := (div_le_iff₀ hs).mp hNs; nlinarith)
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · calc
      _ ≤ 2/s := (div_le_div_iff₀ (by positivity) hs).mpr (by nlinarith)
      _ ≤ _ := by simpa only [← mul_div_assoc, mul_one] using mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 2)
  · calc
      _ ≤ 3/s := (div_le_div_iff₀ (by positivity) hs).mpr (by nlinarith)
      _ ≤ _ := by simpa only [← mul_div_assoc, mul_one] using mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 3)

/-- Uniform finite estimates for the three terms of the centered remainder. -/
lemma GP005B1b_finite_moments {n d s : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hd : 1 ≤ d) (hs : 0 < s) (hsn : s < n) (hP : standardized P)
    (y : Fin n → ℝ) (K L : ℝ) (hK : 0 ≤ K) (hL : 1 ≤ L)
    (hY : popMean (fun i => y i^2) ≤ K) (hNs : (n : ℝ)/s ≤ L) :
    let Q := fun S => dot (xMean P S) (armNu1 P S y)
    let T := fun S => -dot (xMean P S) (armNu3 P S y)
    let C := fun S => (((n : ℝ)-s)/((n-2 : ℝ)*s)) * sampleCov S (leverage P) y
    variance s Q ≤ (17*L^4*K) * (kappa P/n) ∧
    (expectation s (fun S => |T S|))^2 ≤
      (2*L*K*(17*L^4+4*L^2)) * (kappa P/n) ∧
    variance s C ≤ (72*L^3*K) * (kappa P/n) := by
  dsimp only
  have hn0 : 0 < n := by omega
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  have hsp : (0 : ℝ) < s := by exact_mod_cast hs
  have hsn' : (s : ℝ) ≤ n := by exact_mod_cast hsn.le
  have hdp : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hLp : 0 < L := by linarith
  have κb := kappa_bounds P hn0 hP.2
  have κ0 : 0 ≤ kappa P := (div_nonneg (Nat.cast_nonneg _) hnp.le).trans κb.1
  have hdk : (d : ℝ)^2/(n : ℝ)^2 ≤ kappa P := by
    have hfrac : 0 ≤ (d : ℝ)/n := by positivity
    have hfrac1 : (d : ℝ)/n ≤ 1 := κb.1.trans κb.2
    have hh := mul_le_mul κb.1 hfrac1 hfrac κ0
    nlinarith [show (d : ℝ)^2/(n : ℝ)^2 = ((d : ℝ)/n)^2 by rw [div_pow]]
  obtain ⟨hρ0, hρ, hw0, hw⟩ := GP005B1b_allocation_bounds (n : ℝ) (s : ℝ) L hn' hsp hsn' hL hNs
  have hq : variance s (fun S => dot (xMean P S) (armNu1 P S y)) ≤
      (17*L^4*K)*(kappa P/n) := by
    calc
      _ ≤ 17*((n : ℝ)^3*kappa P*K)/(s : ℝ)^4 :=
        GP005B1b_arm_quadratic_variance P hn hs hsn hP y K hY
      _ = 17*((n : ℝ)/s)^4*K*(kappa P/n) := by field_simp <;> ring
      _ ≤ _ := by gcongr
  have hX := GP005B1b_xMean_moments P hn hs hsn hP
  have hX4 : expectation s (fun S => (dot (xMean P S) (xMean P S))^2) ≤
      (17*L^4+4*L^2)*((d : ℝ)^2/(n : ℝ)^2) := by
    rw [t4_variance_eq hsn.le] at hX
    have hmean0 : 0 ≤ ((n : ℝ)-s)/((s : ℝ)*(n-1))*(d : ℝ) := by positivity
    have hmean : ((n : ℝ)-s)/((s : ℝ)*(n-1))*(d : ℝ) ≤ 2*L*(d : ℝ)/n := by
      simpa only [div_mul_eq_mul_div, mul_assoc] using mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg d)
    have hvar : 17*(n : ℝ)^2*d/(s : ℝ)^4 ≤ 17*L^4*((d : ℝ)^2/(n : ℝ)^2) := by
      calc
        _ = 17*((n : ℝ)/s)^4*(d : ℝ)/(n : ℝ)^2 := by field_simp <;> ring
        _ ≤ 17*L^4*((d : ℝ)^2/(n : ℝ)^2) := by
          have hd2 : (d : ℝ) ≤ (d : ℝ)^2 := by nlinarith
          rw [mul_div_assoc]
          gcongr
    have hmsq := pow_le_pow_left₀ hmean0 hmean 2
    rw [hX.1] at hX
    have heq : (2*L*(d : ℝ)/n)^2 = 4*L^2*((d : ℝ)^2/(n : ℝ)^2) := by ring
    nlinarith only [hX.2, hvar, hmsq, heq]
  have hYm : expectation s (fun S => (mean S (centered y))^2) ≤ 2*L*K/n := by
    have hy0 : popMean (centered y) = 0 := by
      change mean univ (fun i => y i - popMean y) = 0
      rw [mean_sub, mean_const univ ⟨⟨0, hn0⟩, mem_univ _⟩]
      exact sub_self _
    have hyK := (mean_square_centering univ ⟨⟨0, hn0⟩, mem_univ _⟩ y).2.trans hY
    calc
      _ ≤ ((n : ℝ)-s)/((s : ℝ)*(n-1))*popMean (fun i => centered y i^2) :=
        t4_centered_mean_second (by omega) hs hsn.le _ hy0
      _ ≤ (2*L/n)*K := mul_le_mul hρ hyK (by
        exact mean_nonneg univ _ (fun i _ => sq_nonneg _)) (by positivity)
      _ = _ := by ring
  have hT (S : Finset (Fin n)) : -dot (xMean P S) (armNu3 P S y) =
      mean S (centered y) * dot (xMean P S) (xMean P S) := by
    simp only [dot, armNu3, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  have ht : (expectation s (fun S => |-dot (xMean P S) (armNu3 P S y)|))^2 ≤
      (2*L*K*(17*L^4+4*L^2))*(kappa P/n) := by
    simp_rw [hT, abs_mul]
    have hh := GP005B1b_expectation_cs (s := s) (fun S => |mean S (centered y)|)
      (fun S => |dot (xMean P S) (xMean P S)|)
    simp only [sq_abs] at hh
    calc
      _ ≤ _ := hh
      _ ≤ (2*L*K/n)*((17*L^4+4*L^2)*((d : ℝ)^2/(n : ℝ)^2)) :=
        mul_le_mul hYm hX4 (t4_expectation_nonneg _ (fun _ _ => sq_nonneg _)) (by positivity)
      _ = (2*L*K*(17*L^4+4*L^2))*(((d : ℝ)^2/(n : ℝ)^2)/n) := by ring
      _ ≤ _ := by gcongr
  refine ⟨hq, ht, ?_⟩
  let w := ((n : ℝ)-s)/((n-2 : ℝ)*s)
  have hVscale : variance s (fun S => w*sampleCov S (leverage P) y) =
      w^2*variance s (fun S => sampleCov S (leverage P) y) := by
    unfold variance
    rw [expectation_mul]
    have he (S) : (w*sampleCov S (leverage P) y - w*expectation s (fun A => sampleCov A (leverage P) y))^2 =
        w^2*(sampleCov S (leverage P) y-expectation s (fun A => sampleCov A (leverage P) y))^2 := by ring
    simp_rw [he]
    rw [expectation_mul]
  change variance s (fun S => w*sampleCov S (leverage P) y) ≤ _
  rw [hVscale]
  have hw2 : w^2 ≤ (3*L/n)^2 := pow_le_pow_left₀ hw0 hw 2
  have hcov := t4_covariance_coarse P (by omega) hs hsn.le hP y K hK hY
  calc
    _ ≤ (3*L/n)^2 * (4*(((n : ℝ)-s)/((s : ℝ)*(n-1)))*(n : ℝ)^2*kappa P^2*K) :=
      mul_le_mul hw2 hcov (t4_variance_nonneg _ _) (sq_nonneg _)
    _ ≤ (3*L/n)^2 * (4*(2*L/n)*(n : ℝ)^2*kappa P^2*K) := by gcongr
    _ = (72*L^3*K)*(kappa P^2/n) := by field_simp <;> ring
    _ ≤ _ := by
      have hk2 : kappa P^2 ≤ kappa P := by nlinarith [κb.2]
      gcongr

lemma GP005B1b_remainder_first {n d s : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hd : 1 ≤ d) (hs : 0 < s) (hsn : s < n) (hP : standardized P)
    (y : Fin n → ℝ) (K L : ℝ) (hK : 0 ≤ K) (hL : 1 ≤ L)
    (hY : popMean (fun i => y i^2) ≤ K) (hNs : (n : ℝ)/s ≤ L) :
    expectation s (fun S => |armDebiased P S y -
      (mean S y-dot (xMean P S) (populationSlope P y))|) ≤
      ((17*L^4*K+1) + 2*(2*L*K*(17*L^4+4*L^2)+1) + (72*L^3*K+1)) *
        Real.sqrt (kappa P/n) := by
  have hLp : 0 < L := by linarith
  let Q := fun S => dot (xMean P S) (armNu1 P S y)
  let T := fun S => -dot (xMean P S) (armNu3 P S y)
  let w := ((n : ℝ)-s)/((n-2 : ℝ)*s)
  let C := fun S => w*sampleCov S (leverage P) y
  let r := Real.sqrt (kappa P/n)
  have κ0 : 0 ≤ kappa P := (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans
    (kappa_bounds P (by omega) hP.2).1
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = kappa P/n := Real.sq_sqrt (by positivity)
  obtain ⟨hQ, hT, hC⟩ := GP005B1b_finite_moments P hn hd hs hsn hP y K L hK hL hY hNs
  have hqa : expectation s (fun S => |Q S-expectation s Q|) ≤ (17*L^4*K+1)*r := by
    apply GP005B1b_first_of_sq (t4_expectation_nonneg _ (fun _ _ => abs_nonneg _)) (by positivity) hr
    rw [hr2]
    exact (GP005B1b_abs_expectation_sq hsn.le _).trans hQ
  have hta : expectation s (fun S => |T S-expectation s T|) ≤
      2*(2*L*K*(17*L^4+4*L^2)+1)*r := by
    have h := GP005B1b_first_of_sq (t4_expectation_nonneg (fun S => |T S|)
      (fun _ _ => abs_nonneg _)) (by positivity : 0 ≤ 2*L*K*(17*L^4+4*L^2)) hr
      (by rw [hr2]; exact hT)
    exact (GP005B1b_abs_centered hsn.le T).trans (by nlinarith only [h])
  have hca : expectation s (fun S => |C S-expectation s C|) ≤ (72*L^3*K+1)*r := by
    apply GP005B1b_first_of_sq (t4_expectation_nonneg _ (fun _ _ => abs_nonneg _)) (by positivity) hr
    rw [hr2]
    exact (GP005B1b_abs_expectation_sq hsn.le _).trans hC
  have he (S) (hS : S ∈ design n s) :
      armDebiased P S y-(mean S y-dot (xMean P S) (populationSlope P y)) =
        -(Q S-expectation s Q)+(T S-expectation s T)+(C S-expectation s C) := by
    rw [GP005B1b_centered_remainder P hn hs hsn hP.1 y S hS]
    dsimp only [C]
    rw [expectation_mul]
    dsimp only [Q, T, w]
    ring
  calc
    _ ≤ expectation s (fun S => |Q S-expectation s Q|+|T S-expectation s T|+|C S-expectation s C|) := by
      apply t4_expectation_mono; intro S hS
      rw [he S hS]
      calc
        _ ≤ |-(Q S-expectation s Q)+(T S-expectation s T)|+|C S-expectation s C| := abs_add_le _ _
        _ ≤ _ := by
          have hh := abs_add_le (-(Q S-expectation s Q)) (T S-expectation s T)
          rw [abs_neg] at hh
          linarith only [hh]
    _ = expectation s (fun S => |Q S-expectation s Q|) +
        expectation s (fun S => |T S-expectation s T|) +
        expectation s (fun S => |C S-expectation s C|) := by rw [t4_expectation_add, t4_expectation_add]
    _ ≤ _ := by dsimp only [r] at *; nlinarith only [hqa, hta, hca]

/-- The arm remainder has stochastic order √(κ/n) on the varying finite randomization spaces. -/
theorem corrected_arm_debiased_order_proof (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) (h : standingAssumptions d m P) (t : Arm) :
    stochasticO m (fun n S =>
      let A := armSet t S
      let y := if t = .treated then (P n).yT else (P n).yC
      armDebiased (P n) A y - (mean A y - dot (xMean (P n) A) (populationSlope (P n) y)))
      (fun n => Real.sqrt (kappa (P n)/n)) := by
  classical
  rcases h with ⟨hsize, ⟨K, hK, hym⟩, hstd, ⟨lo, hi, hlo, hlohi, hhi, halloc⟩⟩
  let a : ℝ := min lo (1-hi)
  have ha : 0 < a := lt_min hlo (sub_pos.mpr hhi)
  let L : ℝ := 1+1/a
  have hL : 1 ≤ L := by
    have ha0 : 0 ≤ 1/a := (one_div_pos.mpr ha).le
    dsimp [L]; linarith
  have hLp : 0 < L := by linarith
  let B : ℝ := ((17*L^4*K+1) + 2*(2*L*K*(17*L^4+4*L^2)+1) + (72*L^3*K+1))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨n₁, hstd⟩ := Filter.eventually_atTop.mp hstd
  intro ε hε
  let M : ℝ := (B+1)/ε+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hBM : B < ε*M := by
    have he : ε*((B+1)/ε) = B+1 := by field_simp <;> ring
    dsimp only [M]; nlinarith only [he, hε]
  refine ⟨M, hM, max 3 n₁, ?_⟩
  intro n hn
  have hn3 : 3 ≤ n := (le_max_left 3 n₁).trans hn
  have hn0 : 0 < n := by omega
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn0
  have hPn : standardized (P n) := hstd n ((le_max_right 3 n₁).trans hn)
  have hsz := hsize n hn3
  have hp := halloc n hn3
  let s := armSize n (m n) t
  let y := if t = .treated then (P n).yT else (P n).yC
  let F := fun (S : Finset (Fin n)) => armDebiased (P n) (armSet t S) y -
      (mean (armSet t S) y-dot (xMean (P n) (armSet t S)) (populationSlope (P n) y))
  have hs : 0 < s := by cases t <;> simp only [s, armSize] <;> omega
  have hsn : s < n := by cases t <;> simp only [s, armSize] <;> omega
  have hslo : a*(n : ℝ) ≤ s := by
    cases t with
    | treated =>
      change a*(n : ℝ) ≤ (m n : ℝ)
      have hlow : lo*(n : ℝ) < m n := (lt_div_iff₀ hnp).mp hp.1
      exact (mul_le_mul_of_nonneg_right (min_le_left lo (1-hi)) hnp.le).trans hlow.le
    | control =>
      change a*(n : ℝ) ≤ ((n-m n : ℕ) : ℝ)
      rw [Nat.cast_sub hsz.2.2.2.le]
      have hupp : (m n : ℝ) < hi*n := (div_lt_iff₀ hnp).mp hp.2
      have hmul := mul_le_mul_of_nonneg_right (min_le_right lo (1-hi)) hnp.le
      nlinarith
  have hNs : (n : ℝ)/s ≤ L := by
    have hsp : (0 : ℝ) < s := by exact_mod_cast hs
    have hb : (n : ℝ)/s ≤ 1/a := (div_le_div_iff₀ hsp ha).mpr (by nlinarith only [hslo])
    exact hb.trans (by dsimp [L]; linarith)
  have hY : popMean (fun i => y i^2) ≤ K := by
    cases t with
    | treated => exact (hym n hn3).1
    | control => exact (hym n hn3).2.1
  have hfirst : expectation (m n) (fun S => |F S|) ≤ B*Real.sqrt (kappa (P n)/n) := by
    have hh := GP005B1b_remainder_first (P n) hn3 hsz.1 hs hsn hPn y K L hK hL hY hNs
    cases t with
    | treated => exact hh
    | control =>
      change expectation (m n) (fun S => |armDebiased (P n) (control S) y -
        (mean (control S) y-dot (xMean (P n) (control S)) (populationSlope (P n) y))|) ≤ _
      rw [t4_complement_expectation hsz.2.2.2.le
        (fun S => |armDebiased (P n) S y-(mean S y-dot (xMean (P n) S) (populationSlope (P n) y))|)]
      exact hh
  have hκ : 0 < kappa (P n) := lt_of_lt_of_le
    (div_pos (by exact_mod_cast (by omega : 0 < d n)) hnp) (kappa_bounds (P n) hn0 hPn.2).1
  have hr : 0 < Real.sqrt (kappa (P n)/n) := Real.sqrt_pos.2 (div_pos hκ hnp)
  change probability (m n) (fun S => M*Real.sqrt (kappa (P n)/n) < |F S|) < ε
  calc
    _ ≤ expectation (m n) (fun S => |F S|)/(M*Real.sqrt (kappa (P n)/n)) :=
      GP005B1b_markov (m n) (fun S => |F S|) (fun _ _ => abs_nonneg _) _ (mul_pos hM hr)
    _ ≤ (B*Real.sqrt (kappa (P n)/n))/(M*Real.sqrt (kappa (P n)/n)) :=
      div_le_div_of_nonneg_right hfirst (mul_pos hM hr).le
    _ < ε := (div_lt_iff₀ (mul_pos hM hr)).mpr (by
      have hh := mul_lt_mul_of_pos_right hBM hr
      nlinarith only [hh])

end
end AronowAudit.P005.Wave1
