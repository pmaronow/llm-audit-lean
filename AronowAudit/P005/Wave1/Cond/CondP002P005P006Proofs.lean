import AronowAudit.Literature.CondP002P005P006

/-!
Conditional covariance bound for P005-T2. The literature premise is the closed
`LeiDing2021QuadraticSampling` proposition.
-/

noncomputable section
open scoped BigOperators Matrix
open Finset Filter
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

namespace AronowAudit.P005.Wave1

open AronowAudit.Literature

lemma CondP002P005P006_expectation_sub {n : ℕ} (m : ℕ)
    (f g : Finset (Fin n) → ℝ) :
    expectation m (fun S => f S - g S) = expectation m f - expectation m g := by
  simp [expectation, Finset.sum_sub_distrib, sub_div]

lemma CondP002P005P006_variance_congr {n : ℕ} (m : ℕ)
    (f g : Finset (Fin n) → ℝ) (h : ∀ S ∈ design n m, f S = g S) :
    variance m f = variance m g := by
  unfold variance
  rw [expectation_congr m f g h]
  exact expectation_congr m _ _ (fun S hS => by rw [h S hS])

lemma CondP002P005P006_variance_mul {n : ℕ} (m : ℕ)
    (f : Finset (Fin n) → ℝ) (c : ℝ) :
    variance m (fun S => c * f S) = c^2 * variance m f := by
  unfold variance
  rw [expectation_mul]
  have hf : (fun S => (c * f S - c * expectation m f)^2) =
      (fun S => c^2 * (f S - expectation m f)^2) := by funext S; ring
  rw [hf, expectation_mul]

lemma CondP002P005P006_centered_mean {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    popMean (centered a) = 0 := by
  have hS : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  change mean univ (fun i => a i - popMean a) = 0
  rw [mean_sub, mean_const univ hS]
  exact sub_self _

lemma CondP002P005P006_centered_sum {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    (∑ i, centered a i) = 0 := by
  have h := CondP002P005P006_centered_mean hn a
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simpa [popMean, mean, hn0] using h

lemma CondP002P005P006_outer (n : ℕ) (u v : Fin n → ℝ) (S : Finset (Fin n)) :
    principalSum n (fun i j => u i * v j) S = (∑ i ∈ S, u i) * (∑ j ∈ S, v j) := by
  simp only [principalSum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

lemma CondP002P005P006_mean_product {n s : ℕ}
    (H : LeiDing2021QuadraticSampling) (hn : 4 ≤ n) (hs : 0 < s) (hsn : s ≤ n)
    (u v : Fin n → ℝ) (_hu : (∑ i, u i) = 0) (hv : (∑ i, v i) = 0) :
    expectation s (fun S => mean S u * mean S v) =
      ((n : ℝ) - s) / ((s : ℝ) * (n - 1)) * popMean (fun i => u i * v i) := by
  have hform : ∀ S ∈ design n s, mean S u * mean S v =
      (1 / (s : ℝ)^2) * principalSum n (fun i j => u i * v j) S := by
    intro S hS
    have hc := (Finset.mem_powersetCard.mp hS).2
    rw [CondP002P005P006_outer, mean, mean, hc]
    ring
  rw [expectation_congr s _ _ hform, expectation_mul]
  have he := (H n s hn hsn (fun i j => u i * v j)).1
  change expectation s (principalSum n (fun i j => u i * v j)) = _ at he
  have htotal : (∑ i, ∑ j, u i * v j) = 0 := by
    simp [← Finset.mul_sum, hv]
  rw [he, htotal]
  simp only [mul_zero, add_zero, popMean, mean, Finset.card_univ, Fintype.card_fin]
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have s0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have n1 : (n : ℝ) - 1 ≠ 0 := by
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp [n0, s0, n1]
  <;> ring

lemma CondP002P005P006_variance_mean {n s : ℕ}
    (H : LeiDing2021QuadraticSampling) (hn : 4 ≤ n) (hs : 0 < s) (hsn : s ≤ n)
    (a : Fin n → ℝ) :
    variance s (fun S => mean S a) =
      ((n : ℝ) - s) / ((s : ℝ) * (n - 1)) *
        popMean (fun i => (a i - popMean a)^2) := by
  have hn' : 0 < n := by omega
  unfold variance
  rw [mean_unbiased hn' hs hsn]
  have hf : ∀ S ∈ design n s, (mean S a - popMean a)^2 =
      mean S (centered a) * mean S (centered a) := by
    intro S hS
    have hc : S.card = s := (Finset.mem_powersetCard.mp hS).2
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    change (mean S a - popMean a)^2 =
      mean S (fun i => a i - popMean a) * mean S (fun i => a i - popMean a)
    rw [mean_sub, mean_const S hne, pow_two]
  rw [expectation_congr s _ _ hf,
    CondP002P005P006_mean_product H hn hs hsn _ _
      (CondP002P005P006_centered_sum hn' a) (CondP002P005P006_centered_sum hn' a)]
  simp only [centered, pow_two]

lemma CondP002P005P006_variance_product {n s : ℕ}
    (H : LeiDing2021QuadraticSampling) (hn : 4 ≤ n) (hs : 0 < s) (hsn : s ≤ n)
    (u v : Fin n → ℝ) (hu : (∑ i, u i) = 0) (hv : (∑ i, v i) = 0) :
    variance s (fun S => mean S u * mean S v) ≤
      ((n : ℝ) - s) * n / ((s : ℝ)^3 * (n - 1)) *
        popMean (fun i => u i^2) * popMean (fun i => v i^2) := by
  have hform : ∀ S ∈ design n s, mean S u * mean S v =
      (1 / (s : ℝ)^2) * principalSum n (fun i j => u i * v j) S := by
    intro S hS
    have hc := (Finset.mem_powersetCard.mp hS).2
    rw [CondP002P005P006_outer, mean, mean, hc]
    ring
  rw [CondP002P005P006_variance_congr s _ _ hform, CondP002P005P006_variance_mul]
  have he := (H n s hn hsn (fun i j => u i * v j)).2
    (fun i => by rw [← Finset.mul_sum, hv, mul_zero])
    (fun j => by rw [← Finset.sum_mul, hu, zero_mul])
  change variance s (principalSum n (fun i j => u i * v j)) ≤ _ at he
  have hfrob : (∑ i, ∑ j, (u i * v j)^2) = (∑ i, u i^2) * (∑ j, v j^2) := by
    simp only [mul_pow, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hfrob] at he
  calc
    _ ≤ (1 / (s : ℝ)^2)^2 *
        ((s : ℝ)*((n : ℝ)-s)/((n : ℝ)*((n : ℝ)-1)) *
          ((∑ i, u i^2) * (∑ j, v j^2))) :=
      mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := by
      simp only [popMean, mean, Finset.card_univ, Fintype.card_fin]
      have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have s0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
      have n1 : (n : ℝ) - 1 ≠ 0 := by
        have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      field_simp [n0, s0, n1]
      <;> ring


/-- The corrected finite-sample covariance identity and bound for a uniform arm. -/
lemma CondP002P005P006_covariance_treated {n s : ℕ}
    (H : LeiDing2021QuadraticSampling) (hn : 4 ≤ n) (hs : 0 < s) (hsn : s ≤ n)
    (a b : Fin n → ℝ) :
    expectation s (fun S => sampleCov S a b) =
      ((s : ℝ) - 1) * n / ((s : ℝ) * (n - 1)) * popCov a b ∧
    variance s (fun S => sampleCov S a b) ≤ covarianceBound s (centered a) (centered b) := by
  have hn' : 0 < n := by omega
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn'.ne'
  have s0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have n1 : (n : ℝ) - 1 ≠ 0 := by
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hloc : ∀ S ∈ design n s, sampleCov S a b =
      sampleCov S (centered a) (centered b) := by
    intro S hS
    have hc : S.card = s := (Finset.mem_powersetCard.mp hS).2
    exact (covariance_location_invariant S (Finset.card_pos.mp (by omega))
      a b (popMean a) (popMean b)).symm
  have hpop : popCov a b = popMean (fun i => centered a i * centered b i) := by
    have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn'⟩, mem_univ _⟩
    have hh := covariance_location_invariant univ hne a b (popMean a) (popMean b)
    change sampleCov univ (centered a) (centered b) = popCov a b at hh
    rw [← hh]
    change popMean (fun i => centered a i * centered b i) -
      popMean (centered a) * popMean (centered b) = _
    rw [CondP002P005P006_centered_mean hn', CondP002P005P006_centered_mean hn']
    ring
  constructor
  · rw [expectation_congr s _ _ hloc]
    change expectation s (fun S => mean S (fun i => centered a i * centered b i) -
      mean S (centered a) * mean S (centered b)) = _
    rw [CondP002P005P006_expectation_sub, mean_unbiased hn' hs hsn,
      CondP002P005P006_mean_product H hn hs hsn _ _
        (CondP002P005P006_centered_sum hn' a) (CondP002P005P006_centered_sum hn' b), hpop]
    field_simp [n0, s0, n1]
    <;> ring
  · rw [CondP002P005P006_variance_congr s _ _ hloc]
    exact le_trans (variance_difference_bound s
      (fun S => mean S (fun i => centered a i * centered b i))
      (fun S => mean S (centered a) * mean S (centered b))) (by
        rw [CondP002P005P006_variance_mean H hn hs hsn]
        have hv := CondP002P005P006_variance_product H hn hs hsn
          (centered a) (centered b) (CondP002P005P006_centered_sum hn' a)
          (CondP002P005P006_centered_sum hn' b)
        unfold covarianceBound
        convert add_le_add_left
          (mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 2))
          (2 * (((n : ℝ) - s) / ((s : ℝ) * (n - 1)) *
            popMean (fun i => (centered a i * centered b i -
              popMean (fun j => centered a j * centered b j))^2))) using 1 <;> ring)

/-- Complementation transports the treated design to the uniform control design. -/
lemma CondP002P005P006_expectation_control {n m : ℕ} (hm : m ≤ n)
    (f : Finset (Fin n) → ℝ) :
    expectation m (fun S => f (control S)) = expectation (n - m) f := by
  classical
  have hinv : ∀ S : Finset (Fin n), control (control S) = S := by
    intro S
    simp only [control, ← Finset.compl_eq_univ_sdiff, compl_compl]
  have hmem : ∀ {s : ℕ} (S : Finset (Fin n)), S ∈ design n s →
      control S ∈ design n (n - s) := by
    intro s S hS
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    simp only [control, Finset.card_sdiff_of_subset (Finset.subset_univ S),
      Finset.card_univ, Fintype.card_fin, (Finset.mem_powersetCard.mp hS).2]
  have hsum : (∑ S ∈ design n m, f (control S)) = ∑ S ∈ design n (n-m), f S := by
    apply Finset.sum_nbij' control control
    · exact fun S hS => hmem S hS
    · intro S hS
      simpa only [Nat.sub_sub_self hm] using hmem S hS
    · exact fun S _ => hinv S
    · exact fun S _ => hinv S
    · exact fun S _ => rfl
  unfold expectation
  rw [hsum]
  congr 1
  simp only [design, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    Nat.choose_symm hm]

lemma CondP002P005P006_variance_control {n m : ℕ} (hm : m ≤ n)
    (f : Finset (Fin n) → ℝ) :
    variance m (fun S => f (control S)) = variance (n - m) f := by
  unfold variance
  rw [CondP002P005P006_expectation_control hm]
  exact CondP002P005P006_expectation_control hm
    (fun S => (f S - expectation (n - m) f)^2)

/-- P005-T2, conditional on `LeiDing2021QuadraticSampling`. -/
theorem corrected_covariance_lemma_conditional :
    AronowAudit.P005.corrected_covariance_lemma_conditional_statement := by
  unfold AronowAudit.P005.corrected_covariance_lemma_conditional_statement
  intro H n m hn hm hmn t a b
  cases t with
  | treated =>
    exact CondP002P005P006_covariance_treated H hn hm hmn.le a b
  | control =>
    change expectation m (fun S => sampleCov (control S) a b) = _ ∧
      variance m (fun S => sampleCov (control S) a b) ≤ _
    rw [CondP002P005P006_expectation_control hmn.le (fun S => sampleCov S a b),
      CondP002P005P006_variance_control hmn.le (fun S => sampleCov S a b)]
    exact CondP002P005P006_covariance_treated (s := n - m) H hn (by omega) (by omega) a b

end AronowAudit.P005.Wave1
