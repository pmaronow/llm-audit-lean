import AronowAudit.P005.P005_Formalization

namespace AronowAudit.P005.Wave1

noncomputable section
open scoped BigOperators Matrix
open Finset Filter
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

/-!
Finite-sampling second and third moments and exact regression decompositions.
-/

lemma t13_E_add {n : ℕ} (m : ℕ) (f g : Finset (Fin n) → ℝ) :
    expectation m (fun S => f S + g S) = expectation m f + expectation m g := by
  simp only [expectation, Finset.sum_add_distrib, add_div]

lemma t13_E_sub {n : ℕ} (m : ℕ) (f g : Finset (Fin n) → ℝ) :
    expectation m (fun S => f S - g S) = expectation m f - expectation m g := by
  simp only [expectation, Finset.sum_sub_distrib, sub_div]

lemma t13_E_neg {n : ℕ} (m : ℕ) (f : Finset (Fin n) → ℝ) :
    expectation m (fun S => -f S) = -expectation m f := by
  simp only [expectation, Finset.sum_neg_distrib, neg_div]

lemma t13_E_right {n : ℕ} (m : ℕ) (f : Finset (Fin n) → ℝ) (r : ℝ) :
    expectation m (fun S => f S * r) = expectation m f * r := by
  simpa only [mul_comm] using expectation_mul m f r

lemma t13_E_sum {n : ℕ} {ι : Type*} (m : ℕ) (I : Finset ι)
    (f : ι → Finset (Fin n) → ℝ) :
    expectation m (fun S => ∑ i ∈ I, f i S) = ∑ i ∈ I, expectation m (f i) := by
  simp only [expectation, Finset.sum_div]
  exact Finset.sum_comm

lemma t13_control_card {n m : ℕ} {S : Finset (Fin n)} (hS : S ∈ design n m) :
    (control S).card = n - m := by
  have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
  rw [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  simp [hs]

lemma t13_control_control {n : ℕ} (S : Finset (Fin n)) : control (control S) = S := by
  ext i
  simp [control]

lemma t13_control_mem {n m : ℕ} {S : Finset (Fin n)} (hS : S ∈ design n m) :
    control S ∈ design n (n-m) := by
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, t13_control_card hS⟩

lemma t13_E_control {n m : ℕ} (hmn : m ≤ n) (f : Finset (Fin n) → ℝ) :
    expectation m (fun S => f (control S)) = expectation (n-m) f := by
  have hnm : n - (n-m) = m := by omega
  have hs : (∑ S ∈ design n m, f (control S)) = ∑ A ∈ design n (n-m), f A := by
    refine Finset.sum_bij (fun S _ => control S) (fun S hS => t13_control_mem hS) ?_ ?_ ?_
    · intro S hS T hT h
      simpa only [t13_control_control] using congrArg control h
    · intro A hA
      refine ⟨control A, ?_, t13_control_control A⟩
      simpa only [hnm] using t13_control_mem hA
    · intro S hS
      rfl
  have hcard : (design n m).card = (design n (n-m)).card := by
    refine Finset.card_bij (fun S _ => control S) (fun S hS => t13_control_mem hS) ?_ ?_
    · intro S hS T hT h
      simpa only [t13_control_control] using congrArg control h
    · intro A hA
      refine ⟨control A, ?_, t13_control_control A⟩
      simpa only [hnm] using t13_control_mem hA
  unfold expectation
  rw [hs, hcard]

lemma t13_choose_weight {n m : ℕ} (hmn : m ≤ n) (R : Finset (Fin n))
    (hR : R.card ≤ m) :
    expectation m (fun S => if R ⊆ S then 1 else 0) * (n.descFactorial R.card : ℝ) =
      (m.descFactorial R.card : ℝ) := by
  rw [inclusion_count R hR]
  have hC : (n.choose m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hmn)
  have hchoose : (n.choose m : ℝ) * (m.choose R.card : ℝ) =
      (n.choose R.card : ℝ) * ((n-R.card).choose (m-R.card) : ℝ) := by
    exact_mod_cast (Nat.choose_mul (n := n) hR)
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp [hC]
  nlinarith [congrArg (fun z : ℝ => (R.card.factorial : ℝ)*z) hchoose]

lemma t13_inclusion_impossible {n m : ℕ} (R : Finset (Fin n)) (hR : m < R.card) :
    expectation m (fun S => if R ⊆ S then 1 else 0) = 0 := by
  calc
    _ = expectation m (fun _ => 0) := by
      apply expectation_congr
      intro S hS
      have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
      have hnot : ¬R ⊆ S := by
        intro h
        have := Finset.card_le_card h
        omega
      simp only [if_neg hnot]
    _ = 0 := by simp [expectation]

lemma t13_pair_inclusion {n m : ℕ} (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n)
    (i j : Fin n) (hij : i ≠ j) :
    expectation m (fun S => indicator S i * indicator S j) =
      (m : ℝ)*(m-1)/((n : ℝ)*(n-1)) := by
  have hform : (fun S : Finset (Fin n) => indicator S i * indicator S j) =
      (fun S => if ({i,j} : Finset (Fin n)) ⊆ S then 1 else 0) := by
    funext S
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [indicator, hi, hj, Finset.insert_subset_iff, Finset.singleton_subset_iff]
  rw [hform]
  have hcard : ({i,j} : Finset (Fin n)).card = 2 := by simp [hij]
  by_cases hm2 : 2 ≤ m
  · have hw := t13_choose_weight (le_of_lt hmn) {i,j} (by simpa [hcard] using hm2)
    rw [hcard] at hw
    have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ)-1 ≠ 0 := by linarith
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
      Nat.cast_mul, Nat.cast_one, mul_one] at hw
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 1 ≤ m)] at hw
    apply (eq_div_iff (mul_ne_zero hn0 hn1)).mpr
    norm_num at hw
    nlinarith only [hw]
  · have hm1 : m = 1 := by omega
    rw [t13_inclusion_impossible {i,j} (by rw [hcard]; omega), hm1]
    norm_num

lemma t13_triple_inclusion {n m : ℕ} (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    expectation m (fun S => indicator S i * indicator S j * indicator S k) =
      (m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2)) := by
  have hform : (fun S : Finset (Fin n) => indicator S i * indicator S j * indicator S k) =
      (fun S => if ({i,j,k} : Finset (Fin n)) ⊆ S then 1 else 0) := by
    funext S
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> by_cases hk : k ∈ S <;>
      simp [indicator, hi, hj, hk, Finset.insert_subset_iff, Finset.singleton_subset_iff]
  rw [hform]
  have hcard : ({i,j,k} : Finset (Fin n)).card = 3 := by simp [hij, hik, hjk]
  by_cases hm3 : 3 ≤ m
  · have hw := t13_choose_weight (le_of_lt hmn) {i,j,k} (by simpa [hcard] using hm3)
    rw [hcard] at hw
    have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ)-1 ≠ 0 := by linarith
    have hn2 : (n : ℝ)-2 ≠ 0 := by linarith
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
      Nat.cast_mul, Nat.cast_one, mul_one] at hw
    rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 1 ≤ n),
      Nat.cast_sub (by omega : 2 ≤ m), Nat.cast_sub (by omega : 1 ≤ m)] at hw
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)).mpr
    norm_num at hw
    nlinarith only [hw]
  · rw [t13_inclusion_impossible {i,j,k} (by rw [hcard]; omega)]
    have hsmall : m = 1 ∨ m = 2 := by omega
    rcases hsmall with rfl | rfl <;> norm_num

/- The next two identities are deterministic finite-sum algebra. -/
lemma t13_pair_sum {n : ℕ} (a b c : Fin n → ℝ) :
    (∑ i, ∑ j ∈ univ.erase i, a i*b i*c j) =
      (∑ i, a i*b i)*(∑ j, c j) - ∑ i, a i*b i*c i := by
  simp_rw [← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ _), mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_mul]

lemma t13_dist_sum {n : ℕ} (a b c : Fin n → ℝ) :
    (∑ i, ∑ j ∈ univ.erase i, ∑ k ∈ (univ.erase i).erase j, a i*b j*c k) =
      (∑ i, a i)*(∑ j, b j)*(∑ k, c k) + 2*(∑ i, a i*b i*c i) -
        (∑ i, a i*b i)*(∑ i, c i) -
        (∑ i, a i*c i)*(∑ i, b i) -
        (∑ i, b i*c i)*(∑ i, a i) := by
  have hinner : (∑ i, ∑ j ∈ univ.erase i, ∑ k ∈ (univ.erase i).erase j, a i*b j*c k) =
      ∑ i, ∑ j ∈ univ.erase i, a i*b j*((∑ k, c k)-c i-c j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.mul_sum, Finset.sum_erase_eq_sub hj,
      Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  rw [hinner]
  have hterm (i : Fin n) :
      (∑ j ∈ univ.erase i, a i*b j*((∑ k, c k)-c i-c j)) =
        a i*(∑ j, b j)*(∑ k, c k) + 2*(a i*b i*c i) -
          (a i*b i)*(∑ k, c k) - (a i*c i)*(∑ j, b j) -
          a i*(∑ j, b j*c j) := by
    have hs (j : Fin n) : a i*b j*((∑ k, c k)-c i-c j) =
        (a i*((∑ k, c k)-c i))*b j-a i*(b j*c j) := by ring
    simp_rw [hs, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    ring
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  ring

lemma t13_triple_partition {n : ℕ} (S : Finset (Fin n)) (a b c : Fin n → ℝ) :
    (∑ i, indicator S i*a i)*(∑ i, indicator S i*b i)*(∑ i, indicator S i*c i) =
      (∑ i, indicator S i*a i*b i*c i) +
      (∑ i, ∑ j ∈ univ.erase i,
        indicator S i*indicator S j*(a i*b i*c j+a i*b j*c i+a j*b i*c i)) +
      distinctTriple S a b c := by
  have hD (i : Fin n) : indicator S i * indicator S i = indicator S i := by
    by_cases hi : i ∈ S <;> simp [indicator, hi]
  have hP := t13_pair_sum (fun i => indicator S i*a i)
    (fun i => indicator S i*b i) (fun i => indicator S i*c i)
  have hQ := t13_pair_sum (fun i => indicator S i*a i)
    (fun i => indicator S i*c i) (fun i => indicator S i*b i)
  have hR := t13_pair_sum (fun i => indicator S i*b i)
    (fun i => indicator S i*c i) (fun i => indicator S i*a i)
  have hT := t13_dist_sum (fun i => indicator S i*a i)
    (fun i => indicator S i*b i) (fun i => indicator S i*c i)
  have hdiag : (∑ i, (indicator S i*a i)*(indicator S i*b i)*(indicator S i*c i)) =
      ∑ i, indicator S i*a i*b i*c i := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = (indicator S i*indicator S i)*indicator S i*(a i*b i*c i) := by ring
      _ = _ := by rw [hD, hD]; ring
  have hdist : (∑ i, ∑ j ∈ univ.erase i, ∑ k ∈ (univ.erase i).erase j,
      (indicator S i*a i)*(indicator S j*b j)*(indicator S k*c k)) =
      distinctTriple S a b c := by
    unfold distinctTriple
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hpairs : (∑ i, ∑ j ∈ univ.erase i,
      indicator S i*indicator S j*(a i*b i*c j+a i*b j*c i+a j*b i*c i)) =
      (∑ i, ∑ j ∈ univ.erase i, (indicator S i*a i)*(indicator S i*b i)*(indicator S j*c j)) +
      (∑ i, ∑ j ∈ univ.erase i, (indicator S i*a i)*(indicator S i*c i)*(indicator S j*b j)) +
      (∑ i, ∑ j ∈ univ.erase i, (indicator S i*b i)*(indicator S i*c i)*(indicator S j*a j)) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have h := hD i
    calc
      _ = (indicator S i*indicator S i)*indicator S j*
          (a i*b i*c j+a i*b j*c i+a j*b i*c i) := by rw [h]
      _ = _ := by ring
  rw [hpairs, hP, hQ, hR]
  rw [hdist] at hT
  simp only [mul_assoc, mul_left_comm, mul_comm] at hT hdiag ⊢
  linarith [hT, hdiag]

lemma t13_repeated_E {n m : ℕ} (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n)
    (a b c : Fin n → ℝ) (hc : ∑ i, c i = 0) :
    expectation m (fun S => repeatedPair S a b c) =
      -((m : ℝ)*(m-1)/((n : ℝ)*(n-1))) * ∑ i, a i*b i*c i := by
  simp only [repeatedPair, expectation_sum, t13_E_sum, t13_E_right]
  have h : (∑ i, ∑ j ∈ univ.erase i,
      expectation m (fun S => indicator S i*indicator S j)*a i*b i*c j) =
      ((m : ℝ)*(m-1)/((n : ℝ)*(n-1))) *
        (∑ i, ∑ j ∈ univ.erase i, a i*b i*c j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [t13_pair_inclusion hn hm hmn i j (Finset.mem_erase.mp hj).1.symm]
    ring
  rw [h, t13_pair_sum, hc]
  ring

lemma t13_distinct_E {n m : ℕ} (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n)
    (a b c : Fin n → ℝ) (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0)
    (hc : ∑ i, c i = 0) :
    expectation m (fun S => distinctTriple S a b c) =
      (2*(m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2))) * ∑ i, a i*b i*c i := by
  simp only [distinctTriple, expectation_sum, t13_E_sum, t13_E_right]
  have h : (∑ i, ∑ j ∈ univ.erase i, ∑ k ∈ (univ.erase i).erase j,
      expectation m (fun S => indicator S i*indicator S j*indicator S k)*a i*b j*c k) =
      ((m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2))) *
        (∑ i, ∑ j ∈ univ.erase i, ∑ k ∈ (univ.erase i).erase j, a i*b j*c k) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    have hji := (Finset.mem_erase.mp hj).1
    have hkj := (Finset.mem_erase.mp hk).1
    have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    rw [t13_triple_inclusion hn hm hmn i j k hji.symm hki.symm hkj.symm]
    ring
  rw [h, t13_dist_sum, ha, hb, hc]
  ring

lemma t13_third_partition_E {n m : ℕ} (a b c : Fin n → ℝ) :
    expectation m (fun S => mean S a*mean S b*mean S c) =
      (1/(m : ℝ)^3)*(
        expectation m (fun S => ∑ i, indicator S i*a i*b i*c i) +
        expectation m (fun S => ∑ i, ∑ j ∈ univ.erase i,
          indicator S i*indicator S j*(a i*b i*c j+a i*b j*c i+a j*b i*c i)) +
        expectation m (fun S => distinctTriple S a b c)) := by
  have hp : expectation m (fun S => mean S a*mean S b*mean S c) =
      expectation m (fun S => (1/(m : ℝ)^3)*(
        (∑ i, indicator S i*a i*b i*c i) +
        (∑ i, ∑ j ∈ univ.erase i,
          indicator S i*indicator S j*(a i*b i*c j+a i*b j*c i+a j*b i*c i)) +
        distinctTriple S a b c)) := by
    apply expectation_congr
    intro S hS
    have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
    rw [← t13_triple_partition S a b c]
    simp only [mean, hs, indicator_sum]
    ring
  rw [hp, expectation_mul, t13_E_add, t13_E_add]

lemma t13_third_raw {n m : ℕ} (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n)
    (a b c : Fin n → ℝ) (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0)
    (hc : ∑ i, c i = 0) :
    expectation m (fun S => mean S a*mean S b*mean S c) =
      (1/(m : ℝ)^3) * ((m : ℝ)/n - 3*(m : ℝ)*(m-1)/((n : ℝ)*(n-1)) +
        2*(m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2))) * ∑ i, a i*b i*c i := by
  rw [t13_third_partition_E]
  have hdiag : expectation m (fun S => ∑ i, indicator S i*a i*b i*c i) =
      ((m : ℝ)/n)*∑ i, a i*b i*c i := by
    simp only [expectation_sum, t13_E_right, indicator_expectation (by omega : 0 < n) hm (le_of_lt hmn)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hpairs : expectation m (fun S => ∑ i, ∑ j ∈ univ.erase i,
      indicator S i*indicator S j*(a i*b i*c j+a i*b j*c i+a j*b i*c i)) =
      -3*((m : ℝ)*(m-1)/((n : ℝ)*(n-1)))*(∑ i, a i*b i*c i) := by
    have hpoint (S : Finset (Fin n)) :
        (∑ i, ∑ j ∈ univ.erase i,
          indicator S i*indicator S j*(a i*b i*c j+a i*b j*c i+a j*b i*c i)) =
        repeatedPair S a b c + repeatedPair S a c b + repeatedPair S b c a := by
      simp only [repeatedPair, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    simp_rw [hpoint]
    rw [t13_E_add, t13_E_add, t13_repeated_E hn hm hmn a b c hc,
      t13_repeated_E hn hm hmn a c b hb, t13_repeated_E hn hm hmn b c a ha]
    have h1 : (∑ i, a i*c i*b i) = ∑ i, a i*b i*c i := by
      apply Finset.sum_congr rfl; intro i hi; ring
    have h2 : (∑ i, b i*c i*a i) = ∑ i, a i*b i*c i := by
      apply Finset.sum_congr rfl; intro i hi; ring
    rw [h1, h2]
    ring
  rw [hdiag, hpairs, t13_distinct_E hn hm hmn a b c ha hb hc]
  ring

lemma t13_third {n m : ℕ} (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n)
    (a b c : Fin n → ℝ) (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0)
    (hc : ∑ i, c i = 0) :
    expectation m (fun S => mean S a*mean S b*mean S c) =
      NTTT n m * popMean (fun i => a i*b i*c i) := by
  rw [t13_third_raw hn hm hmn a b c ha hb hc, third_moment_coefficient n m hn hm]
  simp only [popMean, mean, Finset.card_univ, Fintype.card_fin]
  ring

lemma t13_complement_mean {n m : ℕ} (hmn : m < n) (c : Fin n → ℝ)
    (hc : ∑ i, c i = 0) (S : Finset (Fin n)) (hS : S ∈ design n m) :
    mean (control S) c = -((m : ℝ)/((n : ℝ)-m))*mean S c := by
  have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
  have hsum : (∑ i ∈ control S, c i) = -(∑ i ∈ S, c i) := by
    rw [control, Finset.sum_sdiff_eq_sub (Finset.subset_univ S), hc]
    ring
  rw [mean, t13_control_card hS, Nat.cast_sub (le_of_lt hmn), hsum]
  simp only [mean, hs]
  by_cases hm0 : m = 0
  · have hsempty : S = ∅ := Finset.card_eq_zero.mp (hs.trans hm0)
    simp [hsempty]
  · have hm0r : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    have hmnr : (m : ℝ) < n := by exact_mod_cast hmn
    have nc0 : (n : ℝ)-m ≠ 0 := by linarith
    field_simp [hm0r, nc0]
    <;> ring

lemma t13_mixed_third {n m : ℕ} (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n)
    (a b c : Fin n → ℝ) (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0)
    (hc : ∑ i, c i = 0) :
    expectation m (fun S => mean S a*mean S b*mean (control S) c) =
      NTTC n m * popMean (fun i => a i*b i*c i) := by
  have hp : expectation m (fun S => mean S a*mean S b*mean (control S) c) =
      -((m : ℝ)/((n : ℝ)-m))*expectation m (fun S => mean S a*mean S b*mean S c) := by
    rw [← expectation_mul]
    apply expectation_congr
    intro S hS
    rw [t13_complement_mean hmn c hc S hS]
    ring
  rw [hp, t13_third hn hm hmn a b c ha hb hc]
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnr : (m : ℝ) < n := by exact_mod_cast hmn
  have n1 : (n : ℝ)-1 ≠ 0 := by linarith
  have n2 : (n : ℝ)-2 ≠ 0 := by linarith
  have nc0 : (n : ℝ)-m ≠ 0 := by linarith
  unfold NTTT NTTC
  field_simp [n1, n2, ne_of_gt hmr, nc0]
  <;> ring

lemma t13_sum_centered {n : ℕ} (a : Fin n → ℝ) : ∑ i, centered a i = 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [centered, popMean, mean, Finset.card_univ, Fintype.card_fin,
      Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp [hn0]
    <;> ring

lemma t13_x_sum {n d : ℕ} (P : Population n d) (hx : xMean P univ = 0)
    (k : Fin d) : ∑ i, P.x i k = 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have h := congrArg (fun v : Fin d → ℝ => v k) hx
    simp only [xMean, mean, Finset.card_univ, Fintype.card_fin, Pi.zero_apply] at h
    exact (div_eq_zero_iff.mp h).resolve_right hn0

lemma t13_second {n m : ℕ} (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n)
    (a b : Fin n → ℝ) :
    expectation m (fun S => mean S a*mean S b) =
      ((n : ℝ)-m)/((m : ℝ)*(n-1))*popMean (fun i => a i*b i) +
        ((m : ℝ)-1)*n/((m : ℝ)*(n-1))*popMean a*popMean b := by
  have hpoint : ∀ S ∈ design n m,
      mean S a*mean S b = (1/(m : ℝ)^2)*(
        (∑ i, indicator S i*a i*b i) +
        ∑ i, ∑ j ∈ univ.erase i, indicator S i*indicator S j*a i*b j) := by
    intro S hS
    have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
    have hsplit : (∑ i, indicator S i*a i)*(∑ j, indicator S j*b j) =
        (∑ i, indicator S i*a i*b i) +
        ∑ i, ∑ j ∈ univ.erase i, indicator S i*indicator S j*a i*b j := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hid : indicator S i*indicator S i = indicator S i := by
        by_cases h : i ∈ S <;> simp [indicator, h]
      have hd : (indicator S i*a i)*(indicator S i*b i) = indicator S i*a i*b i := by
        calc
          _ = (indicator S i*indicator S i)*a i*b i := by ring
          _ = _ := by rw [hid]
      rw [← hd]
      have hh := Finset.add_sum_erase univ (fun j => (indicator S i*a i)*(indicator S j*b j))
        (Finset.mem_univ i)
      convert hh.symm using 1 <;>
        simp only [mul_assoc, mul_left_comm, mul_comm]
    rw [mean, mean, hs, ← indicator_sum S a, ← indicator_sum S b, ← hsplit]
    ring
  rw [expectation_congr m _ _ hpoint, expectation_mul, t13_E_add]
  have hdiag : expectation m (fun S => ∑ i, indicator S i*a i*b i) =
      ((m : ℝ)/n)*∑ i, a i*b i := by
    simp only [expectation_sum, t13_E_right,
      indicator_expectation (by omega : 0 < n) hm (le_of_lt hmn)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hoff : expectation m (fun S => ∑ i, ∑ j ∈ univ.erase i,
      indicator S i*indicator S j*a i*b j) =
      ((m : ℝ)*(m-1)/((n : ℝ)*(n-1))) *
        ((∑ i, a i)*(∑ j, b j)-∑ i, a i*b i) := by
    simp only [expectation_sum, t13_E_sum, t13_E_right]
    have h : (∑ i, ∑ j ∈ univ.erase i,
        expectation m (fun S => indicator S i*indicator S j)*a i*b j) =
        ((m : ℝ)*(m-1)/((n : ℝ)*(n-1))) *
          (∑ i, ∑ j ∈ univ.erase i, a i*b j) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [t13_pair_inclusion hn hm hmn i j (Finset.mem_erase.mp hj).1.symm]
      ring
    rw [h]
    congr 1
    simp only [← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ _),
      mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hdiag, hoff]
  simp only [popMean, mean, Finset.card_univ, Fintype.card_fin]
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have n0 : (n : ℝ) ≠ 0 := by linarith
  have n1 : (n : ℝ)-1 ≠ 0 := by linarith
  field_simp [n0, n1, ne_of_gt hmr]
  <;> ring

lemma t13_cov_E {n m : ℕ} (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n)
    (a b : Fin n → ℝ) :
    expectation m (fun S => sampleCov S a b) =
      ((m : ℝ)-1)*n/((m : ℝ)*(n-1))*popCov a b := by
  simp only [sampleCov]
  rw [t13_E_sub, mean_unbiased (by omega : 0 < n) hm (le_of_lt hmn),
    t13_second hn hm hmn]
  unfold popCov sampleCov
  change _ = _ * (popMean (fun i => a i*b i)-popMean a*popMean b)
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have n1 : (n : ℝ)-1 ≠ 0 := by linarith
  field_simp [n1, ne_of_gt hmr]
  <;> ring

lemma t13_cov_centered {n : ℕ} (a y : Fin n → ℝ) :
    popMean (fun i => a i*centered y i) = popCov a y := by
  have hf : (fun i => a i*centered y i) =
      (fun i => a i*y i-popMean y*a i) := by
    funext i
    unfold centered
    ring
  rw [hf]
  unfold popMean
  rw [mean_sub, mean_mul]
  unfold popCov sampleCov
  ring

lemma t13_nu1_E {n d m : ℕ} (P : Population n d) (hn : 3 ≤ n)
    (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0) (y : Fin n → ℝ) :
    expectation m (fun S => dot (xMean P S) (armNu1 P S y)) =
      ((n : ℝ)-m)/((m : ℝ)*(n-1))*leverageCov P y := by
  have hxk (k : Fin d) : popMean (fun i => P.x i k) = 0 := by
    simpa only [xMean, popMean, Pi.zero_apply] using congrArg (fun v : Fin d → ℝ => v k) hx
  have hk (k : Fin d) : expectation m (fun S =>
      mean S (fun i => P.x i k)*
        (mean S (fun i => centered y i*P.x i k)-popMean (fun i => centered y i*P.x i k))) =
      ((n : ℝ)-m)/((m : ℝ)*(n-1))*popMean (fun i => P.x i k*(centered y i*P.x i k)) := by
    simp_rw [mul_sub]
    rw [t13_E_sub, t13_E_right, mean_unbiased (by omega : 0 < n) hm (le_of_lt hmn),
      t13_second hn hm hmn, hxk]
    ring
  simp only [dot, xMean, armNu1, expectation_sum]
  simp_rw [hk]
  rw [← Finset.mul_sum, ← popMean_sum]
  congr 1
  change _ = popCov (leverage P) y
  rw [← t13_cov_centered (leverage P) y]
  apply congrArg popMean
  funext i
  simp only [leverage, dot, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma t13_square_third_E {n d m : ℕ} (P : Population n d) (hn : 3 ≤ n)
    (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0) (y : Fin n → ℝ) :
    expectation m (fun S => dot (xMean P S) (xMean P S)*mean S (centered y)) =
      NTTT n m*leverageCov P y := by
  simp only [dot, xMean, Finset.sum_mul, expectation_sum]
  simp_rw [t13_third hn hm hmn _ _ _ (t13_x_sum P hx _) (t13_x_sum P hx _)
    (t13_sum_centered y)]
  rw [← Finset.mul_sum, ← popMean_sum]
  congr 1
  change _ = popCov (leverage P) y
  rw [← t13_cov_centered (leverage P) y]
  apply congrArg popMean
  funext i
  simp only [leverage, dot, Finset.sum_mul]

lemma t13_nu3_E {n d m : ℕ} (P : Population n d) (hn : 3 ≤ n)
    (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0) (y : Fin n → ℝ) :
    expectation m (fun S => dot (xMean P S) (armNu3 P S y)) =
      -NTTT n m*leverageCov P y := by
  have hp (S : Finset (Fin n)) : dot (xMean P S) (armNu3 P S y) =
      -(dot (xMean P S) (xMean P S)*mean S (centered y)) := by
    simp only [dot, armNu3, Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [hp]
  rw [t13_E_neg, t13_square_third_E P hn hm hmn hx y]
  ring

lemma t13_dot_mean_E {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0)
    (v : Fin d → ℝ) : expectation m (fun S => dot (xMean P S) v) = 0 := by
  simp only [dot, xMean, expectation_sum, t13_E_right,
    mean_unbiased hn hm (le_of_lt hmn)]
  have hk (k : Fin d) : popMean (fun i => P.x i k) = 0 := by
    simpa only [xMean, popMean, Pi.zero_apply] using congrArg (fun v : Fin d → ℝ => v k) hx
  simp only [hk, zero_mul, Finset.sum_const_zero]

lemma t13_dot_add {d : ℕ} (u v w : Fin d → ℝ) :
    dot u (v+w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma t13_dot_smul_left {d : ℕ} (r : ℝ) (u v : Fin d → ℝ) :
    dot (r • u) v = r*dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

lemma t13_dot_smul_right {d : ℕ} (r : ℝ) (u v : Fin d → ℝ) :
    dot u (r • v) = r*dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring


theorem corrected_control_bias_estimator_proof {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (hinv : ∀ S ∈ design n m, (armL P (control S)).det ≠ 0) :
    expectation m (fun S =>
      (m : ℝ)/((n-2 : ℝ)*(n-m)) * sampleCov (control S) (leverage P) P.yC +
        dot (xMean P (control S)) (armNu2 P (control S) P.yC)) =
    expectation m (fun S => dot (xMean P (control S))
      (armNu1 P (control S) P.yC + armNu2 P (control S) P.yC + armNu3 P (control S) P.yC)) ∧
    expectation m (fun S => dot (xMean P (control S))
      (armNu1 P (control S) P.yC + armNu2 P (control S) P.yC + armNu3 P (control S) P.yC)) =
    expectation m (fun S => dot (xMean P (control S)) (armBetaHat P (control S) P.yC)) ∧
    (∀ S ∈ design n m, dot (xMean P (control S)) (armNu2 P (control S) P.yC) =
      dot (xMean P (control S)) (((armL P (control S))⁻¹-1) *ᵥ armN P (control S) P.yC)) ∧
    expectation m (fun S => dot (xMean P (control S)) (armNu1 P (control S) P.yC)) =
      (m : ℝ)/((n-1 : ℝ)*(n-m))*leverageCov P P.yC ∧
    expectation m (fun S => dot (xMean P (control S)) (armNu3 P (control S) P.yC)) =
      -NCCC n m*leverageCov P P.yC ∧
    expectation m (fun S => sampleCov (control S) (leverage P) P.yC) =
      ((n : ℝ)-m-1)*n/(((n : ℝ)-m)*(n-1))*leverageCov P P.yC ∧
    (m : ℝ)/((n-1 : ℝ)*(n-m))-NCCC n m =
      (m : ℝ)*n*((n : ℝ)-m-1)/((n-1 : ℝ)*(n-2)*(n-m)^2) ∧
    (m : ℝ)*n*((n : ℝ)-m-1)/((n-1 : ℝ)*(n-2)*(n-m)^2) =
      (m : ℝ)/((n-2 : ℝ)*(n-m))*(((n : ℝ)-m-1)*n/(((n : ℝ)-m)*(n-1))) := by
  have hnc : 0 < n-m := Nat.sub_pos_of_lt hmn
  have hcn : n-m < n := Nat.sub_lt (by omega) hm
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnr : (m : ℝ) < n := by exact_mod_cast hmn
  have n1 : (n : ℝ)-1 ≠ 0 := by linarith
  have n2 : (n : ℝ)-2 ≠ 0 := by linarith
  have nc0 : (n : ℝ)-m ≠ 0 := by linarith
  have hfirst : expectation m (fun S => dot (xMean P (control S))
      (armNu1 P (control S) P.yC)) =
      (m : ℝ)/((n-1 : ℝ)*(n-m))*leverageCov P P.yC := by
    rw [t13_E_control (le_of_lt hmn) (fun A => dot (xMean P A) (armNu1 P A P.yC)), t13_nu1_E P hn hnc hcn hP.1]
    simp only [Nat.cast_sub (le_of_lt hmn)]
    field_simp [n1, nc0]
    <;> ring
  have hthird : expectation m (fun S => dot (xMean P (control S))
      (armNu3 P (control S) P.yC)) = -NCCC n m*leverageCov P P.yC := by
    rw [t13_E_control (le_of_lt hmn) (fun A => dot (xMean P A) (armNu3 P A P.yC)), t13_nu3_E P hn hnc hcn hP.1]
    rfl
  have hcov : expectation m (fun S => sampleCov (control S) (leverage P) P.yC) =
      ((n : ℝ)-m-1)*n/(((n : ℝ)-m)*(n-1))*leverageCov P P.yC := by
    rw [t13_E_control (le_of_lt hmn) (fun A => sampleCov A (leverage P) P.yC), t13_cov_E hn hnc hcn]
    simp only [Nat.cast_sub (le_of_lt hmn), leverageCov]
  have hcoef1 : (m : ℝ)/((n-1 : ℝ)*(n-m))-NCCC n m =
      (m : ℝ)*n*((n : ℝ)-m-1)/((n-1 : ℝ)*(n-2)*(n-m)^2) := by
    unfold NCCC NTTT
    simp only [Nat.cast_sub (le_of_lt hmn)]
    field_simp [n1, n2, nc0]
    <;> ring
  have hcoef2 : (m : ℝ)*n*((n : ℝ)-m-1)/((n-1 : ℝ)*(n-2)*(n-m)^2) =
      (m : ℝ)/((n-2 : ℝ)*(n-m))*(((n : ℝ)-m-1)*n/(((n : ℝ)-m)*(n-1))) := by
    field_simp [n1, n2, nc0]
    <;> ring
  have hfixed : expectation m (fun S => dot (xMean P (control S))
      (populationSlope P P.yC)) = 0 := by
    rw [t13_E_control (le_of_lt hmn) (fun A => dot (xMean P A) (populationSlope P P.yC))]
    exact t13_dot_mean_E P (by omega) hnc hcn hP.1 _
  have hfull : expectation m (fun S => dot (xMean P (control S))
      (armBetaHat P (control S) P.yC)) =
      expectation m (fun S => dot (xMean P (control S))
        (armNu1 P (control S) P.yC + armNu2 P (control S) P.yC + armNu3 P (control S) P.yC)) := by
    have hp : expectation m (fun S => dot (xMean P (control S))
        (armBetaHat P (control S) P.yC)) =
        expectation m (fun S => dot (xMean P (control S))
          (populationSlope P P.yC + armNu1 P (control S) P.yC +
            armNu2 P (control S) P.yC + armNu3 P (control S) P.yC)) := by
      apply expectation_congr
      intro S hS
      have hcN : (control S).Nonempty := Finset.card_pos.mp (by
        rw [t13_control_card hS]; exact hnc)
      rw [arm_slope_decomposition P hP (control S) hcN P.yC (hinv S hS)]
    rw [hp]
    simp only [t13_dot_add, t13_E_add, hfixed, zero_add]
  refine ⟨?_, hfull.symm, ?_, hfirst, hthird, hcov, hcoef1, hcoef2⟩
  · simp only [t13_dot_add, t13_E_add, expectation_mul]
    rw [hfirst, hthird, hcov]
    have hcoef := hcoef1.trans hcoef2
    nlinarith [congrArg (fun r : ℝ => r*leverageCov P P.yC) hcoef]
  · intro S hS
    rfl

/-!
The noninteracted decomposition.
-/

lemma t14_mean_control_E {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m < n)
    (a : Fin n → ℝ) : expectation m (fun S => mean (control S) a) = popMean a := by
  rw [t13_E_control (le_of_lt hmn) (fun A => mean A a)]
  exact mean_unbiased hn (Nat.sub_pos_of_lt hmn) (by omega) a

lemma t14_W_fixed_E {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0)
    (v : Fin d → ℝ) :
    expectation m (fun S => dot (xMean P (control S)-xMean P S) v) = 0 := by
  have hp (S : Finset (Fin n)) : dot (xMean P (control S)-xMean P S) v =
      dot (xMean P (control S)) v-dot (xMean P S) v := by
    simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  simp_rw [hp]
  rw [t13_E_sub, t13_dot_mean_E P hn hm hmn hx,
    t13_E_control (le_of_lt hmn) (fun A => dot (xMean P A) v),
    t13_dot_mean_E P hn (Nat.sub_pos_of_lt hmn) (by omega) hx]
  ring

lemma t14_first {n d m : ℕ} (P : Population n d) (hn : 3 ≤ n)
    (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0) :
    expectation m (fun S => dot (xMean P (control S)-xMean P S) (nu1 P m S)) =
      (leverageCov P P.yC-leverageCov P P.yT)/(n-1 : ℝ) := by
  have hp : expectation m (fun S => dot (xMean P (control S)-xMean P S) (nu1 P m S)) =
      -(pT n m/pC n m)*expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT)) +
      (pC n m/pT n m)*expectation m (fun S =>
        dot (xMean P (control S)) (armNu1 P (control S) P.yC)) := by
    rw [← expectation_mul, ← expectation_mul, ← t13_E_add]
    apply expectation_congr
    intro S hS
    have hw := control_minus_treated_mean_identities P (by omega) hm hmn hx S hS
    unfold nu1
    rw [t13_dot_add]
    conv_lhs =>
      arg 1
      rw [hw.2, t13_dot_smul_left, t13_dot_smul_right]
    conv_lhs =>
      arg 2
      rw [hw.1, t13_dot_smul_left, t13_dot_smul_right]
    ring
  rw [hp, t13_nu1_E P hn hm hmn hx, t13_E_control (le_of_lt hmn) (fun A => dot (xMean P A) (armNu1 P A P.yC)),
    t13_nu1_E P hn (Nat.sub_pos_of_lt hmn) (by omega) hx]
  unfold pT pC
  simp only [Nat.cast_sub (le_of_lt hmn)]
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnr : (m : ℝ) < n := by exact_mod_cast hmn
  have n0 : (n : ℝ) ≠ 0 := by linarith
  have n1 : (n : ℝ)-1 ≠ 0 := by linarith
  have nc0 : (n : ℝ)-m ≠ 0 := by linarith
  field_simp [n0, n1, nc0, ne_of_gt hmr]
  <;> ring

lemma t14_third {n d m : ℕ} (P : Population n d) (hn : 3 ≤ n)
    (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0) :
    expectation m (fun S => dot (xMean P (control S)-xMean P S) (nu3 P m S)) =
      ((n : ℝ)-2*m)/((n-1 : ℝ)*(n-2 : ℝ)*m)*leverageCov P P.yT -
        (2*(m : ℝ)-n)/((n-1 : ℝ)*(n-2 : ℝ)*(n-m))*leverageCov P P.yC := by
  have hp : expectation m (fun S => dot (xMean P (control S)-xMean P S) (nu3 P m S)) =
      -(pT n m/pC n m)*expectation m (fun S => dot (xMean P S) (armNu3 P S P.yT)) +
      (pC n m/pT n m)*expectation m (fun S =>
        dot (xMean P (control S)) (armNu3 P (control S) P.yC)) := by
    rw [← expectation_mul, ← expectation_mul, ← t13_E_add]
    apply expectation_congr
    intro S hS
    have hw := control_minus_treated_mean_identities P (by omega) hm hmn hx S hS
    unfold nu3
    rw [t13_dot_add]
    conv_lhs =>
      arg 1
      rw [hw.2, t13_dot_smul_left, t13_dot_smul_right]
    conv_lhs =>
      arg 2
      rw [hw.1, t13_dot_smul_left, t13_dot_smul_right]
    ring
  rw [hp, t13_nu3_E P hn hm hmn hx, t13_E_control (le_of_lt hmn) (fun A => dot (xMean P A) (armNu3 P A P.yC)),
    t13_nu3_E P hn (Nat.sub_pos_of_lt hmn) (by omega) hx]
  unfold pT pC NTTT
  simp only [Nat.cast_sub (le_of_lt hmn)]
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnr : (m : ℝ) < n := by exact_mod_cast hmn
  have n0 : (n : ℝ) ≠ 0 := by linarith
  have n1 : (n : ℝ)-1 ≠ 0 := by linarith
  have n2 : (n : ℝ)-2 ≠ 0 := by linarith
  have nc0 : (n : ℝ)-m ≠ 0 := by linarith
  field_simp [n0, n1, n2, nc0, ne_of_gt hmr]
  <;> ring

lemma t14_cov_difference {n d : ℕ} (P : Population n d) :
    leverageCov P P.yC-leverageCov P P.yT =
      -popMean (fun i => (leverage P i-popMean (leverage P))*(P.yT i-P.yC i)) := by
  have hf : (fun i => (leverage P i-popMean (leverage P))*(P.yT i-P.yC i)) =
      (fun i => (leverage P i*P.yT i-leverage P i*P.yC i)-
        (popMean (leverage P)*P.yT i-popMean (leverage P)*P.yC i)) := by
    funext i
    ring
  rw [hf]
  unfold leverageCov popCov sampleCov popMean
  rw [mean_sub, mean_sub, mean_sub, mean_mul, mean_mul]
  ring


theorem noninteracted_exact_decomposition_proof {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (hinv : noninteractedRegular P m) :
    (∀ S ∈ design n m, betaHat P m S = N P m + nu1 P m S + nu2 P m S + nu3 P m S) ∧
    expectation m (adjustedATE P m) - ate P =
      expectation m (fun S => dot (xMean P (control S) - xMean P S)
        (nu1 P m S + nu2 P m S + nu3 P m S)) ∧
    expectation m (fun S => dot (xMean P (control S)-xMean P S) (nu1 P m S)) =
      (leverageCov P P.yC - leverageCov P P.yT) / (n-1 : ℝ) ∧
    (leverageCov P P.yC - leverageCov P P.yT) / (n-1 : ℝ) =
      -(1/(n-1 : ℝ)) * popMean (fun i => (leverage P i-popMean (leverage P))*(P.yT i-P.yC i)) ∧
    expectation m (fun S => dot (xMean P (control S)-xMean P S) (nu3 P m S)) =
      ((n : ℝ)-2*m)/((n-1 : ℝ)*(n-2 : ℝ)*m)*leverageCov P P.yT -
        (2*(m : ℝ)-n)/((n-1 : ℝ)*(n-2 : ℝ)*(n-m))*leverageCov P P.yC ∧
    ((∃ c : ℝ, ∀ i, P.yT i-P.yC i = c) →
      expectation m (fun S => dot (xMean P (control S)-xMean P S) (nu1 P m S)) = 0) ∧
    (m = n-m → expectation m (fun S => dot (xMean P (control S)-xMean P S) (nu3 P m S)) = 0) := by
  have hslope := noninteracted_slope_decomposition P hn hm hmn hP hinv
  have hfirst := t14_first P hn hm hmn hP.1
  have hthird := t14_third P hn hm hmn hP.1
  have hbias : expectation m (adjustedATE P m)-ate P =
      expectation m (fun S => dot (xMean P (control S)-xMean P S)
        (nu1 P m S+nu2 P m S+nu3 P m S)) := by
    have hp : expectation m (adjustedATE P m) = expectation m (fun S =>
        (mean S P.yT-mean (control S) P.yC) +
        dot (xMean P (control S)-xMean P S) (N P m) +
        dot (xMean P (control S)-xMean P S) (nu1 P m S+nu2 P m S+nu3 P m S)) := by
      apply expectation_congr
      intro S hS
      simp only [adjustedATE, hslope S hS, dot, Pi.add_apply, Pi.sub_apply,
        mul_add, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      ring
    rw [hp, t13_E_add, t13_E_add, t13_E_sub,
      mean_unbiased (by omega : 0 < n) hm (le_of_lt hmn),
      t14_mean_control_E (by omega : 0 < n) hm hmn,
      t14_W_fixed_E P (by omega) hm hmn hP.1]
    unfold ate
    ring
  refine ⟨hslope, hbias, hfirst, ?_, hthird, ?_, ?_⟩
  · rw [t14_cov_difference P]
    ring
  · rintro ⟨c, hc⟩
    rw [hfirst, t14_cov_difference P]
    have hz : popMean (fun i =>
        (leverage P i-popMean (leverage P))*(P.yT i-P.yC i)) = 0 := by
      simp_rw [hc]
      change popMean (fun i => centered (leverage P) i*c) = 0
      simp only [popMean, mean, ← Finset.sum_mul, t13_sum_centered, zero_mul, zero_div]
    rw [hz]
    simp
  · intro hbal
    rw [hthird]
    have hn2m : n = 2*m := by omega
    have hn2mr : (n : ℝ) = 2*(m : ℝ) := by exact_mod_cast hn2m
    have hz1 : (n : ℝ)-2*m = 0 := by linarith
    have hz2 : 2*(m : ℝ)-n = 0 := by linarith
    rw [hz1, hz2]
    simp

/-!
All nine exact third-moment identities.
-/


theorem corrected_third_moment_calculation_proof {n m : ℕ} (hn : 3 ≤ n)
    (hm : 0 < m) (hmn : m < n) (a b c : Fin n → ℝ)
    (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0) (hc : ∑ i, c i = 0) :
    (∀ i j : Fin n, i ≠ j → expectation m (fun S => indicator S i * indicator S j) =
      (m : ℝ)*(m-1)/((n : ℝ)*(n-1))) ∧
    (∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
      expectation m (fun S => indicator S i*indicator S j*indicator S k) =
        (m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2))) ∧
    expectation m (fun S => repeatedPair S a b c) =
      ∑ i, ∑ j ∈ univ.erase i,
        expectation m (fun S => indicator S i * indicator S j) * a i * b i * c j ∧
    expectation m (fun S => repeatedPair S a b c) =
      -(m : ℝ)*(m-1)/((n : ℝ)*(n-1)) * ∑ i, a i*b i*c i ∧
    expectation m (fun S => distinctTriple S a b c) =
      2*(m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2)) * ∑ i, a i*b i*c i ∧
    expectation m (fun S => mean S a*mean S b*mean S c) =
      (1/(m : ℝ)^3)*(
        expectation m (fun S => ∑ i, indicator S i*a i*b i*c i) +
        expectation m (fun S => ∑ i, ∑ j ∈ univ.erase i,
          indicator S i*indicator S j*(a i*b i*c j+a i*b j*c i+a j*b i*c i)) +
        expectation m (fun S => distinctTriple S a b c)) ∧
    expectation m (fun S => mean S a * mean S b * mean S c) =
      (1/(m : ℝ)^3) * ((m : ℝ)/n - 3*(m : ℝ)*(m-1)/((n : ℝ)*(n-1)) +
        2*(m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2))) * ∑ i, a i*b i*c i ∧
    expectation m (fun S => mean S a * mean S b * mean S c) =
      NTTT n m * popMean (fun i => a i*b i*c i) ∧
    expectation m (fun S => mean S a * mean S b * mean (control S) c) =
      NTTC n m * popMean (fun i => a i*b i*c i) := by
  refine ⟨t13_pair_inclusion hn hm hmn, t13_triple_inclusion hn hm hmn,
    ?_, ?_, t13_distinct_E hn hm hmn a b c ha hb hc,
    t13_third_partition_E a b c, t13_third_raw hn hm hmn a b c ha hb hc,
    t13_third hn hm hmn a b c ha hb hc, t13_mixed_third hn hm hmn a b c ha hb hc⟩
  · simp only [repeatedPair, expectation_sum, t13_E_sum, t13_E_right]
  · rw [t13_repeated_E hn hm hmn a b c hc]
    ring

end
end AronowAudit.P005.Wave1
