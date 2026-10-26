import AronowAudit.P005.P005_Formalization
import Mathlib.Data.Nat.Choose.Cast

namespace AronowAudit.P005.Wave1

noncomputable section
open scoped BigOperators Matrix
open Finset Filter
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

/-!
For P005-T4, a second-moment bound suffices for the big-O rate,
without a fourth-moment covariance bound.
-/

lemma t4_expectation_nonneg {n m : ℕ} (f : Finset (Fin n) → ℝ)
    (hf : ∀ S ∈ design n m, 0 ≤ f S) : 0 ≤ expectation m f := by
  exact div_nonneg (Finset.sum_nonneg hf) (Nat.cast_nonneg _)

lemma t4_expectation_mono {n m : ℕ} (f g : Finset (Fin n) → ℝ)
    (hf : ∀ S ∈ design n m, f S ≤ g S) : expectation m f ≤ expectation m g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum hf) (Nat.cast_nonneg _)

lemma t4_expectation_sub {n : ℕ} (m : ℕ) (f g : Finset (Fin n) → ℝ) :
    expectation m (fun S => f S - g S) = expectation m f - expectation m g := by
  simp only [expectation, Finset.sum_sub_distrib, sub_div]

lemma t4_expectation_add {n : ℕ} (m : ℕ) (f g : Finset (Fin n) → ℝ) :
    expectation m (fun S => f S + g S) = expectation m f + expectation m g := by
  simp only [expectation, Finset.sum_add_distrib, add_div]

lemma t4_expectation_const {n m : ℕ} (hmn : m ≤ n) (c : ℝ) :
    expectation (n := n) m (fun _ => c) = c := by
  have hcard : (0 : ℝ) < (design n m).card := by
    exact_mod_cast (show 0 < (design n m).card by
      simpa only [design, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin] using Nat.choose_pos hmn)
  simp only [expectation, Finset.sum_const, nsmul_eq_mul]
  field_simp [ne_of_gt hcard]

lemma t4_variance_nonneg {n : ℕ} (m : ℕ) (f : Finset (Fin n) → ℝ) :
    0 ≤ variance m f := t4_expectation_nonneg _ (fun _ _ => sq_nonneg _)

lemma t4_variance_eq {n m : ℕ} (hmn : m ≤ n) (f : Finset (Fin n) → ℝ) :
    variance m f = expectation m (fun S => f S ^ 2) - (expectation m f)^2 := by
  unfold variance
  have heq : (fun S => (f S - expectation m f)^2) =
      (fun S => f S^2 - 2 * expectation m f * f S + (expectation m f)^2) := by
    funext S
    ring
  rw [heq, t4_expectation_add, t4_expectation_sub, expectation_mul,
    t4_expectation_const hmn]
  ring

lemma t4_variance_le_second {n m : ℕ} (hmn : m ≤ n)
    (f : Finset (Fin n) → ℝ) :
    variance m f ≤ expectation m (fun S => f S^2) := by
  rw [t4_variance_eq hmn]
  exact sub_le_self _ (sq_nonneg _)

lemma t4_variance_div {n : ℕ} (m : ℕ) (f : Finset (Fin n) → ℝ) (c : ℝ) :
    variance m (fun S => f S / c) = variance m f / c^2 := by
  have he : expectation m (fun S => f S / c) = expectation m f / c := by
    simpa only [div_eq_mul_inv, mul_comm] using expectation_mul m f c⁻¹
  unfold variance
  rw [he]
  have hp : (fun S => (f S / c - expectation m f / c)^2) =
      (fun S => (c^2)⁻¹ * (f S - expectation m f)^2) := by
    funext S
    rw [← sub_div, div_pow]
    ring
  rw [hp, expectation_mul]
  ring

/-- The exact labelled inclusion probability, including sample sizes below |R|. -/
lemma t4_inclusion_ratio {n m : ℕ} (hmn : m ≤ n) (R : Finset (Fin n)) :
    expectation m (fun S => if R ⊆ S then 1 else 0) =
      (m.choose R.card : ℝ) / (n.choose R.card : ℝ) := by
  classical
  have hRn : R.card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ R)
  have hN : (n.choose m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hmn).ne'
  have hR : (n.choose R.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hRn).ne'
  by_cases hr : R.card ≤ m
  · rw [inclusion_count R hr]
    have hc : (n.choose m : ℝ) * (m.choose R.card : ℝ) =
        (n.choose R.card : ℝ) * ((n - R.card).choose (m - R.card) : ℝ) := by
      exact_mod_cast (Nat.choose_mul (n := n) hr)
    apply (div_eq_div_iff hN hR).mpr
    nlinarith only [hc]
  · have hz : expectation m (fun S => if R ⊆ S then (1 : ℝ) else 0) = 0 := by
      calc
        _ = expectation m (fun _ => 0) := by
          apply expectation_congr
          intro S hS
          have hSc : S.card = m := (Finset.mem_powersetCard.mp hS).2
          have hnot : ¬ R ⊆ S := by
            intro hs
            exact hr (hSc ▸ Finset.card_le_card hs)
          simp only [if_neg hnot]
        _ = 0 := by simp [expectation]
    rw [hz, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hr)]
    simp

lemma t4_pair_inclusion {n m : ℕ} (hn : 2 ≤ n) (hmn : m ≤ n)
    (i j : Fin n) (hij : i ≠ j) :
    expectation m (fun S => indicator S i * indicator S j) =
      (m : ℝ) * (m - 1) / ((n : ℝ) * (n - 1)) := by
  classical
  have hcard : ({i,j} : Finset (Fin n)).card = 2 := by simp [hij]
  have he : expectation m (fun S => indicator S i * indicator S j) =
      expectation m (fun S => if ({i,j} : Finset (Fin n)) ⊆ S then 1 else 0) := by
    apply expectation_congr
    intro S _
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [indicator, Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
  rw [he, t4_inclusion_ratio hmn, hcard,
    Nat.cast_choose_two ℝ, Nat.cast_choose_two ℝ]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have n0 : (n : ℝ) ≠ 0 := by linarith
  have n1 : (n : ℝ)-1 ≠ 0 := by linarith
  field_simp [n0, n1]
  <;> ring

lemma t4_complement_involutive {n : ℕ} (S : Finset (Fin n)) :
    control (control S) = S := by
  classical
  ext i
  simp [control]

lemma t4_complement_mem {n m : ℕ} {S : Finset (Fin n)} (hS : S ∈ design n m) :
    control S ∈ design n (n-m) := by
  classical
  have hSc : S.card = m := (Finset.mem_powersetCard.mp hS).2
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.subset_univ _, ?_⟩
  simp only [control, Finset.card_sdiff_of_subset (Finset.subset_univ S),
    Finset.card_univ, Fintype.card_fin, hSc]

lemma t4_complement_expectation {n m : ℕ} (hmn : m ≤ n)
    (f : Finset (Fin n) → ℝ) :
    expectation m (fun S => f (control S)) = expectation (n-m) f := by
  classical
  have hsum : (∑ S ∈ design n m, f (control S)) = ∑ S ∈ design n (n-m), f S := by
    refine Finset.sum_bij (fun S _ => control S) (fun S hS => t4_complement_mem hS)
      ?_ ?_ (fun _ _ => rfl)
    · intro S hS T hT heq
      simpa only [t4_complement_involutive] using congrArg control heq
    · intro T hT
      refine ⟨control T, ?_, t4_complement_involutive T⟩
      simpa only [Nat.sub_sub_self hmn] using t4_complement_mem hT
  have hcard : (design n m).card = (design n (n-m)).card := by
    simp only [design, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact (Nat.choose_symm hmn).symm
  unfold expectation
  rw [hsum, hcard]

lemma t4_complement_variance {n m : ℕ} (hmn : m ≤ n)
    (f : Finset (Fin n) → ℝ) :
    variance m (fun S => f (control S)) = variance (n-m) f := by
  unfold variance
  rw [t4_complement_expectation hmn]
  exact t4_complement_expectation hmn (fun S => (f S - expectation (n-m) f)^2)

/-- Raw second moment; deriving it first avoids any normalization of a. -/
lemma t4_mean_second {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) (hmn : m ≤ n)
    (a : Fin n → ℝ) :
    expectation m (fun S => (mean S a)^2) =
      (1 / (m : ℝ)^2) *
        (((m : ℝ)/n - (m : ℝ)*(m-1)/((n : ℝ)*(n-1))) * (∑ i, a i^2) +
          ((m : ℝ)*(m-1)/((n : ℝ)*(n-1))) * (∑ i, a i)^2) := by
  classical
  let p₁ : ℝ := (m : ℝ)/n
  let p₂ : ℝ := (m : ℝ)*(m-1)/((n : ℝ)*(n-1))
  have hpair : ∀ i j : Fin n,
      expectation m (fun S => indicator S i * indicator S j) =
        p₂ + if i = j then p₁-p₂ else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      have he : (fun S => indicator S i * indicator S i) = (fun S => indicator S i) := by
        funext S
        by_cases hi : i ∈ S <;> simp [indicator, hi]
      rw [he, indicator_expectation (by omega) hm hmn]
      simp [p₁] <;> ring
    · rw [t4_pair_inclusion hn hmn i j hij]
      simp [hij, p₂]
  have hform : ∀ S ∈ design n m,
      (mean S a)^2 = (1/(m : ℝ)^2) *
        ∑ i, ∑ j, (a i*a j) * (indicator S i*indicator S j) := by
    intro S hS
    have hSc : S.card = m := (Finset.mem_powersetCard.mp hS).2
    rw [mean, hSc, ← indicator_sum S a]
    calc
      _ = (1/(m : ℝ)^2)*((∑ i, indicator S i*a i)*(∑ j, indicator S j*a j)) := by ring
      _ = _ := by
        congr 1
        simp only [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [expectation_congr m _ _ hform, expectation_mul]
  simp_rw [expectation_sum, expectation_mul, hpair]
  have hexpand : (∑ i, ∑ j, a i*a j*(p₂ + if i = j then p₁-p₂ else 0)) =
      (p₁-p₂)*(∑ i, a i^2) + p₂*(∑ i, a i)^2 := by
    simp_rw [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [← Finset.sum_mul, ← Finset.mul_sum, pow_two]
    ring
  rw [hexpand]

lemma t4_mean_variance_bound {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) (hmn : m ≤ n)
    (a : Fin n → ℝ) :
    variance m (fun S => mean S a) ≤
      ((n : ℝ)-m)/((m : ℝ)*(n-1)) * popMean (fun i => a i^2) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have n0 : (n : ℝ) ≠ 0 := by linarith
  have n1 : (n : ℝ)-1 ≠ 0 := by linarith
  have m0 : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hρ : 0 ≤ ((n : ℝ)-m)/((m : ℝ)*(n-1)) :=
    div_nonneg (sub_nonneg.mpr hmn') (mul_nonneg hm'.le (by linarith))
  have heq : variance m (fun S => mean S a) =
      ((n : ℝ)-m)/((m : ℝ)*(n-1)) *
        (popMean (fun i => a i^2) - (popMean a)^2) := by
    rw [t4_variance_eq hmn, t4_mean_second hn hm hmn, mean_unbiased (by omega) hm hmn]
    simp only [popMean, mean, Finset.card_univ, Fintype.card_fin]
    field_simp [n0, n1, m0]
    <;> ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) hρ

lemma t4_centered_mean_second {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) (hmn : m ≤ n)
    (a : Fin n → ℝ) (ha : popMean a = 0) :
    expectation m (fun S => (mean S a)^2) ≤
      ((n : ℝ)-m)/((m : ℝ)*(n-1)) * popMean (fun i => a i^2) := by
  have he : expectation m (fun S => mean S a) = 0 := by
    rw [mean_unbiased (by omega) hm hmn, ha]
  have hv := t4_mean_variance_bound hn hm hmn a
  rwa [t4_variance_eq hmn, he, zero_pow (by decide : 2 ≠ 0), sub_zero] at hv

/-- A coarse bound sufficient for T4(f). It uses only second moments
and |h-d| ≤ nκ, without a fourth-moment bound. -/
lemma t4_covariance_coarse {n d s : ℕ} (P : Population n d)
    (hn : 2 ≤ n) (hs : 0 < s) (hsn : s ≤ n) (hP : standardized P)
    (y : Fin n → ℝ) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : popMean (fun i => y i^2) ≤ K) :
    variance s (fun S => sampleCov S (leverage P) y) ≤
      4 * (((n : ℝ)-s)/((s : ℝ)*(n-1))) * (n : ℝ)^2 * kappa P^2 * K := by
  classical
  let u := fun i => leverage P i - (d : ℝ)
  let v := centered y
  let B : ℝ := (n : ℝ)*kappa P
  let ρ : ℝ := ((n : ℝ)-s)/((s : ℝ)*(n-1))
  have hn0 : 0 < n := by omega
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hsn' : (s : ℝ) ≤ n := by exact_mod_cast hsn
  have hρ : 0 ≤ ρ := by
    exact div_nonneg (sub_nonneg.mpr hsn') (mul_nonneg hs'.le (by linarith))
  have hU := centered_leverage_moment_bounds P hn0 hP.2 y K hK
  have hu : ∀ i, |u i| ≤ B := hU.2.1
  have hB : 0 ≤ B := le_trans (Nat.cast_nonneg d) hU.1
  have hvK : popMean (fun i => v i^2) ≤ K := hU.2.2.2.2.2.1
  have huvK : popMean (fun i => (u i*v i)^2) ≤ B^2*K := by
    simpa only [u, v, B, mul_pow] using hU.2.2.2.2.2.2.2
  have hS : (univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn0⟩, mem_univ _⟩
  have hv0 : popMean v = 0 := by
    change mean univ (fun i => y i - popMean y) = 0
    rw [mean_sub, mean_const univ hS]
    exact sub_self _
  have hmeanU : ∀ S, |mean S u| ≤ B := by
    intro S
    by_cases hne : S.Nonempty
    · have hlow : mean S (fun _ => -B) ≤ mean S u :=
        mean_mono _ _ _ (fun i _ => (abs_le.mp (hu i)).1)
      have hupp : mean S u ≤ mean S (fun _ => B) :=
        mean_mono _ _ _ (fun i _ => (abs_le.mp (hu i)).2)
      rw [mean_const S hne] at hlow hupp
      exact abs_le.mpr ⟨hlow, hupp⟩
    · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst S
      simpa [mean] using hB
  have hfirst : variance s (fun S => mean S (fun i => u i*v i)) ≤ ρ*B^2*K := by
    exact (t4_mean_variance_bound hn hs hsn _).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left huvK hρ)
  have hsecond : variance s (fun S => mean S u * mean S v) ≤ ρ*B^2*K := by
    calc
      _ ≤ expectation s (fun S => (mean S u * mean S v)^2) := t4_variance_le_second hsn _
      _ ≤ expectation s (fun S => B^2 * (mean S v)^2) := by
        apply t4_expectation_mono
        intro S _
        rw [mul_pow]
        have hsq : (mean S u)^2 ≤ B^2 := by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hmeanU S)
        exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = B^2 * expectation s (fun S => (mean S v)^2) := expectation_mul _ _ _
      _ ≤ B^2*(ρ*popMean (fun i => v i^2)) :=
        mul_le_mul_of_nonneg_left (t4_centered_mean_second hn hs hsn v hv0) (sq_nonneg _)
      _ ≤ B^2*(ρ*K) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hvK hρ) (sq_nonneg _)
      _ = ρ*B^2*K := by ring
  have hcov : ∀ S ∈ design n s, sampleCov S (leverage P) y = sampleCov S u v := by
    intro S hSS
    have hSc : S.card = s := (Finset.mem_powersetCard.mp hSS).2
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    change sampleCov S (leverage P) y = sampleCov S (fun i => leverage P i - (d : ℝ)) (fun i => y i - popMean y)
    exact (covariance_location_invariant S hne (leverage P) y (d : ℝ) (popMean y)).symm
  have hvar : variance s (fun S => sampleCov S (leverage P) y) =
      variance s (fun S => sampleCov S u v) := by
    unfold variance
    rw [expectation_congr s _ _ hcov]
    apply expectation_congr
    intro S hSS
    dsimp only
    rw [hcov S hSS]
  rw [hvar]
  have hdiff := variance_difference_bound s
    (fun S => mean S (fun i => u i*v i)) (fun S => mean S u * mean S v)
  change variance s (fun S => mean S (fun i => u i*v i) - mean S u*mean S v) ≤ _
  calc
    _ ≤ 2*variance s (fun S => mean S (fun i => u i*v i)) +
        2*variance s (fun S => mean S u*mean S v) := hdiff
    _ ≤ 4*ρ*B^2*K := by linarith
    _ = _ := by dsimp [ρ, B]; ring

lemma t4_allocation_rho (N s a : ℝ) (hN : 3 ≤ N) (ha : 0 < a)
    (hs : a*N ≤ s) (hsN : s ≤ N) :
    (N-s)/(s*(N-1)) ≤ 2/(a*N) := by
  have hN0 : 0 < N := by linarith
  have hs0 : 0 < s := lt_of_lt_of_le (mul_pos ha hN0) hs
  have hden : 0 < s*(N-1) := mul_pos hs0 (by linarith)
  have han : 0 < a*N := mul_pos ha hN0
  apply (div_le_div_iff₀ hden han).mpr
  have h₁ : a*N*N ≤ s*N := mul_le_mul_of_nonneg_right hs (le_of_lt hN0)
  have h₂ : s*N ≤ 2*(s*(N-1)) := by
    nlinarith [mul_nonneg (le_of_lt hs0) (show 0 ≤ N-2 by linarith)]
  have h₃ : (N-s)*(a*N) ≤ a*N*N := by
    nlinarith [mul_nonneg (le_of_lt hs0) (le_of_lt han)]
  linarith

/-- T4. The finite estimate used here is
Var(Cov_A(h,y)) ≤ 4 ρ_s n² κ² K, hence ≤ (8K/a)nκ².
The additional nonnegative term in the rate is harmless. -/
theorem corrected_leverage_variance_order_proof (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) (h : standingAssumptions d m P) (t : Arm) :
    Asymptotics.IsBigO atTop
      (fun n => variance (m n) (fun S => sampleCov (armSet t S) (leverage (P n))
        (if t = .treated then (P n).yT else (P n).yC)))
      (fun n => (n : ℝ)*kappa (P n)^2 + kappa (P n)*(d n)/n) ∧
    Asymptotics.IsBigO atTop
      (fun n => variance (m n) (fun S => sampleCov (armSet t S) (leverage (P n))
        (if t = .treated then (P n).yT else (P n).yC) / n))
      (fun n => kappa (P n)^2/n + kappa (P n)*(d n)/(n : ℝ)^3) := by
  classical
  rcases h with ⟨hsize, ⟨K, hK, hym⟩, hstd, ⟨lo, hi, hlo, hlohi, hhi, halloc⟩⟩
  let a : ℝ := min lo (1-hi)
  have ha : 0 < a := lt_min hlo (sub_pos.mpr hhi)
  let C : ℝ := 8*K/a
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let f := fun n (S : Finset (Fin n)) => sampleCov (armSet t S) (leverage (P n))
    (if t = .treated then (P n).yT else (P n).yC)
  let r := fun (n : ℕ) => (n : ℝ)*kappa (P n)^2 + kappa (P n)*(d n)/n
  have hbound : ∀ᶠ n in atTop, 0 ≤ variance (m n) (f n) ∧
      0 ≤ r n ∧ variance (m n) (f n) ≤ C*r n := by
    filter_upwards [hstd, Filter.eventually_ge_atTop (3 : ℕ)] with n hPn hn
    have hn0 : 0 < n := by omega
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by positivity
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hsz := hsize n hn
    have hp := halloc n hn
    have hκ : 0 ≤ kappa (P n) :=
      (div_nonneg (Nat.cast_nonneg _) (le_of_lt hnpos)).trans
        (kappa_bounds (P n) hn0 hPn.2).1
    have htail : 0 ≤ kappa (P n)*(d n)/(n : ℝ) := by positivity
    have hr : 0 ≤ r n := add_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) htail
    have hY : popMean (fun i => ((if t = .treated then (P n).yT else (P n).yC) i)^2) ≤ K := by
      cases t with
      | treated => simpa using (hym n hn).1
      | control => simpa using (hym n hn).2.1
    let s := armSize n (m n) t
    have hs : 0 < s := by cases t <;> simp only [s, armSize] <;> omega
    have hsn : s ≤ n := by cases t <;> simp only [s, armSize] <;> omega
    have hslo : a*(n : ℝ) ≤ s := by
      cases t with
      | treated =>
        change a*(n : ℝ) ≤ (m n : ℝ)
        have hlow : lo*(n : ℝ) < m n := (lt_div_iff₀ hnpos).mp hp.1
        exact (mul_le_mul_of_nonneg_right (min_le_left lo (1-hi)) (le_of_lt hnpos)).trans hlow.le
      | control =>
        change a*(n : ℝ) ≤ ((n-m n : ℕ) : ℝ)
        rw [Nat.cast_sub (Nat.le_of_lt hsz.2.2.2)]
        have hupp : (m n : ℝ) < hi*n := (div_lt_iff₀ hnpos).mp hp.2
        have hamin : a ≤ 1-hi := min_le_right _ _
        have hmul := mul_le_mul_of_nonneg_right hamin (le_of_lt hnpos)
        nlinarith
    have hρ := t4_allocation_rho (n : ℝ) (s : ℝ) a hn' ha hslo (by exact_mod_cast hsn)
    have hfinite : variance (m n) (f n) ≤
        4 * (((n : ℝ)-s)/((s : ℝ)*(n-1))) * (n : ℝ)^2 * kappa (P n)^2 * K := by
      have hc := t4_covariance_coarse (P n) (by omega : 2 ≤ n) hs hsn hPn
        (if t = .treated then (P n).yT else (P n).yC) K hK hY
      cases t with
      | treated => exact hc
      | control =>
        change variance (m n) (fun S => sampleCov (control S) (leverage (P n)) (P n).yC) ≤ _
        rw [t4_complement_variance hsz.2.2.2.le (fun S => sampleCov S (leverage (P n)) (P n).yC)]
        exact hc
    have hcoarse : variance (m n) (f n) ≤ C*((n : ℝ)*kappa (P n)^2) := by
      calc
        _ ≤ 4 * (((n : ℝ)-s)/((s : ℝ)*(n-1))) * (n : ℝ)^2 * kappa (P n)^2 * K := hfinite
        _ ≤ 4 * (2/(a*n)) * (n : ℝ)^2 * kappa (P n)^2 * K := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ (by norm_num))
                (sq_nonneg _)) (sq_nonneg _)) hK
        _ = C*((n : ℝ)*kappa (P n)^2) := by
          dsimp [C]
          field_simp [ne_of_gt ha, hnne]
          <;> ring
    refine ⟨t4_variance_nonneg _ _, hr, hcoarse.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right htail) hC
  constructor
  · apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hbound] with n hn
    change ‖variance (m n) (f n)‖ ≤ C * ‖r n‖
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn.1, abs_of_nonneg hn.2.1] using hn.2.2
  · apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hbound, Filter.eventually_ge_atTop (3 : ℕ)] with n hn hn3
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hrate : r n/(n : ℝ)^2 =
        kappa (P n)^2/n + kappa (P n)*(d n)/(n : ℝ)^3 := by
      dsimp [r]
      field_simp [hnne]
      <;> ring
    have hscaled := div_le_div_of_nonneg_right hn.2.2 (sq_nonneg (n : ℝ))
    have hnonneg : 0 ≤ variance (m n) (fun S => f n S / n) := t4_variance_nonneg _ _
    have hrate0 : 0 ≤ r n/(n : ℝ)^2 := div_nonneg hn.2.1 (sq_nonneg _)
    change ‖variance (m n) (fun S => f n S / n)‖ ≤
      C * ‖kappa (P n)^2/n + kappa (P n)*(d n)/(n : ℝ)^3‖
    rw [← hrate, Real.norm_eq_abs, abs_of_nonneg hnonneg,
      Real.norm_eq_abs, abs_of_nonneg hrate0, t4_variance_div]
    simpa only [mul_div_assoc] using hscaled

/-!
T6: the third sampling moment.
-/

lemma t6_cast_choose_three (a : ℕ) :
    (a.choose 3 : ℝ) = (a : ℝ)*(a-1)*(a-2)/6 := by
  by_cases ha : a = 0
  · subst a
    norm_num
  have ha1 : 1 ≤ a := by omega
  have hc : (a : ℝ) * ((a-1).choose 2 : ℝ) = (a.choose 3 : ℝ)*3 := by
    exact_mod_cast (show a * (a-1).choose 2 = a.choose 3 * 3 by
      simpa only [Nat.sub_add_cancel ha1] using Nat.add_one_mul_choose_eq (a-1) 2)
  rw [Nat.cast_choose_two ℝ, Nat.cast_sub ha1] at hc
  norm_num at hc
  nlinarith only [hc]

lemma t6_triple_inclusion {n m : ℕ} (hn : 3 ≤ n) (hmn : m ≤ n)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    expectation m (fun S => indicator S i*indicator S j*indicator S k) =
      (m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2)) := by
  classical
  have hcard : ({i,j,k} : Finset (Fin n)).card = 3 := by simp [hij, hik, hjk]
  have he : expectation m (fun S => indicator S i*indicator S j*indicator S k) =
      expectation m (fun S => if ({i,j,k} : Finset (Fin n)) ⊆ S then 1 else 0) := by
    apply expectation_congr
    intro S _
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> by_cases hk : k ∈ S <;>
      simp [indicator, Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj, hk]
  rw [he, t4_inclusion_ratio hmn, hcard, t6_cast_choose_three, t6_cast_choose_three]
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have n0 : (n : ℝ) ≠ 0 := by linarith
  have n1 : (n : ℝ)-1 ≠ 0 := by linarith
  have n2 : (n : ℝ)-2 ≠ 0 := by linarith
  field_simp [n0, n1, n2]
  <;> ring

/-- Equality-pattern expansion. It is valid also at m=1 and m=2. -/
lemma t6_indicator_third {n m : ℕ} (hn : 3 ≤ n) (hm : 0 < m) (hmn : m ≤ n)
    (i j k : Fin n) :
    let p₁ : ℝ := (m : ℝ)/n
    let p₂ : ℝ := (m : ℝ)*(m-1)/((n : ℝ)*(n-1))
    let p₃ : ℝ := (m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2))
    expectation m (fun S => indicator S i*indicator S j*indicator S k) =
      p₃ + (p₂-p₃)*((if i=j then 1 else 0)+(if i=k then 1 else 0)+
        (if j=k then 1 else 0)) + (p₁-3*p₂+2*p₃)*(if i=j ∧ j=k then 1 else 0) := by
  classical
  dsimp only
  by_cases hij : i=j
  · subst j
    by_cases hik : i=k
    · subst k
      have he : (fun S => indicator S i*indicator S i*indicator S i) =
          (fun S => indicator S i) := by
        funext S
        by_cases hi : i ∈ S <;> simp [indicator, hi]
      rw [he, indicator_expectation (by omega) hm hmn]
      simp only [ite_true, and_self]
      ring
    · have he : (fun S => indicator S i*indicator S i*indicator S k) =
          (fun S => indicator S i*indicator S k) := by
        funext S
        by_cases hi : i ∈ S <;> by_cases hk : k ∈ S <;> simp [indicator, hi, hk]
      rw [he, t4_pair_inclusion (by omega) hmn i k hik]
      simp only [hik, ite_true, ite_false, and_false]
      ring
  · by_cases hik : i=k
    · subst k
      have he : (fun S => indicator S i*indicator S j*indicator S i) =
          (fun S => indicator S i*indicator S j) := by
        funext S
        by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [indicator, Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
      rw [he, t4_pair_inclusion (by omega) hmn i j hij]
      simp only [hij, Ne.symm hij, ite_true, ite_false, false_and]
      ring
    · by_cases hjk : j=k
      · subst k
        have he : (fun S => indicator S i*indicator S j*indicator S j) =
            (fun S => indicator S i*indicator S j) := by
          funext S
          by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [indicator, Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
        rw [he, t4_pair_inclusion (by omega) hmn i j hij]
        simp only [hij, ite_true, ite_false, false_and]
        ring
      · rw [t6_triple_inclusion hn hmn i j k hij hik hjk]
        simp only [hij, hik, hjk, ite_false, false_and]
        ring

lemma t6_centered_third_moment {n m : ℕ} (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n)
    (a b c : Fin n → ℝ) (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0)
    (hc : ∑ i, c i = 0) :
    expectation m (fun S => mean S a*mean S b*mean S c) =
      NTTT n m * popMean (fun i => a i*b i*c i) := by
  classical
  let p₁ : ℝ := (m : ℝ)/n
  let p₂ : ℝ := (m : ℝ)*(m-1)/((n : ℝ)*(n-1))
  let p₃ : ℝ := (m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2))
  have hform : ∀ S ∈ design n m,
      mean S a*mean S b*mean S c = (1/(m : ℝ)^3) *
        ∑ i, ∑ j, ∑ k, (a i*b j*c k)*(indicator S i*indicator S j*indicator S k) := by
    intro S hS
    have hSc : S.card = m := (Finset.mem_powersetCard.mp hS).2
    simp only [mean, hSc]
    rw [← indicator_sum S a, ← indicator_sum S b, ← indicator_sum S c]
    calc
      _ = (1/(m : ℝ)^3)*
          ((∑ i, indicator S i*a i)*(∑ j, indicator S j*b j)*(∑ k, indicator S k*c k)) := by ring
      _ = _ := by
        congr 1
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum univ (fun j => indicator S j*b j) (indicator S i*a i), Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hsum0 : (∑ i, ∑ j, ∑ k, a i*b j*c k) = 0 := by
    simp only [← Finset.mul_sum, hc, mul_zero, Finset.sum_const_zero]
  have hsumij : (∑ i, ∑ j, ∑ k, if i=j then a i*b j*c k else 0) = 0 := by
    simp only [Finset.sum_ite_irrel, ← Finset.mul_sum, hc, mul_zero,
      ite_self, Finset.sum_const_zero]
  have hsumik : (∑ i, ∑ j, ∑ k, if i=k then a i*b j*c k else 0) = 0 := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hinner : ∀ i, (∑ j, a i*b j*c i) = 0 := by
      intro i
      rw [← Finset.sum_mul, ← Finset.mul_sum, hb]
      ring
    simp_rw [hinner]
    simp
  have hsumjk : (∑ i, ∑ j, ∑ k, if j=k then a i*b j*c k else 0) = 0 := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [← Finset.sum_mul, ha, zero_mul]
  have hsumdiag : (∑ i, ∑ j, ∑ k, if i=j ∧ j=k then a i*b j*c k else 0) =
      ∑ i, a i*b i*c i := by
    simp_rw [ite_and]
    simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_const_zero]
  have hw : ∀ i j k : Fin n,
      (a i*b j*c k)*expectation m (fun S => indicator S i*indicator S j*indicator S k) =
        p₃*(a i*b j*c k) + (p₂-p₃)*
          ((if i=j then a i*b j*c k else 0)+(if i=k then a i*b j*c k else 0)+
            (if j=k then a i*b j*c k else 0)) +
          (p₁-3*p₂+2*p₃)*(if i=j ∧ j=k then a i*b j*c k else 0) := by
    intro i j k
    rw [t6_indicator_third hn hm hmn.le]
    dsimp only [p₁, p₂, p₃]
    split_ifs <;> ring
  rw [expectation_congr m _ _ hform, expectation_mul]
  simp_rw [expectation_sum, expectation_mul, hw]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    hsum0, hsumij, hsumik, hsumjk, hsumdiag, hc, Finset.sum_const_zero, mul_zero, zero_add, add_zero]
  have hcoef := third_moment_coefficient n m hn hm
  rw [← mul_assoc]
  change (1/(m : ℝ)^3)*(p₁-3*p₂+2*p₃)*(∑ i, a i*b i*c i) = _
  have hcoef' : (1/(m : ℝ)^3)*(p₁-3*p₂+2*p₃) = (1/(n : ℝ))*NTTT n m := by
    calc
      _ = (1/(m : ℝ)^3)*((m : ℝ)/n -
          3*(m : ℝ)*(m-1)/((n : ℝ)*(n-1)) +
          2*(m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2))) := by
        dsimp only [p₁, p₂, p₃]
        ring
      _ = _ := hcoef
  rw [hcoef']
  simp only [popMean, mean, Finset.card_univ, Fintype.card_fin]
  ring

lemma t6_sum_centered {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) :
    ∑ i, centered y i = 0 := by
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [centered, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, popMean, mean]
  field_simp [n0]
  <;> ring

lemma t6_leverage_centering {n d : ℕ} (P : Population n d) (y : Fin n → ℝ) :
    popMean (fun i => leverage P i * centered y i) = leverageCov P y := by
  change mean univ (fun i => leverage P i * (y i-popMean y)) =
    mean univ (fun i => leverage P i*y i)-mean univ (leverage P)*mean univ y
  have hf : (fun i => leverage P i*(y i-popMean y)) =
      (fun i => leverage P i*y i-popMean y*leverage P i) := by funext i; ring
  rw [hf, mean_sub, mean_mul]
  change _ - mean univ y * mean univ (leverage P) = _
  ring

lemma t6_coordinate_contraction {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0)
    (y : Fin n → ℝ) :
    expectation m (fun S => dot (xMean P S) (xMean P S) * mean S (centered y)) =
      NTTT n m * leverageCov P y := by
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hzero : ∀ k, ∑ i, P.x i k = 0 := by
    intro k
    have hk : (∑ i, P.x i k)/(n : ℝ) = 0 := by
      simpa only [xMean, mean, Finset.card_univ, Fintype.card_fin, Pi.zero_apply]
        using congrFun hx k
    exact (div_eq_zero_iff.mp hk).resolve_right n0
  have hcoord : ∀ k, expectation m (fun S =>
      mean S (fun i => P.x i k)*mean S (fun i => P.x i k)*mean S (centered y)) =
      NTTT n m * popMean (fun i => P.x i k*P.x i k*centered y i) := by
    intro k
    exact t6_centered_third_moment hn hm hmn _ _ _ (hzero k) (hzero k)
      (t6_sum_centered (by omega) y)
  calc
    _ = ∑ k, expectation m (fun S =>
        mean S (fun i => P.x i k)*mean S (fun i => P.x i k)*mean S (centered y)) := by
      simp only [dot, xMean, Finset.sum_mul, expectation_sum]
    _ = ∑ k, NTTT n m * popMean (fun i => P.x i k*P.x i k*centered y i) :=
      Finset.sum_congr rfl (fun k _ => hcoord k)
    _ = NTTT n m * popMean (fun i => leverage P i*centered y i) := by
      rw [← Finset.mul_sum, ← popMean_sum]
      simp only [leverage, dot, Finset.sum_mul]
    _ = NTTT n m * leverageCov P y := by rw [t6_leverage_centering]

lemma t6_nu3_sign {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (y : Fin n → ℝ) :
    dot (xMean P S) (armNu3 P S y) =
      -(dot (xMean P S) (xMean P S)*mean S (centered y)) := by
  simp only [dot, armNu3, mul_neg, ← mul_assoc, Finset.sum_neg_distrib, Finset.sum_mul]

/-- T6: corrected third-component bias. The treated and control cubic
moments have coefficients NTTT and NCCC; their ν₃ contribution is
−NCCC leverageCov(P,yC) + NTTT leverageCov(P,yT). -/
theorem corrected_interacted_third_bias_proof {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0) :
    expectation m (fun S => dot (xMean P S) (xMean P S) * mean S (centered P.yT)) =
      NTTT n m * leverageCov P P.yT ∧
    expectation m (fun S => dot (xMean P (control S)) (xMean P (control S)) *
      mean (control S) (centered P.yC)) = NCCC n m * leverageCov P P.yC ∧
    expectation m (fun S => dot (xMean P (control S)) (armNu3 P (control S) P.yC)) -
      expectation m (fun S => dot (xMean P S) (armNu3 P S P.yT)) =
        -NCCC n m * leverageCov P P.yC + NTTT n m * leverageCov P P.yT := by
  have hT := t6_coordinate_contraction P hn hm hmn hx P.yT
  have hC : expectation m (fun S => dot (xMean P (control S)) (xMean P (control S)) *
      mean (control S) (centered P.yC)) = NCCC n m * leverageCov P P.yC := by
    rw [t4_complement_expectation hmn.le (fun S => dot (xMean P S) (xMean P S) * mean S (centered P.yC))]
    exact t6_coordinate_contraction P hn (by omega) (by omega) hx P.yC
  refine ⟨hT, hC, ?_⟩
  simp_rw [t6_nu3_sign]
  have hneg : ∀ f : Finset (Fin n) → ℝ,
      expectation m (fun S => -(f S)) = -expectation m f := by
    intro f
    simpa only [neg_one_mul] using expectation_mul m f (-1)
  rw [hneg, hneg, hC, hT]
  ring

/-!
T8: deterministic Euclidean estimates for the inverse matrix.
-/


lemma t8_dot_self_nonneg {d : ℕ} (v : Fin d → ℝ) : 0 ≤ dot v v := by
  exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

lemma t8_cauchy_schwarz {d : ℕ} (u v : Fin d → ℝ) :
    (dot u v)^2 ≤ dot u u * dot v v := by
  simpa only [dot, pow_two] using Finset.sum_mul_sq_le_sq_mul_sq univ u v


/-- A deterministic inverse estimate; the square uses the Euclidean dot
product, avoiding the sup norm on the unbundled coordinate function space. -/
lemma t8_coercive_inverse_squared {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hdet : A.det ≠ 0)
    (hA : ∀ z : Fin d → ℝ, dot z z / 4 ≤ dot z (A *ᵥ z))
    (v : Fin d → ℝ) :
    dot (A⁻¹ *ᵥ v) (A⁻¹ *ᵥ v) ≤ 16 * dot v v := by
  let z := A⁻¹ *ᵥ v
  have hAz : A *ᵥ z = v := by
    dsimp only [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have hlow : dot z z / 4 ≤ dot z v := by simpa only [hAz] using hA z
  have hzz : 0 ≤ dot z z := t8_dot_self_nonneg z
  have hzv : 0 ≤ dot z v := (div_nonneg hzz (by norm_num)).trans hlow
  have hsq : (dot z z / 4)^2 ≤ (dot z v)^2 :=
    (sq_le_sq₀ (div_nonneg hzz (by norm_num)) hzv).mpr hlow
  have hcs := t8_cauchy_schwarz z v
  change dot z z ≤ 16*dot v v
  by_contra hbad
  have hgt : 16*dot v v < dot z z := lt_of_not_ge hbad
  have hpos : 0 < dot z z := lt_of_le_of_lt
    (mul_nonneg (by norm_num) (t8_dot_self_nonneg v)) hgt
  have hprod := mul_pos hpos (sub_pos.mpr hgt)
  nlinarith




end
end AronowAudit.P005.Wave1
