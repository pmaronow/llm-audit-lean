import AronowAudit.P004.P004_Spatial
import AronowAudit.P004.P004_SpatialCLTCompletion
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.Analysis.SpecificLimits.Basic

/-!
T18 and T19: Hájek linearization rates and a dependency CLT counterexample.
-/
namespace AronowAudit.P004.Wave1

open scoped BigOperators Matrix Classical Topology
open MeasureTheory Filter
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

variable {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
  [∀ N, MeasurableSpace (Space N)]

/-! T18: elementary finite probability and a local second-moment bound. -/

lemma t18_expect_abs_le {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (F : Assignment N → ℝ) (b : ℝ)
    (hF : ∀ z, |F z| ≤ b) : |expect p F| ≤ b := by
  have hl := expect_mono p hp (fun _ => -b) F (fun z => (abs_le.mp (hF z)).1)
  have hu := expect_mono p hp F (fun _ => b) (fun z => (abs_le.mp (hF z)).2)
  rw [expect_const] at hl hu
  exact abs_le.mpr ⟨hl, hu⟩

lemma t18_expect_coordinate {N : ℕ} (p : Fin N → ℝ) (i : Fin N) (f : Bool → ℝ) :
    expect p (fun z => f (z i)) = p i * f true + (1-p i) * f false := by
  have hj (a : Bool) (u : {j : Fin N // j ≠ i} → Bool) :
      f (joinAssignment i a u i) = f a := by simp [joinAssignment]
  have hw : (∑ u : {j : Fin N // j ≠ i} → Bool,
      ∏ j : {j : Fin N // j ≠ i}, coin (p j) (u j)) = 1 :=
    by
      rw [← Fintype.prod_sum]
      simp [coin]
  have hi (a : Bool) : (∑ u : {j : Fin N // j ≠ i} → Bool,
      (∏ j : {j : Fin N // j ≠ i}, coin (p j) (u j)) * f a) = f a := by
    rw [← Finset.sum_mul, hw, one_mul]
  rw [AronowAudit.P004.expect_split p i]
  simp_rw [hj, hi]
  simp [Fintype.sum_bool, coin, add_comm]

lemma t18_coin_pos (p : ℝ) (hp : 0 < p ∧ p < 1) (a : Bool) : 0 < coin p a := by
  cases a <;> simp only [coin, Bool.false_eq_true, ite_false, ite_true]
  · exact sub_pos.mpr hp.2
  · exact hp.1

lemma t18_prob_nonneg {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A : Assignment N → Prop) : 0 ≤ prob p A := by
  change 0 ≤ expect p (fun z => if A z then 1 else 0)
  have hh := expect_mono p hp (fun _ => 0) (fun z => if A z then 1 else 0)
    (by intro z; split_ifs <;> norm_num)
  simpa only [expect_const] using hh

lemma t18_prob_mono {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A B : Assignment N → Prop)
    (h : ∀ z, A z → B z) : prob p A ≤ prob p B := by
  apply expect_mono p hp
  intro z
  by_cases ha : A z
  · simp only [if_pos ha, if_pos (h z ha), le_refl]
  · simp only [if_neg ha]
    split_ifs <;> norm_num

lemma t18_markov {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (Q : Assignment N → ℝ)
    (hQ : ∀ z, 0 ≤ Q z) (t : ℝ) (ht : 0 < t) :
    prob p (fun z => t < Q z) ≤ expect p Q / t := by
  apply (le_div_iff₀ ht).mpr
  unfold prob
  rw [mul_comm, ← expect_mul]
  apply expect_mono p hp
  intro z
  by_cases hz : t < Q z
  · simpa only [if_pos hz, mul_one] using hz.le
  · simpa only [if_neg hz, mul_zero] using hQ z

lemma t18_table_depends {N : ℕ} (R : CircleTable N) (i : Fin N) :
    DependsOn (R i) {k | interferes R i k} := by
  apply GraphCompletion.depends_of_update
  intro z k hk a
  by_contra hne
  apply hk
  right
  refine ⟨Function.update z k a, z, ?_, hne⟩
  intro j hj
  exact Function.update_of_ne hj _ _

lemma t18_local_variance {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (R X : CircleTable N)
    (B : Fin N → Finset (Fin N)) (D : ℕ) (L : ℝ) (hN : 0 < N)
    (hL : 0 ≤ L) (hX : ∀ i z, |X i z| ≤ L)
    (hdep : ∀ i, DependsOn (X i) {k | interferes R i k})
    (hdeg : ∀ i, (B i).card ≤ D)
    (hout : ∀ i j, j ∉ B i → ¬ sharesSource R i j) :
    variance p (fun z => (∑ i, X i z)/(N : ℝ)) ≤ (D : ℝ)*L^2/N := by
  have hv (i : Fin N) : variance p (X i) ≤ L^2 := by
    apply (variance_le_second p (X i)).trans
    rw [← expect_const p (L^2)]
    apply expect_mono p hp
    intro z
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (X i z)) hL).mpr (hX i z)
  have hcov (i j : Fin N) : cov p (X i) (X j) ≤ L^2 := by
    have hc := cov_young p hp (X i) (X j)
    linarith [hv i, hv j]
  have hz (i j : Fin N) (hij : ¬ sharesSource R i j) : cov p (X i) (X j) = 0 := by
    have hj : DependsOn (X j) ({k | interferes R i k}ᶜ) :=
      (hdep j).mono (by
        intro k hk hki
        exact hij ⟨k, hki, hk⟩)
    unfold cov
    rw [GraphCompletion.expect_mul_of_disjoint_depends p _ _ _ (hdep i) hj, sub_self]
  have hlocal : (∑ i, ∑ j, cov p (X i) (X j)) =
      ∑ i, ∑ j ∈ B i, cov p (X i) (X j) := by
    apply Finset.sum_congr rfl
    intro i _
    symm
    exact Finset.sum_subset (Finset.subset_univ _)
      (fun j _ hj => hz i j (hout i j hj))
  have hsum : (∑ i, ∑ j ∈ B i, cov p (X i) (X j)) ≤ (N : ℝ)*(D : ℝ)*L^2 := by
    calc
      _ ≤ ∑ _i : Fin N, (D : ℝ)*L^2 := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ∑ _j ∈ B i, L^2 := Finset.sum_le_sum (fun j _ => hcov i j)
          _ = ((B i).card : ℝ)*L^2 := by simp
          _ ≤ (D : ℝ)*L^2 :=
            mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hdeg i)) (sq_nonneg L)
      _ = _ := by simp [mul_assoc]
  rw [variance_div, variance_sum, hlocal]
  apply (div_le_div_of_nonneg_right hsum (sq_nonneg (N : ℝ))).trans_eq
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hn]
  <;> ring

private def t18_selected {N : ℕ} (p : ℝ) (F : CircleTable N) (a : Bool) : CircleTable N :=
  fun i z => (if z i = a then F i z else 0) / coin p a

private def t18_average {N : ℕ} (p : ℝ) (F : CircleTable N) (a : Bool)
    (z : Assignment N) : ℝ :=
  (∑ i, if z i = a then F i z else 0) / ((N : ℝ)*coin p a)

private def t18_B {N : ℕ} (p : ℝ) (R : CircleTable N) (a : Bool)
    (z : Assignment N) : ℝ :=
  t18_average p (fun i z => R i z-barMu (fun _ => p) R a) a z

private def t18_C {N : ℕ} (p : ℝ) (a : Bool) (z : Assignment N) : ℝ :=
  armCount z a / ((N : ℝ)*coin p a)

private def t18_Q {N : ℕ} (p : ℝ) (R : CircleTable N) (z : Assignment N) : ℝ :=
  (t18_B p R true z)^2 + (t18_B p R false z)^2 +
    (t18_C (N := N) p true z-1)^2 + (t18_C (N := N) p false z-1)^2

lemma t18_average_eq {N : ℕ} (p : ℝ) (F : CircleTable N) (a : Bool) :
    t18_average p F a = fun z => (∑ i, t18_selected p F a i z)/(N : ℝ) := by
  funext z
  simp only [t18_average, t18_selected, ← Finset.sum_div, div_div]
  rw [mul_comm (coin p a)]

lemma t18_selected_depends {N : ℕ} (p : ℝ) (R F : CircleTable N) (a : Bool)
    (hF : ∀ i, DependsOn (F i) {k | interferes R i k}) (i : Fin N) :
    DependsOn (t18_selected p F a i) {k | interferes R i k} := by
  intro x y hxy
  have hi : x i = y i := hxy i (Or.inl rfl)
  have hf : F i x = F i y := hF i hxy
  simp only [t18_selected, hi, hf]

lemma t18_selected_abs {N : ℕ} (p : ℝ) (hp : 0 < p ∧ p < 1)
    (F : CircleTable N) (a : Bool) (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ i z, |F i z| ≤ L) (i : Fin N) (z : Assignment N) :
    |t18_selected p F a i z| ≤ L / coin p a := by
  rw [t18_selected, abs_div, abs_of_pos (t18_coin_pos p hp a)]
  apply div_le_div_of_nonneg_right _ (t18_coin_pos p hp a).le
  split_ifs
  · exact hF i z
  · simpa only [abs_zero] using hL

lemma t18_barMu_abs {N : ℕ} (p b : ℝ) (R : CircleTable N)
    (hp : 0 < p ∧ p < 1) (hN : 0 < N) (hR : ∀ i z, |R i z| ≤ b) (a : Bool) :
    |barMu (fun _ => p) R a| ≤ b := by
  have hm (i : Fin N) : |marginal (fun _ => p) R i a| ≤ b := by
    rw [marginal_is_marginalization _ _ _ _ (fun _ => hp)]
    exact t18_expect_abs_le _ (fun _ => hp) _ b (fun z => hR i _)
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  unfold barMu
  rw [abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    |∑ i, marginal (fun _ => p) R i a| ≤ ∑ i, |marginal (fun _ => p) R i a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, b := Finset.sum_le_sum (fun i _ => hm i)
    _ = b*(N : ℝ) := by simp [mul_comm]

lemma t18_B_mean {N : ℕ} (p : ℝ) (R : CircleTable N)
    (hp : 0 < p ∧ p < 1) (hN : 0 < N) (a : Bool) :
    expect (fun _ => p) (t18_B p R a) = 0 := by
  have hm (i : Fin N) : expect (fun _ => p)
      (t18_selected p (fun i z => R i z-barMu (fun _ => p) R a) a i) =
      marginal (fun _ => p) R i a-barMu (fun _ => p) R a := by
    unfold t18_selected
    rw [expect_div]
    change marginal (fun _ => p) (fun i z => R i z-barMu (fun _ => p) R a) i a = _
    rw [marginal_is_marginalization _ _ _ _ (fun _ => hp), expect_sub, expect_const,
      ← marginal_is_marginalization (fun _ => p) R i a (fun _ => hp)]
  unfold t18_B
  rw [t18_average_eq, expect_div, expect_sum]
  simp_rw [hm]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, barMu]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hn]
  <;> ring

lemma t18_C_mean {N : ℕ} (p : ℝ) (hp : 0 < p ∧ p < 1)
    (hN : 0 < N) (a : Bool) : expect (fun _ => p) (t18_C (N := N) p a) = 1 := by
  have he (i : Fin N) : expect (fun _ => p)
      (fun z : Assignment N => if z i = a then (1 : ℝ) else 0) = coin p a := by
    rw [t18_expect_coordinate (fun _ => p) i (fun b => if b = a then 1 else 0)]
    cases a <;> norm_num [coin]
  unfold t18_C armCount
  rw [expect_div, expect_sum]
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact div_self (mul_ne_zero (by exact_mod_cast hN.ne') (t18_coin_pos p hp a).ne')

lemma t18_second_eq_variance {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ)
    (m : ℝ) (hm : expect p X = m) :
    expect p (fun z => (X z-m)^2) = variance p X := by
  rw [variance, cov_centered, hm]
  simp only [pow_two]

lemma t18_arm_moments {N : ℕ} (p b : ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (D : ℕ)
    (hp : 0 < p ∧ p < 1) (hb : 0 ≤ b) (hN : 0 < N)
    (hR : ∀ i z, |R i z| ≤ b) (hdeg : ∀ i, (B i).card ≤ D)
    (hout : ∀ i j, j ∉ B i → ¬ sharesSource R i j) (a : Bool) :
    expect (fun _ => p) (fun z => (t18_B p R a z)^2) ≤
        (D : ℝ)*(2*b/coin p a)^2/N ∧
    expect (fun _ => p) (fun z => (t18_C (N := N) p a z-1)^2) ≤
        (D : ℝ)*(1/coin p a)^2/N := by
  let F : CircleTable N := fun i z => R i z-barMu (fun _ => p) R a
  have hF (i : Fin N) (z : Assignment N) : |F i z| ≤ 2*b := by
    exact (abs_sub _ _).trans (by linarith [hR i z, t18_barMu_abs p b R hp hN hR a])
  have hdepF (i : Fin N) : DependsOn (F i) {k | interferes R i k} := by
    intro x y hxy
    dsimp only [F]
    rw [t18_table_depends R i hxy]
  have hdepOne (i : Fin N) : DependsOn (fun _ : Assignment N => (1 : ℝ))
      {k | interferes R i k} := by intro x y _; rfl
  have hB := t18_local_variance (fun _ => p) (fun _ => hp) R
    (t18_selected p F a) B D (2*b/coin p a) hN
    (div_nonneg (by positivity) (t18_coin_pos p hp a).le)
    (t18_selected_abs p hp F a (2*b) (by positivity) hF)
    (t18_selected_depends p R F a hdepF) hdeg hout
  have hC := t18_local_variance (fun _ => p) (fun _ => hp) R
    (t18_selected p (fun _ _ => 1) a) B D (1/coin p a) hN
    (div_nonneg (by norm_num) (t18_coin_pos p hp a).le)
    (t18_selected_abs p hp _ a 1 (by norm_num) (by intros; norm_num))
    (t18_selected_depends p R _ a hdepOne) hdeg hout
  have hBeq : t18_B p R a = fun z => (∑ i, t18_selected p F a i z)/(N : ℝ) :=
    t18_average_eq p F a
  have hCeq : t18_C (N := N) p a = fun z =>
      (∑ i, t18_selected p (fun _ _ => 1) a i z)/(N : ℝ) :=
    t18_average_eq p (fun _ _ => 1) a
  constructor
  · have hs := t18_second_eq_variance (fun _ => p) (t18_B p R a) 0 (t18_B_mean p R hp hN a)
    simp only [sub_zero] at hs
    rw [hs, hBeq]
    exact hB
  · rw [t18_second_eq_variance _ _ 1 (t18_C_mean p hp hN a), hCeq]
    exact hC

lemma t18_Q_nonneg {N : ℕ} (p : ℝ) (R : CircleTable N) (z : Assignment N) :
    0 ≤ t18_Q p R z := by unfold t18_Q; positivity

/-! The deterministic ratio estimate.  The four-square statistic controls the
remainder whenever it is at most 1/4; it also forces both arms to be nonempty. -/
lemma t18_remainder_bound {N : ℕ} (p : ℝ) (R : CircleTable N) (z : Assignment N)
    (hp : 0 < p ∧ p < 1) (hN : 0 < N) (hQ : t18_Q p R z ≤ 1/4) :
    |hajek R z-linearHajek (fun _ => p) R z| ≤ t18_Q p R z := by
  have hsq1 := sq_nonneg (t18_B p R true z)
  have hsq0 := sq_nonneg (t18_B p R false z)
  have hs1 := sq_nonneg (t18_C (N := N) p true z-1)
  have hs0 := sq_nonneg (t18_C (N := N) p false z-1)
  have hc1 : 1/2 ≤ t18_C (N := N) p true z := by
    unfold t18_Q at hQ
    nlinarith [sq_nonneg (t18_C (N := N) p true z-(1/2 : ℝ))]
  have hc0 : 1/2 ≤ t18_C (N := N) p false z := by
    unfold t18_Q at hQ
    nlinarith [sq_nonneg (t18_C (N := N) p false z-(1/2 : ℝ))]
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h1 : 0 < armCount z true := by
    have hh : 0 < armCount z true / ((N : ℝ)*p) := by
      simpa only [t18_C, coin, ite_true] using (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hc1)
    exact (div_pos_iff_of_pos_right (mul_pos hn hp.1)).mp hh
  have h0 : 0 < armCount z false := by
    have hh : 0 < armCount z false / ((N : ℝ)*(1-p)) := by
      simpa only [t18_C, coin, Bool.false_eq_true, ite_false] using
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hc0)
    exact (div_pos_iff_of_pos_right (mul_pos hn (sub_pos.mpr hp.2))).mp hh
  have hB1 : t18_B p R true z =
      (∑ i, bit (z i)*(R i z-barMu (fun _ => p) R true))/((N : ℝ)*p) := by
    unfold t18_B t18_average
    simp only [coin, ite_true]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases h : z i <;> simp [bit, h]
  have hB0 : t18_B p R false z =
      (∑ i, (1-bit (z i))*(R i z-barMu (fun _ => p) R false))/((N : ℝ)*(1-p)) := by
    unfold t18_B t18_average
    simp only [coin, Bool.false_eq_true, ite_false]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases h : z i <;> simp [bit, h]
  have hr := hajek_ratio_identity p R z hN hp h1 h0
  change hajek R z-ame (fun _ => p) R = _ ∧
    linearHajek (fun _ => p) R z-ame (fun _ => p) R = _ at hr
  have hr1 : hajek R z-ame (fun _ => p) R =
      t18_B p R true z/t18_C (N := N) p true z-t18_B p R false z/t18_C (N := N) p false z := by
    simpa only [hB1, hB0, t18_C, coin, Bool.false_eq_true, ite_true, ite_false] using hr.1
  have hr0 : linearHajek (fun _ => p) R z-ame (fun _ => p) R =
      t18_B p R true z-t18_B p R false z := by
    simpa only [hB1, hB0] using hr.2
  have hrem : hajek R z-linearHajek (fun _ => p) R z =
      t18_B p R true z*(1/t18_C (N := N) p true z-1) -
      t18_B p R false z*(1/t18_C (N := N) p false z-1) := by
    simp only [mul_sub, mul_one, mul_one_div]
    linarith
  have hinv (c : ℝ) (hc : 1/2 ≤ c) : |1/c-1| ≤ 2*|c-1| := by
    have hcp : 0 < c := by linarith
    have he : 1/c-1 = -(c-1)/c := by field_simp [hcp.ne']; ring
    rw [he, abs_div, abs_neg, abs_of_pos hcp]
    apply (div_le_iff₀ hcp).mpr
    have hm := mul_le_mul_of_nonneg_right hc (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg (c-1)))
    nlinarith
  rw [hrem]
  calc
    _ ≤ |t18_B p R true z*(1/t18_C (N := N) p true z-1)| +
        |t18_B p R false z*(1/t18_C (N := N) p false z-1)| := abs_sub _ _
    _ ≤ |t18_B p R true z| *(2*|t18_C (N := N) p true z-1|) +
        |t18_B p R false z| *(2*|t18_C (N := N) p false z-1|) := by
      simp only [abs_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hinv _ hc1) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hinv _ hc0) (abs_nonneg _))
    _ ≤ t18_Q p R z := by
      unfold t18_Q
      nlinarith [sq_nonneg (|t18_B p R true z|-|t18_C (N := N) p true z-1|),
        sq_nonneg (|t18_B p R false z|-|t18_C (N := N) p false z-1|),
        sq_abs (t18_B p R true z), sq_abs (t18_B p R false z),
        sq_abs (t18_C (N := N) p true z-1), sq_abs (t18_C (N := N) p false z-1)]

lemma t18_Q_moment {N : ℕ} (p b : ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (D : ℕ)
    (hp : 0 < p ∧ p < 1) (hb : 0 ≤ b) (hN : 0 < N)
    (hR : ∀ i z, |R i z| ≤ b) (hdeg : ∀ i, (B i).card ≤ D)
    (hout : ∀ i j, j ∉ B i → ¬ sharesSource R i j) :
    expect (fun _ => p) (t18_Q p R) ≤
      ((D : ℝ)*(2*b/p)^2 + (D : ℝ)*(2*b/(1-p))^2 +
        (D : ℝ)*(1/p)^2 + (D : ℝ)*(1/(1-p))^2)/N := by
  have h1 := t18_arm_moments p b R B D hp hb hN hR hdeg hout true
  have h0 := t18_arm_moments p b R B D hp hb hN hR hdeg hout false
  simp only [coin, Bool.false_eq_true, ite_true, ite_false] at h1 h0
  unfold t18_Q
  rw [expect_add, expect_add, expect_add]
  simp only [add_div]
  linarith [h1.1, h1.2, h0.1, h0.2]

lemma t18_bigop_rootn (p : ∀ N, Fin N → ℝ) (hp : ∀ N i, 0 < p N i ∧ p N i < 1)
    (U : ∀ N, Assignment N → ℝ)
    (hU : BigOp p U (fun N => (N : ℝ)⁻¹)) :
    InProb p (fun N z => Real.sqrt N * (-U N z)) := by
  intro ε hε
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun N =>
      ha.trans_le (t18_prob_nonneg (p N) (hp N) _))
  · intro η hη
    obtain ⟨C, hC, htail⟩ := hU η hη
    have hbase : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hscale : Tendsto (fun N : ℕ => Real.sqrt N*(C*(N : ℝ)⁻¹)) atTop (nhds 0) := by
      have hh : Tendsto (fun N : ℕ => C*Real.sqrt ((N : ℝ)⁻¹)) atTop (nhds 0) := by
        simpa only [Real.sqrt_zero, mul_zero] using (hbase.sqrt).const_mul C
      apply hh.congr'
      exact Filter.Eventually.of_forall (fun N => by
        dsimp only
        rw [Real.sqrt_inv]
        calc
          C*(Real.sqrt (N : ℝ))⁻¹ = C*(Real.sqrt (N : ℝ)/(N : ℝ)) := by
            rw [Real.sqrt_div_self]
          _ = Real.sqrt (N : ℝ)*(C*(N : ℝ)⁻¹) := by ring)
    filter_upwards [htail, hscale.eventually (eventually_lt_nhds hε)] with N ht hs
    apply lt_of_le_of_lt (t18_prob_mono (p N) (hp N) _ _ ?_) ht
    intro z hz
    rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
    by_contra hnot
    have hu : |U N z| ≤ C*(N : ℝ)⁻¹ := le_of_not_gt hnot
    have hmul := mul_le_mul_of_nonneg_left hu (Real.sqrt_nonneg (N : ℝ))
    have he : |Real.sqrt (N : ℝ)*(-U N z)| = Real.sqrt (N : ℝ)*|U N z| := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_neg]
    rw [he] at hz
    linarith

/-- T18: the Hájek linearization remainder satisfies both stochastic rate bounds. -/
theorem hajek_linearization_proof (P : PopulationSequence Space) (p d : ℝ)
    (hp : 0 < p ∧ p < 1) (hd : 0 ≤ d) (hP : SpatialLocalConditions P)
    (hWD : ∀ᶠ N in atTop, WellDefined (P N) d) :
    let R := circleSequence P d
    let π := fun N (_ : Fin N) => p
    InProb π (fun N z => Real.sqrt N*(linearHajek (π N) (R N) z-hajek (R N) z)) ∧
    BigOp π (fun N z => hajek (R N) z-linearHajek (π N) (R N) z) (fun N => (N : ℝ)⁻¹) := by
  dsimp only
  obtain ⟨b, hb, hbout⟩ := hP.1
  obtain ⟨h, hh, hloc⟩ := hP.2.1
  obtain ⟨c, hc⟩ := hP.2.2
  let D : ℕ := Nat.ceil (c (h d))
  let K : ℝ := (D : ℝ)*(2*b/p)^2 + (D : ℝ)*(2*b/(1-p))^2 +
    (D : ℝ)*(1/p)^2 + (D : ℝ)*(1/(1-p))^2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hm : ∀ᶠ N in atTop,
      expect (fun _ => p) (t18_Q p (circleSequence P d N)) ≤ K/(N : ℝ) := by
    filter_upwards [eventually_gt_atTop 0, hbout, hWD, hloc d hd,
      hc (h d) (hh d hd)] with N hN hbN hwdN hlocN hcN
    have hdeg (i : Fin N) : (ball (nodeSeparation (P N)) i (h d)).card ≤ D := by
      exact_mod_cast (hcN i).trans (Nat.le_ceil (c (h d)))
    have hR : ∀ i z, |circleAverage (P N) d i z| ≤ b :=
      CLTCompletion.circleAverage_abs_le (P N) d b hwdN (fun x z => (hbN x z).le)
    exact t18_Q_moment p b (circleAverage (P N) d)
      (fun i => ball (nodeSeparation (P N)) i (h d)) D hp hb.le hN hR hdeg (by
        intro i j hj
        apply hlocN i j
        simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hj)
  have hO : BigOp (fun N (_ : Fin N) => p)
      (fun N z => hajek (circleSequence P d N) z-
        linearHajek (fun _ => p) (circleSequence P d N) z) (fun N => (N : ℝ)⁻¹) := by
    intro ε hε
    let t : ℝ := K/ε+1
    have ht : 0 < t := by dsimp only [t]; positivity
    have hKt : K/t < ε := by
      apply (div_lt_iff₀ ht).mpr
      dsimp only [t]
      have he : ε*(K/ε) = K := by field_simp [hε.ne']
      nlinarith
    have hlim : Tendsto (fun N : ℕ => t/(N : ℝ)) atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
        (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul t
    refine ⟨t, ht, ?_⟩
    filter_upwards [hm, eventually_gt_atTop 0,
      hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/4))] with N hmN hN hsmall
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have htn : 0 < t/(N : ℝ) := div_pos ht hn
    rw [abs_of_nonneg (inv_nonneg.mpr hn.le)]
    have he : t*(N : ℝ)⁻¹ = t/(N : ℝ) := rfl
    rw [he]
    calc
      _ ≤ prob (fun _ => p) (fun z => t/(N : ℝ) < t18_Q p (circleSequence P d N) z) := by
        apply t18_prob_mono _ (fun _ => hp)
        intro z hz
        by_contra hnot
        have hq : t18_Q p (circleSequence P d N) z ≤ t/(N : ℝ) := le_of_not_gt hnot
        have hr := t18_remainder_bound p (circleSequence P d N) z hp hN
          (hq.trans hsmall.le)
        exact (not_lt_of_ge (hr.trans hq)) hz
      _ ≤ expect (fun _ => p) (t18_Q p (circleSequence P d N))/(t/(N : ℝ)) :=
        t18_markov _ (fun _ => hp) _ (t18_Q_nonneg p _) _ htn
      _ ≤ (K/(N : ℝ))/(t/(N : ℝ)) :=
        div_le_div_of_nonneg_right hmN htn.le
      _ = K/t := by field_simp [hn.ne', ht.ne']
      _ < ε := hKt
  refine ⟨?_, hO⟩
  have hi := t18_bigop_rootn (fun N (_ : Fin N) => p) (fun _ _ => hp) _ hO
  simpa only [neg_sub] using hi

/-! T19: a single fair sign, deterministic other coordinates, and a CDF obstruction. -/

lemma t19_sum {N : ℕ} (hN : 0 < N) (z : Assignment N) :
    (∑ i, loneRademacher N i z) = 2*bit (z ⟨0, hN⟩)-1 := by
  let i0 : Fin N := ⟨0, hN⟩
  have hzero (i : Fin N) (hi : i ≠ i0) : loneRademacher N i z = 0 := by
    have hiv : i.val ≠ 0 := by
      intro hv
      apply hi
      exact Fin.ext hv
    simp only [loneRademacher, if_neg hiv]
  calc
    (∑ i, loneRademacher N i z) = loneRademacher N i0 z :=
      Finset.sum_eq_single i0 (fun i _ hi => hzero i hi) (by simp)
    _ = 2*bit (z ⟨0, hN⟩)-1 := by rfl

lemma t19_mean {N : ℕ} (i : Fin N) :
    expect (fun _ => 1/2) (loneRademacher N i) = 0 := by
  by_cases hi : i.val = 0
  · have he : loneRademacher N i = fun z => 2*bit (z i)-1 := by
      funext z; simp only [loneRademacher, if_pos hi]
    rw [he, t18_expect_coordinate (fun _ => 1/2) i (fun a => 2*bit a-1)]
    norm_num [bit]
  · have he : loneRademacher N i = fun _ => (0 : ℝ) := by
      funext z
      simp [loneRademacher, hi]
    rw [he, expect_const]

lemma t19_variance {N : ℕ} (hN : 0 < N) :
    variance (fun _ => 1/2) (fun z => ∑ i, loneRademacher N i z) = 1 := by
  have hm : expect (fun _ : Fin N => (1/2 : ℝ))
      (fun z => ∑ i, loneRademacher N i z) = 0 := by
    rw [expect_sum]
    simp_rw [t19_mean]
    simp
  have hs : (fun z : Assignment N => (∑ i, loneRademacher N i z)*
      (∑ i, loneRademacher N i z)) = fun _ => (1 : ℝ) := by
    funext z
    simp only [t19_sum hN z]
    cases h : z ⟨0, hN⟩ <;> norm_num [bit, h]
  unfold variance cov
  rw [hs, expect_const, hm]
  norm_num

lemma t19_cdf {N : ℕ} (hN : 0 < N) :
    prob (fun _ => 1/2) (fun z => (∑ i, loneRademacher N i z) ≤ -(1/2 : ℝ)) = 1/2 := by
  have he : (fun z : Assignment N =>
      if (∑ i, loneRademacher N i z) ≤ -(1/2 : ℝ) then (1 : ℝ) else 0) =
      fun z => if z ⟨0, hN⟩ = false then 1 else 0 := by
    funext z
    simp only [t19_sum hN z]
    cases h : z ⟨0, hN⟩ <;> norm_num [bit, h]
  unfold prob
  rw [he, t18_expect_coordinate (fun _ => 1/2) ⟨0, hN⟩
    (fun a => if a = false then 1 else 0)]
  norm_num

lemma t19_family_graph {N : ℕ} (hN : 0 < N) :
    FiniteDependencyGraph (fun _ => 1/2) (loneRademacher N) (fun i => {i}) := by
  let i0 : Fin N := ⟨0, hN⟩
  have hz (I : Finset (Fin N)) (hi : i0 ∉ I) (z : Assignment N) :
      (fun i : I => loneRademacher N i z) = fun _ => 0 := by
    funext i
    have hiv : (i : Fin N).val ≠ 0 := by
      intro hv
      have he : (i : Fin N) = i0 := Fin.ext hv
      exact hi (he ▸ i.property)
    simp only [loneRademacher, if_neg hiv]
  refine ⟨by simp, by simp [eq_comm], ?_⟩
  intro I J hsep A C
  have hij : i0 ∉ I ∨ i0 ∉ J := by
    by_cases hi : i0 ∈ I
    · right
      intro hj
      exact hsep i0 hi i0 hj (by simp)
    · exact Or.inl hi
  rcases hij with hi | hj
  · have he (z : Assignment N) : A (fun i : I => loneRademacher N i z) =
        A (fun _ => 0) := congrArg A (hz I hi z)
    unfold prob
    simp_rw [he]
    by_cases ha : A (fun _ : I => (0 : ℝ))
    · simp only [ha, true_and, ite_true, expect_const, one_mul]
    · simp only [ha, false_and, ite_false, expect_const, zero_mul]
  · have he (z : Assignment N) : C (fun j : J => loneRademacher N j z) =
        C (fun _ => 0) := congrArg C (hz J hj z)
    unfold prob
    simp_rw [he]
    by_cases hc : C (fun _ : J => (0 : ℝ))
    · simp only [hc, and_true, ite_true, expect_const, mul_one]
    · simp only [hc, and_false, ite_false, expect_const, mul_zero]

lemma t19_normal_gap : normalCDF (-(1/2 : ℝ)) < 1/2 := by
  have hm := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf
    (by norm_num : -(1/2 : ℝ) < 0)
  rw [AronowAudit.P053.NormalCompletion.normal_cdf_zero] at hm
  simpa only [ProbabilityTheory.cdf_eq_real, measureReal_def, normalCDF] using hm

/-- T19: the dependency CLT counterexample, with full tuple-event independence. -/
theorem dependency_clt_counterexample_proof :
    (∀ N : ℕ, 0 < N →
      (∀ i z, |loneRademacher N i z| ≤ 1) ∧
      (∀ i, expect (fun _ => 1/2) (loneRademacher N i) = 0) ∧
      (∀ i, expect (fun _ => 1/2) (fun z => (loneRademacher N i z)^4) ≤ 1) ∧
      FiniteDependencyGraph (fun _ => 1/2) (loneRademacher N) (fun i => {i}) ∧
      (∀ i : Fin N, ({i} : Finset (Fin N)).card = 1) ∧
      variance (fun _ => 1/2) (fun z => ∑ i, loneRademacher N i z) = 1 ∧
      prob (fun _ => 1/2) (fun z => (∑ i, loneRademacher N i z) ≤ -(1/2 : ℝ)) = 1/2) ∧
    Tendsto (fun N : ℕ => (1 : ℝ)/N) atTop (nhds 0) ∧
    normalCDF (-(1/2 : ℝ)) < 1/2 ∧
    ¬ NormalLimit (fun _ _ => 1/2) (fun N z =>
      (∑ i, loneRademacher N i z) / Real.sqrt
        (variance (fun _ => 1/2) (fun z' => ∑ i, loneRademacher N i z'))) := by
  refine ⟨?_, ?_, t19_normal_gap, ?_⟩
  · intro N hN
    refine ⟨?_, t19_mean, ?_, t19_family_graph hN, by simp, t19_variance hN, t19_cdf hN⟩
    · intro i z
      by_cases hi : i.val = 0
      · cases h : z i <;> norm_num [loneRademacher, hi, bit, h]
      · simp [loneRademacher, hi]
    · intro i
      have hb (z : Assignment N) : (loneRademacher N i z)^4 ≤ 1 := by
        by_cases hi : i.val = 0
        · cases h : z i <;> norm_num [loneRademacher, hi, bit, h]
        · simp [loneRademacher, hi]
      calc
        _ ≤ expect (fun _ => 1/2) (fun _ => 1) :=
          expect_mono _ (by intro i; norm_num) _ _ hb
        _ = 1 := expect_const _ _
  · simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  · intro hlim
    have hnormal := hlim (-(1/2 : ℝ))
    have he : (fun N => prob (fun _ : Fin N => (1/2 : ℝ)) (fun z =>
        (∑ i, loneRademacher N i z) / Real.sqrt
          (variance (fun _ => 1/2) (fun z' => ∑ i, loneRademacher N i z')) ≤ -(1/2 : ℝ)))
        =ᶠ[atTop] fun _ => (1/2 : ℝ) := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      rw [t19_variance hN, Real.sqrt_one]
      simp only [div_one]
      exact t19_cdf hN
    have hhalf : Tendsto (fun N => prob (fun _ : Fin N => (1/2 : ℝ)) (fun z =>
        (∑ i, loneRademacher N i z) / Real.sqrt
          (variance (fun _ => 1/2) (fun z' => ∑ i, loneRademacher N i z')) ≤ -(1/2 : ℝ)))
        atTop (nhds (1/2 : ℝ)) := tendsto_const_nhds.congr' he.symm
    have heq : normalCDF (-(1/2 : ℝ)) = 1/2 := tendsto_nhds_unique hnormal hhalf
    exact (ne_of_lt t19_normal_gap) heq

end
end AronowAudit.P004.Wave1
