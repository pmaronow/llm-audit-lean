import AronowAudit.P009.P009_OneSourceCompletion

namespace AronowAudit.P009.Wave1

open scoped BigOperators
open Filter

noncomputable section

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

-- The following two update identities specialize the finite Bernoulli
-- numerator formulas to the fair law.
lemma oneSourceFormulas_one_numerator (n : ℕ) (i : Fin n) (a : Bool)
    (f : Assignment n → ℝ) :
    mean (fairLaw n) (fun z => if z i = a then f z else 0) =
      (1 / 2) * mean (fairLaw n) (fun z => f (Function.update z i a)) := by
  let E : Experiment n := fairExperiment n (fun _ => f)
  have hc := BernoulliCompletion.conditional_observed_eq_potential_mean E
    (SparseCompletion.fair_BER _ _) i a
  have hc' : mean (fairLaw n) (fun z => if z i = a then f z else 0) / marginal E i a =
      mean (fairLaw n) (fun z => f (Function.update z i a)) := by
    simp only [cmean, potential, E, fairExperiment, marginal] at hc
    convert hc using 1 <;> congr 2 <;> funext z <;> split_ifs <;> rfl
  change mean (fairLaw n) (fun z => if z i = a then f z else 0) /
    marginal (fairExperiment n (fun _ => f)) i a = _ at hc'
  rw [SparseCompletion.fair_marginal] at hc'
  linarith

lemma oneSourceFormulas_average (n : ℕ) (i : Fin n) (f : Assignment n → ℝ) :
    mean (fairLaw n) f = mean (fairLaw n) (fun z =>
      (f (Function.update z i true) + f (Function.update z i false)) / 2) := by
  have he : f = fun z => (if z i = true then f z else 0) +
      (if z i = false then f z else 0) := by
    funext z
    cases z i <;> simp
  calc
    _ = mean (fairLaw n) (fun z => if z i = true then f z else 0) +
        mean (fairLaw n) (fun z => if z i = false then f z else 0) := by
      rw [← mean_add, ← he]
    _ = _ := by
      rw [oneSourceFormulas_one_numerator, oneSourceFormulas_one_numerator,
        mean_div, mean_add]
      ring

lemma oneSourceFormulas_two_numerator (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (a b : Bool) (f : Assignment n → ℝ) :
    mean (fairLaw n) (fun z => if z i = a ∧ z j = b then f z else 0) =
      (1 / 4) * mean (fairLaw n)
        (fun z => f (Function.update (Function.update z i a) j b)) := by
  have he : (fun z : Assignment n => if z i = a ∧ z j = b then f z else 0) =
      fun z => if z i = a then (if z j = b then f z else 0) else 0 := by
    funext z
    split_ifs <;> simp_all
  rw [he, oneSourceFormulas_one_numerator]
  simp only [Function.update_of_ne (Ne.symm hij)]
  rw [oneSourceFormulas_one_numerator]
  have hu (z : Assignment n) : Function.update (Function.update z j b) i a =
      Function.update (Function.update z i a) j b := by
    exact Function.update_comm (Ne.symm hij) _ _ _
  simp_rw [hu]
  ring

lemma oneSourceFormulas_two_prob (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (a b : Bool) :
    prob (fairLaw n) (fun z => z i = a ∧ z j = b) = 1 / 4 := by
  have h := oneSourceFormulas_two_numerator n i j hij a b (fun _ => 1)
  simp only [mean_const, mul_one] at h
  rw [← h]
  unfold prob
  congr 1
  funext z
  split_ifs <;> rfl

lemma oneSourceFormulas_two_cmean (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (a b : Bool) (f : Assignment n → ℝ) :
    cmean (fairLaw n) (fun z => z i = a ∧ z j = b) f =
      mean (fairLaw n) (fun z => f (Function.update (Function.update z i a) j b)) := by
  rw [cmean, oneSourceFormulas_two_prob n i j hij]
  calc
    _ = (mean (fairLaw n) (fun z => if z i = a ∧ z j = b then f z else 0)) /
        (1 / 4) := by
      congr 1
      congr 1
      funext z
      split_ifs <;> rfl
    _ = _ := by rw [oneSourceFormulas_two_numerator n i j hij]; ring

lemma oneSourceFormulas_two_ccov (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (a b : Bool) (f g : Assignment n → ℝ) :
    ccov (fairLaw n) (fun z => z i = a ∧ z j = b) f g =
      cov (fairLaw n)
        (fun z => f (Function.update (Function.update z i a) j b))
        (fun z => g (Function.update (Function.update z i a) j b)) := by
  unfold ccov cov
  simp only [oneSourceFormulas_two_cmean n i j hij]

lemma oneSourceFormulas_outcome {n : ℕ} (hn : 0 < n) (b : ℕ) (c : Fin n → ℝ)
    (i : Fin n) (z : Assignment n) :
    oneSourceOutcome b c i z =
      if 0 < i.val ∧ i.val < b then 2 * bit (z ⟨0, hn⟩) * bit (z i) + c i
      else bit (z i) + c i := by
  unfold oneSourceOutcome
  split_ifs <;> rfl

lemma oneSourceFormulas_effect_mean {n : ℕ} (hn : 0 < n) (b : ℕ)
    (c : Fin n → ℝ) (i : Fin n) :
    mean (fairLaw n) (effect (fairExperiment n (oneSourceOutcome b c)) i) = 1 := by
  by_cases hi : 0 < i.val ∧ i.val < b
  · have hio : (⟨0, hn⟩ : Fin n) ≠ i := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_mk] at this
      omega
    have he : effect (fairExperiment n (oneSourceOutcome b c)) i =
        fun z => 2 * bit (z ⟨0, hn⟩) := by
      funext z
      simp [effect, potential, fairExperiment, oneSourceFormulas_outcome hn,
        hi, Function.update_of_ne hio, bit]
    rw [he, SparseCompletion.fair_coordinate n ⟨0, hn⟩ (fun a => 2 * bit a)]
    norm_num [bit]
  · have he : effect (fairExperiment n (oneSourceOutcome b c)) i = fun _ => 1 := by
      funext z
      simp [effect, potential, fairExperiment, oneSourceFormulas_outcome hn, hi, bit]
    rw [he, mean_const]

lemma oneSourceFormulas_msq {n : ℕ} (hn : 0 < n) (b : ℕ) (c : Fin n → ℝ) :
    msq (fairExperiment n (oneSourceOutcome b c)) = 1 := by
  change (∑ i, mean (fairLaw n)
    (effect (fairExperiment n (oneSourceOutcome b c)) i) ^ 2) / n = 1
  simp_rw [oneSourceFormulas_effect_mean hn]
  simp [ne_of_gt hn]

lemma oneSourceFormulas_ccov {n : ℕ} (hn : 0 < n) (b : ℕ) (c : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (a d : Bool) :
    ccov (fairLaw n) (fun z => z i = a ∧ z j = d)
      (oneSourceOutcome b c i) (oneSourceOutcome b c j) =
      (if 0 < i.val ∧ i.val < b then (1 : ℝ) else 0) *
      (if 0 < j.val ∧ j.val < b then (1 : ℝ) else 0) * bit a * bit d := by
  rw [oneSourceFormulas_two_ccov n i j hij, BernoulliCompletion.covariance_product_formula]
  by_cases hi : 0 < i.val ∧ i.val < b <;>
    by_cases hj : 0 < j.val ∧ j.val < b
  · have hoi : (⟨0, hn⟩ : Fin n) ≠ i := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_mk] at this
      omega
    have hoj : (⟨0, hn⟩ : Fin n) ≠ j := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_mk] at this
      omega
    simp only [oneSourceFormulas_outcome hn, hi, hj, if_true,
      Function.update_self, Function.update_of_ne hij, Function.update_of_ne hoi,
      Function.update_of_ne hoj, one_mul, and_self]
    rw [SparseCompletion.fair_coordinate n ⟨0, hn⟩
        (fun t => (2 * bit t * bit a + c i) * (2 * bit t * bit d + c j)),
      SparseCompletion.fair_coordinate n ⟨0, hn⟩ (fun t => 2 * bit t * bit a + c i),
      SparseCompletion.fair_coordinate n ⟨0, hn⟩ (fun t => 2 * bit t * bit d + c j)]
    cases a <;> cases d <;> norm_num [bit] <;> ring
  all_goals
    simp only [oneSourceFormulas_outcome hn, hi, hj, if_true, if_false,
      Function.update_self, Function.update_of_ne hij, zero_mul, mul_zero,
      mean_const, and_self]
    first
    | exact sub_self _
    | rw [mean_const_mul]; ring
    | simp_rw [mul_comm _ (bit d + c j)]; rw [mean_const_mul]; ring

def oneSourceFormulas_U {n : ℕ} (b : ℕ) (c : Fin n → ℝ)
    (i : Fin n) (z : Assignment n) : ℝ :=
  2 * (2 * bit (z i) - 1) * oneSourceOutcome b c i z

lemma oneSourceFormulas_U_mean {n : ℕ} (hn : 0 < n) (b : ℕ)
    (c : Fin n → ℝ) (i : Fin n) :
    mean (fairLaw n) (oneSourceFormulas_U b c i) = 1 := by
  rw [oneSourceFormulas_average n i, oneSourceFormulas_average n ⟨0, hn⟩]
  by_cases hi : 0 < i.val ∧ i.val < b
  · have hoi : (⟨0, hn⟩ : Fin n) ≠ i := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_mk] at this
      omega
    simp [oneSourceFormulas_U, oneSourceFormulas_outcome hn, hi,
      Function.update_apply, hoi, hoi.symm, bit, mean_add, mean_div,
      mean_const_mul, mean_const]
    ring
  · simp [oneSourceFormulas_U, oneSourceFormulas_outcome hn, hi,
      Function.update_apply, bit, mean_add, mean_div, mean_const_mul, mean_const]
    ring

def oneSourceFormulas_w {n : ℕ} (b : ℕ) (i : Fin n) : ℝ :=
  if 0 < i.val ∧ i.val < b then 1 else 0

lemma oneSourceFormulas_w_sum {n : ℕ} (hn : 0 < n) (b : ℕ)
    (hb : 1 ≤ b ∧ b ≤ n) :
    (∑ i : Fin n, oneSourceFormulas_w b i) = (b : ℝ) - 1 :=
  OneSourceCompletion.source_count_affected hn b hb

lemma oneSourceFormulas_w_sq {n : ℕ} (b : ℕ) (i : Fin n) :
    oneSourceFormulas_w b i * oneSourceFormulas_w b i = oneSourceFormulas_w b i := by
  unfold oneSourceFormulas_w
  split_ifs <;> norm_num

lemma oneSourceFormulas_offdiag_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ι → ℝ) :
    (∑ i, ∑ j, if j = i then 0 else F i j) =
      (∑ i, ∑ j, F i j) - ∑ i, F i i := by
  have he (i j : ι) : (if j = i then 0 else F i j) =
      F i j - if j = i then F i i else 0 := by
    by_cases h : j = i <;> simp [h]
  simp_rw [he, Finset.sum_sub_distrib]
  simp

lemma oneSourceFormulas_pairs {n : ℕ} (hn : 0 < n) (b : ℕ)
    (hb : 1 ≤ b ∧ b ≤ n) :
    (∑ i : Fin n, ∑ j : Fin n, if j = i then 0 else
      oneSourceFormulas_w b i * oneSourceFormulas_w b j) =
      ((b : ℝ) - 1) * ((b : ℝ) - 2) := by
  rw [oneSourceFormulas_offdiag_sum]
  simp_rw [← Finset.mul_sum, oneSourceFormulas_w_sq]
  rw [← Finset.sum_mul, oneSourceFormulas_w_sum hn b hb]
  ring

lemma oneSourceFormulas_B2 {n : ℕ} (hn : 0 < n) (b : ℕ)
    (hb : 1 ≤ b ∧ b ≤ n) (c : Fin n → ℝ) :
    B2 (fairExperiment n (oneSourceOutcome b c)) =
      ((b : ℝ) - 1) * ((b : ℝ) - 2) / ((n : ℝ) + (b : ℝ) * ((b : ℝ) - 1)) := by
  have he (i j : Fin n) : (if j = i then 0 else
      ∑ a : Bool, ∑ d : Bool, (1 - 2 * bit a) * (1 - 2 * bit d) *
        ccov (fairLaw n) (fun z => z i = a ∧ z j = d)
          (oneSourceOutcome b c i) (oneSourceOutcome b c j)) =
      if j = i then 0 else oneSourceFormulas_w b i * oneSourceFormulas_w b j := by
    by_cases hij : i = j
    · simp [hij]
    · simp only [(Ne.symm hij), if_false, oneSourceFormulas_ccov hn b c i j hij,
        Fintype.sum_bool, bit, Bool.false_eq_true, ite_false, ite_true]
      dsimp [oneSourceFormulas_w]
      ring
  unfold B2
  change (∑ i, ∑ j, if j = i then 0 else
      ∑ a : Bool, ∑ d : Bool, (1 - 2 * bit a) * (1 - 2 * bit d) *
        ccov (fairLaw n) (fun z => z i = a ∧ z j = d)
          (oneSourceOutcome b c i) (oneSourceOutcome b c j)) / _ = _
  simp_rw [he]
  rw [oneSourceFormulas_pairs hn b hb, OneSourceCompletion.source_davg hn b hb c]

-- Averaging the distinct own coordinates and then the source is the finite
-- fair-coordinate orthogonality calculation for the HT contributions.
lemma oneSourceFormulas_cov_offdiag {n : ℕ} (hn : 0 < n) (b : ℕ)
    (c : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    cov (fairLaw n) (oneSourceFormulas_U b c i) (oneSourceFormulas_U b c j) =
      oneSourceFormulas_w b i * oneSourceFormulas_w b j +
      (if i = ⟨0, hn⟩ then 1 else 0) * oneSourceFormulas_w b j *
        (1 + 2 * c ⟨0, hn⟩) +
      (if j = ⟨0, hn⟩ then 1 else 0) * oneSourceFormulas_w b i *
        (1 + 2 * c ⟨0, hn⟩) := by
  rw [BernoulliCompletion.covariance_product_formula,
    oneSourceFormulas_U_mean hn, oneSourceFormulas_U_mean hn]
  by_cases hio : i = (⟨0, hn⟩ : Fin n)
  · subst i
    have hjo := (Ne.symm hij)
    rw [oneSourceFormulas_average n ⟨0, hn⟩, oneSourceFormulas_average n j]
    by_cases hj : 0 < j.val ∧ j.val < b <;>
      simp [oneSourceFormulas_U, oneSourceFormulas_outcome hn, oneSourceFormulas_w,
        hj, hjo, hij, Function.update_apply, bit, mean_const] <;> ring
  · by_cases hjo : j = (⟨0, hn⟩ : Fin n)
    · subst j
      rw [oneSourceFormulas_average n i, oneSourceFormulas_average n ⟨0, hn⟩]
      by_cases hi : 0 < i.val ∧ i.val < b <;>
        simp [oneSourceFormulas_U, oneSourceFormulas_outcome hn, oneSourceFormulas_w,
          hi, hio, (Ne.symm hio), Function.update_apply, bit, mean_const] <;> ring
    · rw [oneSourceFormulas_average n i, oneSourceFormulas_average n j,
        oneSourceFormulas_average n ⟨0, hn⟩]
      by_cases hi : 0 < i.val ∧ i.val < b <;>
        by_cases hj : 0 < j.val ∧ j.val < b <;>
        simp [oneSourceFormulas_U, oneSourceFormulas_outcome hn, oneSourceFormulas_w,
          hi, hj, hio, (Ne.symm hio), hjo, (Ne.symm hjo), hij, (Ne.symm hij),
          Function.update_apply, bit, mean_const] <;> ring

lemma oneSourceFormulas_cov_sum {n : ℕ} (hn : 0 < n) (b : ℕ)
    (hb : 1 ≤ b ∧ b ≤ n) (c : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, if j = i then 0 else
      cov (fairLaw n) (oneSourceFormulas_U b c i) (oneSourceFormulas_U b c j)) =
      2 * ((b : ℝ) - 1) * (1 + 2 * c ⟨0, hn⟩) +
        ((b : ℝ) - 1) * ((b : ℝ) - 2) := by
  let o : Fin n := ⟨0, hn⟩
  let F : Fin n → Fin n → ℝ := fun i j =>
    oneSourceFormulas_w b i * oneSourceFormulas_w b j +
      (if i = o then 1 else 0) * oneSourceFormulas_w b j * (1 + 2 * c o) +
      (if j = o then 1 else 0) * oneSourceFormulas_w b i * (1 + 2 * c o)
  have he (i j : Fin n) : (if j = i then 0 else
      cov (fairLaw n) (oneSourceFormulas_U b c i) (oneSourceFormulas_U b c j)) =
      if j = i then 0 else F i j := by
    by_cases hij : i = j
    · simp [hij]
    · simp only [(Ne.symm hij), if_false, oneSourceFormulas_cov_offdiag hn b c i j hij]
      rfl
  have hd (i : Fin n) : F i i = oneSourceFormulas_w b i := by
    by_cases hi : i = o
    · subst i
      simp [F, o, oneSourceFormulas_w]
    · simp [F, hi, oneSourceFormulas_w_sq]
  simp_rw [he]
  rw [oneSourceFormulas_offdiag_sum]
  simp_rw [hd]
  have hs : (∑ i, ∑ j, F i j) = ((b : ℝ) - 1) ^ 2 +
      2 * ((b : ℝ) - 1) * (1 + 2 * c o) := by
    dsimp [F]
    simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    simp [oneSourceFormulas_w_sum hn b hb]
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul,
      oneSourceFormulas_w_sum hn b hb]
    ring
  rw [hs, oneSourceFormulas_w_sum hn b hb]
  dsimp [o]
  ring

lemma oneSourceFormulas_ht {n : ℕ} (b : ℕ) (c : Fin n → ℝ) :
    ht (fairExperiment n (oneSourceOutcome b c)) =
      fun z => (∑ i, oneSourceFormulas_U b c i z) / n := by
  funext z
  unfold ht muHat
  simp only [SparseCompletion.fair_marginal, ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hzi : z i <;> simp [oneSourceFormulas_U, fairExperiment, hzi, bit] <;> ring

lemma oneSourceFormulas_vBER {n : ℕ} (b : ℕ) (c : Fin n → ℝ) :
    vBER (fairExperiment n (oneSourceOutcome b c)) =
      fun z => (∑ i, (oneSourceFormulas_U b c i z) ^ 2) / (n : ℝ) ^ 2 := by
  funext z
  unfold vBER
  simp only [SparseCompletion.fair_marginal]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hzi : z i <;> simp [oneSourceFormulas_U, fairExperiment, hzi, bit] <;> ring

lemma oneSourceFormulas_variance_gap {n : ℕ} (hn : 0 < n) (b : ℕ)
    (hb : 1 ≤ b ∧ b ≤ n) (c : Fin n → ℝ) :
    let E := fairExperiment n (oneSourceOutcome b c)
    (n : ℝ) ^ 2 * (mean E.design (vBER E) - var E.design (ht E)) =
      n - 2 * ((b : ℝ) - 1) * (1 + 2 * c ⟨0, hn⟩) -
        ((b : ℝ) - 1) * ((b : ℝ) - 2) := by
  dsimp only
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hv : var (fairLaw n) (fun z => ∑ i, oneSourceFormulas_U b c i z) =
      ∑ i, ∑ j, cov (fairLaw n) (oneSourceFormulas_U b c i)
        (oneSourceFormulas_U b c j) := by
    simpa only [one_mul] using (weighted_variance_absolute (fairLaw n)
      (oneSourceFormulas_U b c) (fun _ => 1) 1
      (fun _ => ⟨by norm_num, le_rfl⟩)).1
  have hd : (∑ i : Fin n, cov (fairLaw n) (oneSourceFormulas_U b c i)
      (oneSourceFormulas_U b c i)) =
      (∑ i : Fin n, mean (fairLaw n) (fun z => (oneSourceFormulas_U b c i z) ^ 2)) - n := by
    change (∑ i : Fin n, var (fairLaw n) (oneSourceFormulas_U b c i)) = _
    simp only [variance_second_moment, oneSourceFormulas_U_mean hn,
      one_pow, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hoff := oneSourceFormulas_cov_sum hn b hb c
  rw [oneSourceFormulas_offdiag_sum] at hoff
  rw [hd] at hoff
  rw [oneSourceFormulas_vBER, oneSourceFormulas_ht,
    BernoulliCompletion.variance_div]
  change (n : ℝ) ^ 2 * (mean (fairLaw n)
    (fun z => (∑ i, (oneSourceFormulas_U b c i z) ^ 2) / (n : ℝ) ^ 2) -
    var (fairLaw n) (fun z => ∑ i, oneSourceFormulas_U b c i z) / (n : ℝ) ^ 2) = _
  rw [mean_div, mean_sum, hv]
  field_simp
  nlinarith only [hoff]

lemma oneSourceFormulas_correction_bound (N m : ℝ) (hN : 0 < N) (hm : 0 ≤ m) :
    0 ≤ 2 * m / (N + (m + 1) * m) ∧
      2 * m / (N + (m + 1) * m) ≤ 1 / Real.sqrt N := by
  have hD : 0 < N + (m + 1) * m := by positivity
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsq := Real.sq_sqrt hN.le
  have hpoly : 4 * N * m ^ 2 ≤ (N + (m + 1) * m) ^ 2 := by
    nlinarith [sq_nonneg (N - m ^ 2), mul_nonneg hN.le hm,
      mul_nonneg (sq_nonneg m) hm, sq_nonneg m]
  have hle : 2 * m * Real.sqrt N ≤ N + (m + 1) * m := by
    have hleft : 0 ≤ 2 * m * Real.sqrt N := by positivity
    apply (sq_le_sq₀ hleft hD.le).mp
    calc
      _ = 4 * N * m ^ 2 := by rw [mul_pow, hsq]; ring
      _ ≤ _ := hpoly
  exact ⟨by positivity, (div_le_div_iff₀ hD hs).mpr (by simpa using hle)⟩

theorem corrected_one_source_formulas_proof {n : ℕ} (hn : 0 < n) (b : ℕ)
    (hb : 1 ≤ b ∧ b ≤ n) (c : Fin n → ℝ) :
    let E := fairExperiment n (oneSourceOutcome b c)
    (n:ℝ)*dAvg E = n+(b:ℝ)*((b:ℝ)-1) ∧ msq E = 1 ∧
    B2 E = ((b:ℝ)-1)*((b:ℝ)-2)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) ∧
    B1 E = (2+4*c ⟨0,hn⟩)*((b:ℝ)-1)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) ∧
    (n:ℝ)^2*(mean E.design (vBER E)-var E.design (ht E)) =
      n-2*((b:ℝ)-1)*(1+2*c ⟨0,hn⟩)-((b:ℝ)-1)*((b:ℝ)-2) ∧
    (c ⟨0,hn⟩ = -1/4 →
      msq E/dAvg E-B1 E-B2 E = ((n:ℝ)-((b:ℝ)-1)^2)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) ∧
      (n:ℝ)/dAvg E*(mean E.design (vBER E)-var E.design (ht E)) =
        ((n:ℝ)-((b:ℝ)-1)^2)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1))) ∧
    0 ≤ 2*((b:ℝ)-1)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) ∧
    2*((b:ℝ)-1)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) ≤ 1/Real.sqrt n := by
  let E := fairExperiment n (oneSourceOutcome b c)
  have hgraph := OneSourceCompletion.source_davg hn b hb c
  have hmsq := oneSourceFormulas_msq hn b c
  have hB2 := oneSourceFormulas_B2 hn b hb c
  have hB1 := (OneSourceCompletion.corrected_one_source_spillover_completed hn b hb c).2.2
  have hgap := oneSourceFormulas_variance_gap hn b hb c
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb.1
  have hD : 0 < (n : ℝ) + (b : ℝ) * ((b : ℝ) - 1) := by positivity
  have hd : dAvg E = ((n : ℝ) + (b : ℝ) * ((b : ℝ) - 1)) / n := by
    apply (eq_div_iff hnR.ne').mpr
    dsimp [E]
    linarith [hgraph]
  have hbound := oneSourceFormulas_correction_bound (n : ℝ) ((b : ℝ) - 1)
    hnR (by linarith)
  have hnorm : (n : ℝ) + ((b : ℝ) - 1 + 1) * ((b : ℝ) - 1) =
      (n : ℝ) + (b : ℝ) * ((b : ℝ) - 1) := by ring
  rw [hnorm] at hbound
  refine ⟨hgraph, hmsq, hB2, hB1, hgap, ?_, hbound.1, hbound.2⟩
  intro hc
  constructor
  · change msq E / dAvg E - B1 E - B2 E = _
    rw [hmsq, hB1, hB2, hd, hc]
    field_simp
    ring
  · have hg : (n : ℝ) ^ 2 *
        (mean E.design (vBER E) - var E.design (ht E)) =
        (n : ℝ) - ((b : ℝ) - 1) ^ 2 := by
      dsimp only at hgap
      rw [hc] at hgap
      dsimp [E]
      nlinarith only [hgap]
    change (n : ℝ) / dAvg E *
      (mean E.design (vBER E) - var E.design (ht E)) = _
    rw [hd]
    calc
      _ = ((n : ℝ) ^ 2 * (mean E.design (vBER E) - var E.design (ht E))) /
          ((n : ℝ) + (b : ℝ) * ((b : ℝ) - 1)) := by
        field_simp
      _ = _ := by rw [hg]

end
end AronowAudit.P009.Wave1
