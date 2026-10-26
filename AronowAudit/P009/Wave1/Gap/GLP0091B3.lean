import AronowAudit.P009.P009_BernoulliCompletion

/-! Finite corrected bias bounds (P009-T12). -/
namespace AronowAudit.P009.Wave1
open scoped BigOperators Topology
open Filter BernoulliCompletion
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000



/-- Apply the one-coordinate Bernoulli identity to an arbitrary
outcome function by putting that function at every unit of an experiment. -/
private lemma correctedBias_one_numerator {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i : Fin n) (a : Bool) (f : Assignment n → ℝ) :
    mean E.design (fun z => if z i = a then f z else 0) =
      marginal E i a * mean E.design (fun z => f (Function.update z i a)) := by
  let F : Experiment n := ⟨E.design, fun _ => f⟩
  have hF : Bernoulli F := hb
  have hc := conditional_observed_eq_potential_mean F hF i a
  have hc' : mean E.design (fun z => if z i = a then f z else 0)/marginal E i a =
      mean E.design (fun z => f (Function.update z i a)) := by
    simp only [cmean, potential, F, marginal] at hc
    convert hc using 1 <;> congr 2 <;> funext z <;> split_ifs <;> rfl
  have he := (div_eq_iff (marginal_pos E hb i a).ne').mp hc'
  exact he.trans (mul_comm _ _)

private lemma correctedBias_two_numerator {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (f : Assignment n → ℝ) :
    mean E.design (fun z => if z i = a ∧ z j = b then f z else 0) =
      (marginal E i a*marginal E j b) *
        mean E.design (fun z => f (Function.update (Function.update z i a) j b)) := by
  have he : (fun z : Assignment n => if z i = a ∧ z j = b then f z else 0) =
      fun z => if z i = a then (if z j = b then f z else 0) else 0 := by
    funext z; split_ifs <;> simp_all
  rw [he, correctedBias_one_numerator E hb i a]
  simp only [Function.update_of_ne (Ne.symm hij)]
  rw [correctedBias_one_numerator E hb j b]
  have hu (z : Assignment n) : Function.update (Function.update z j b) i a =
      Function.update (Function.update z i a) j b := by
    funext l
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
      simp_all [Function.update]
  simp_rw [hu]
  ring

private lemma correctedBias_two_prob {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool) :
    prob E.design (fun z => z i = a ∧ z j = b) = marginal E i a*marginal E j b := by
  have h := correctedBias_two_numerator E hb i j hij a b (fun _ => 1)
  simp only [mean_const, mul_one] at h
  rw [← h]
  unfold prob
  congr 1
  funext z
  split_ifs <;> rfl

private lemma correctedBias_two_cmean {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (f : Assignment n → ℝ) :
    cmean E.design (fun z => z i = a ∧ z j = b) f =
      mean E.design (fun z => f (Function.update (Function.update z i a) j b)) := by
  rw [cmean, correctedBias_two_prob E hb i j hij]
  calc
    _ = (mean E.design (fun z => if z i = a ∧ z j = b then f z else 0)) /
        (marginal E i a*marginal E j b) := by
      congr 1
      congr 1
      funext z
      split_ifs <;> rfl
    _ = _ := by
      rw [correctedBias_two_numerator E hb i j hij]
      exact mul_div_cancel_left₀ _ (mul_ne_zero
        (marginal_pos E hb i a).ne' (marginal_pos E hb j b).ne')


private lemma correctedBias_mean_mono {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (f g : Ω → ℝ) (h : ∀ z, f z ≤ g z) : mean P f ≤ mean P g :=
  Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (h z) (P.nonneg z))

private def correctedBias_condLaw {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (A : Ω → Prop) (hp : 0 < prob P A) : Law Ω where
  mass z := if A z then P.mass z / prob P A else 0
  nonneg z := by
    split_ifs
    · exact div_nonneg (P.nonneg z) hp.le
    · exact le_rfl
  total := by
    have he : (∑ z, if A z then P.mass z / prob P A else 0) =
        prob P A / prob P A := by
      unfold prob mean
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z _
      split_ifs <;> simp_all
    rw [he, div_self hp.ne']

private lemma correctedBias_condLaw_mean {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (A : Ω → Prop) (hp : 0 < prob P A) (f : Ω → ℝ) :
    mean (correctedBias_condLaw P A hp) f = cmean P A f := by
  change (∑ z, (if A z then P.mass z / prob P A else 0)*f z) =
    (∑ z, P.mass z*(if A z then f z else 0))/prob P A
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp_all [div_mul_eq_mul_div]

private lemma correctedBias_ccov_formula {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (A : Ω → Prop) (hp : 0 < prob P A) (f g : Ω → ℝ) :
    ccov P A f g = cmean P A (fun z => f z*g z)-cmean P A f*cmean P A g := by
  have h := covariance_product_formula (correctedBias_condLaw P A hp) f g
  simpa only [cov, correctedBias_condLaw_mean, ccov] using h

private lemma correctedBias_cmean_sq {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (A : Ω → Prop) (hp : 0 < prob P A) (f : Ω → ℝ) :
    (cmean P A f)^2 ≤ cmean P A (fun z => f z^2) := by
  have h := variance_nonnegative (correctedBias_condLaw P A hp) f
  rw [variance_second_moment] at h
  simp only [correctedBias_condLaw_mean] at h
  linarith

private lemma correctedBias_cmean_abs {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (A : Ω → Prop) (hp : 0 < prob P A) (f : Ω → ℝ) (k : ℝ)
    (h2 : cmean P A (fun z => f z^2) ≤ k^4) : |cmean P A f| ≤ k^2 := by
  have h := (correctedBias_cmean_sq P A hp f).trans h2
  nlinarith [sq_abs (cmean P A f), sq_nonneg (|cmean P A f|-k^2)]

private lemma correctedBias_ccov_abs {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (A : Ω → Prop) (hp : 0 < prob P A) (f g : Ω → ℝ) (k : ℝ)
    (hf : cmean P A (fun z => f z^2) ≤ k^4)
    (hg : cmean P A (fun z => g z^2) ≤ k^4) : |ccov P A f g| ≤ k^4 := by
  let Q := correctedBias_condLaw P A hp
  have hvf : var Q f ≤ k^4 := by
    rw [variance_second_moment, correctedBias_condLaw_mean, correctedBias_condLaw_mean]
    nlinarith [sq_nonneg (cmean P A f)]
  have hvg : var Q g ≤ k^4 := by
    rw [variance_second_moment, correctedBias_condLaw_mean, correctedBias_condLaw_mean]
    nlinarith [sq_nonneg (cmean P A g)]
  have hc : cov Q f g = ccov P A f g := by
    simp only [cov, ccov, Q, correctedBias_condLaw_mean]
  rw [← hc]
  apply (covariance_cauchy_schwarz Q f g).trans
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  simpa only [pow_two] using
    (mul_le_mul hvf hvg (variance_nonnegative Q g) (by positivity) :
      var Q f * var Q g ≤ k^4*k^4)

private lemma correctedBias_observed_second {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (i : Fin n) :
    mean E.design (fun z => E.outcome i z^2) ≤ k^2 := by
  have hM : 0 ≤ mean E.design (fun z => Real.rpow |E.outcome i z| q) :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (E.design.nonneg z)
      (Real.rpow_nonneg (abs_nonneg _) _))
  have hq : 0 < q := by linarith [hr.2.1]
  calc
    _ = mean E.design (fun z => |E.outcome i z|^2) := by simp only [sq_abs]
    _ ≤ Real.rpow (mean E.design (fun z => Real.rpow |E.outcome i z| q)) (2/q) :=
      finite_moment_interpolation E.design _ 2 (by omega) q (by simpa using hr.2.1)
    _ ≤ Real.rpow (Real.rpow k q) (2/q) :=
      Real.rpow_le_rpow hM (hr.2.2.2.2.1 i) (by positivity)
    _ = k^2 := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul hr.1.le, mul_div_cancel₀ _ hq.ne']
      norm_num

private lemma correctedBias_cond_second {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (A : Ω → Prop) (hp : 0 < prob P A) (f : Ω → ℝ) (k : ℝ)
    (hm : mean P (fun z => f z^2) ≤ k^2) (hi : (prob P A)⁻¹ ≤ k^2) :
    cmean P A (fun z => f z^2) ≤ k^4 := by
  have hnum : mean P (fun z => if A z then f z^2 else 0) ≤ k^2 := by
    apply le_trans (correctedBias_mean_mono P _ _ _) hm
    intro z
    split_ifs <;> nlinarith [sq_nonneg (f z)]
  calc
    _ ≤ k^2 / prob P A := div_le_div_of_nonneg_right hnum hp.le
    _ ≤ k^2*k^2 := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hi (sq_nonneg k)
    _ = _ := by ring

private lemma correctedBias_pair_inv {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j)
    (a b : Bool) :
    0 < prob E.design (fun z => z i = a ∧ z j = b) ∧
      (prob E.design (fun z => z i = a ∧ z j = b))⁻¹ ≤ k^2 := by
  rw [correctedBias_two_prob E hb i j hij]
  have hi := regular_marginal_bounds E k q s hr i a
  have hj := regular_marginal_bounds E k q s hr j b
  refine ⟨mul_pos hi.2.2.1 hj.2.2.1, ?_⟩
  rw [mul_inv_rev, pow_two]
  exact mul_le_mul hj.2.2.2 hi.2.2.2 (inv_nonneg.mpr hi.2.2.1.le) hr.1.le

private lemma correctedBias_pair_second {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j)
    (a b : Bool) (l : Fin n) :
    cmean E.design (fun z => z i = a ∧ z j = b) (fun z => E.outcome l z^2) ≤ k^4 := by
  have hp := correctedBias_pair_inv E k q s hr hb i j hij a b
  exact correctedBias_cond_second E.design _ hp.1 _ k
    (correctedBias_observed_second E k q s hr l) hp.2

private lemma correctedBias_single_mean {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (i : Fin n) (a : Bool) :
    |cmean E.design (fun z => z i = a) (E.outcome i)| ≤ k^2 := by
  have hk := regular_k_ge_two hn E k q s hr
  have hi := regular_marginal_bounds E k q s hr i a
  have hp : 0 < prob E.design (fun z => z i = a) := hi.2.2.1
  apply correctedBias_cmean_abs E.design _ hp _ k
  apply correctedBias_cond_second E.design _ hp _ k
    (correctedBias_observed_second E k q s hr i)
  change (marginal E i a)⁻¹ ≤ k^2
  exact hi.2.2.2.trans (by nlinarith [sq_nonneg (k-1)])


private lemma correctedBias_pair_mean {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j)
    (a b : Bool) (l : Fin n) :
    |cmean E.design (fun z => z i = a ∧ z j = b) (E.outcome l)| ≤ k^2 :=
  correctedBias_cmean_abs E.design _
    (correctedBias_pair_inv E k q s hr hb i j hij a b).1 _ k
    (correctedBias_pair_second E k q s hr hb i j hij a b l)

private lemma correctedBias_xi_bound {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j)
    (a : Bool) : |xi E i j a| ≤ 2*k^2 := by
  have ht := correctedBias_pair_mean E k q s hr hb i j hij a true i
  have hf := correctedBias_pair_mean E k q s hr hb i j hij a false i
  rw [correctedBias_two_cmean E hb i j hij] at ht hf
  unfold xi
  rw [mean_sub]
  calc
    _ ≤ |mean E.design (fun z => E.outcome i
        (Function.update (Function.update z i a) j true))| +
        |mean E.design (fun z => E.outcome i
        (Function.update (Function.update z i a) j false))| := abs_sub _ _
    _ ≤ k^2+k^2 := add_le_add ht hf
    _ = _ := by ring

private lemma correctedBias_convex_abs (p x y K : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hx : |x| ≤ K) (hy : |y| ≤ K) : |(1-p)*x+p*y| ≤ K := by
  calc
    _ ≤ |(1-p)*x|+|p*y| := abs_add_le _ _
    _ = (1-p)*|x|+p*|y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg (sub_nonneg.mpr hp1)]
    _ ≤ (1-p)*K+p*K := add_le_add
      (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hp1))
      (mul_le_mul_of_nonneg_left hy hp)
    _ = _ := by ring

private lemma correctedBias_xiBreve_bound {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) :
    |xiBreve E i j| ≤ 2*k^2 := by
  unfold xiBreve
  exact correctedBias_convex_abs _ _ _ _ (hb.1 i).1.le (hb.1 i).2.le
    (correctedBias_xi_bound E k q s hr hb i j hij true)
    (correctedBias_xi_bound E k q s hr hb i j hij false)

private lemma correctedBias_yBreve_bound {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (hb : Bernoulli E) (i : Fin n) :
    |yBreve E i| ≤ k^2 := by
  unfold yBreve
  exact correctedBias_convex_abs _ _ _ _ (hb.1 i).1.le (hb.1 i).2.le
    (correctedBias_single_mean hn E k q s hr i true)
    (correctedBias_single_mean hn E k q s hr i false)

private lemma correctedBias_B1_summand {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (hb : Bernoulli E) (i j : Fin n)
    (hij : i ≠ j) :
    |xiBreve E i j*xiBreve E j i +
      2*yBreve E j*(xi E i j true-xi E i j false)| ≤ 12*k^4 := by
  have hx := correctedBias_xiBreve_bound E k q s hr hb i j hij
  have hy := correctedBias_xiBreve_bound E k q s hr hb j i hij.symm
  have hz := correctedBias_yBreve_bound hn E k q s hr hb j
  have hd : |xi E i j true-xi E i j false| ≤ 4*k^2 := by
    exact (abs_sub _ _).trans (by
      have ht := correctedBias_xi_bound E k q s hr hb i j hij true
      have hf := correctedBias_xi_bound E k q s hr hb i j hij false
      linarith)
  calc
    _ ≤ |xiBreve E i j*xiBreve E j i| +
        |2*yBreve E j*(xi E i j true-xi E i j false)| := abs_add_le _ _
    _ = |xiBreve E i j| * |xiBreve E j i| +
        2*|yBreve E j| * |xi E i j true-xi E i j false| := by
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ (2*k^2)*(2*k^2)+(2*k^2)*(4*k^2) := add_le_add
      (mul_le_mul hx hy (abs_nonneg _) (by positivity))
      (mul_le_mul (mul_le_mul_of_nonneg_left hz (by norm_num)) hd
        (abs_nonneg _) (by positivity))
    _ = _ := by ring

private lemma correctedBias_B1_support {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (hb : Bernoulli E) (i j : Fin n) :
    |(if j = i then 0 else xiBreve E i j*xiBreve E j i +
      2*yBreve E j*(xi E i j true-xi E i j false))| ≤
      (12*k^4)*(if j = i then 0 else I E j i) := by
  by_cases hji : j = i
  · simp [hji]
  · by_cases hI : Interferes E j i
    · simpa only [hji, ite_false, I, hI, ite_true, mul_one] using
        correctedBias_B1_summand hn E k q s hr hb i j (Ne.symm hji)
    · have hx := no_interference_zero_spillover E j i hji hI
      simp only [hji, ite_false, xiBreve, hx.2.1, hx.2.2, mul_zero, add_zero,
        sub_self, zero_add, zero_mul, I, hI, abs_zero, le_refl]

private lemma correctedBias_offdiag_sum {n : ℕ} (M : Fin n → Fin n → ℝ)
    (hdiag : ∀ i, M i i = 1) :
    (∑ i, ∑ j, if j = i then 0 else M i j) = (∑ i, ∑ j, M i j)-(n:ℝ) := by
  have he (i j : Fin n) : (if j = i then 0 else M i j) =
      M i j-(if j = i then 1 else 0) := by
    by_cases h : j = i
    · subst j; simp [hdiag]
    · simp [h]
  simp only [he, Finset.sum_sub_distrib]
  simp

private lemma correctedBias_direct_count {n : ℕ} (hn : 0 < n) (E : Experiment n) :
    (∑ i, ∑ j, if j = i then 0 else I E j i) = (n:ℝ)*(C1 E-1) := by
  rw [correctedBias_offdiag_sum _ (fun i => if_pos (Or.inl rfl)), Finset.sum_comm]
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold C1 outgoing
  field_simp
  <;> ring

private lemma correctedBias_dependent_count {n : ℕ} (hn : 0 < n) (E : Experiment n) :
    (∑ i, ∑ j, if j = i then 0 else d E i j) = (n:ℝ)*(dAvg E-1) := by
  rw [correctedBias_offdiag_sum _ (fun i => if_pos ⟨i, Or.inl rfl, Or.inl rfl⟩)]
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold dAvg degree
  field_simp
  <;> ring

private lemma correctedBias_B1_bound {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (hb : Bernoulli E) :
    |B1 E| ≤ 12*k^4*(C1 E-1)/dAvg E := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hd : 0 < dAvg E := zero_lt_one.trans_le (average_degree_at_least_one E hn)
  unfold B1
  rw [abs_div, abs_of_pos (mul_pos hnR hd)]
  calc
    _ ≤ (∑ i, ∑ j, (12*k^4)*(if j = i then 0 else I E j i))/((n:ℝ)*dAvg E) := by
      apply div_le_div_of_nonneg_right _ (mul_pos hnR hd).le
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j _ => correctedBias_B1_support hn E k q s hr hb i j))
    _ = (12*k^4)*((n:ℝ)*(C1 E-1))/((n:ℝ)*dAvg E) := by
      simp only [← Finset.mul_sum, correctedBias_direct_count hn E]
    _ = _ := by field_simp <;> ring

private lemma correctedBias_updated_depends {n : ℕ} (E : Experiment n) (l i j : Fin n)
    (a b : Bool) :
    DependsOn (fun z => E.outcome l (Function.update (Function.update z i a) j b))
      {r | Interferes E r l} := by
  intro z z' hz
  apply outcome_dependsOn E l
  intro r hr
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    simp_all [Function.update]

private lemma correctedBias_ccov_nonedge {n : ℕ} (E : Experiment n) (hb : Bernoulli E)
    (i j : Fin n) (hij : i ≠ j) (hD : ¬ Dependent E i j) (a b : Bool) :
    ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j) = 0 := by
  have hp : 0 < prob E.design (fun z => z i = a ∧ z j = b) := by
    rw [correctedBias_two_prob E hb i j hij]
    exact mul_pos (marginal_pos E hb i a) (marginal_pos E hb j b)
  rw [correctedBias_ccov_formula _ _ hp]
  simp only [correctedBias_two_cmean E hb i j hij]
  have hg : DependsOn
      (fun z => E.outcome j (Function.update (Function.update z i a) j b))
      {r | Interferes E r i}ᶜ := by
    apply DependsOn.mono _ (correctedBias_updated_depends E j i j a b)
    intro r hr hi
    exact hD ⟨r, hi, hr⟩
  rw [mean_product_of_dependsOn E hb _ _ _
    (correctedBias_updated_depends E i i j a b) hg, sub_self]

private lemma correctedBias_ccov_bound {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j)
    (a b : Bool) :
    |ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j)| ≤ k^4 :=
  correctedBias_ccov_abs E.design _
    (correctedBias_pair_inv E k q s hr hb i j hij a b).1 _ _ k
    (correctedBias_pair_second E k q s hr hb i j hij a b i)
    (correctedBias_pair_second E k q s hr hb i j hij a b j)

private lemma correctedBias_signed_ccov_bound {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j)
    (a b : Bool) :
    |(1-2*bit a)*(1-2*bit b)*
      ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j)| ≤ k^4 := by
  have hs (c : Bool) : |1-2*bit c| = 1 := by cases c <;> norm_num [bit]
  simpa only [abs_mul, hs, one_mul] using
    correctedBias_ccov_bound E k q s hr hb i j hij a b

private lemma correctedBias_B2_support {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (hb : Bernoulli E) (i j : Fin n) :
    |(if j = i then 0 else ∑ a : Bool, ∑ b : Bool,
      (1-2*bit a)*(1-2*bit b)*
        ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j))| ≤
      (4*k^4)*(if j = i then 0 else d E i j) := by
  by_cases hji : j = i
  · simp [hji]
  · by_cases hD : Dependent E i j
    · simp only [hji, ite_false, d, hD, ite_true, mul_one]
      calc
        _ ≤ ∑ a : Bool, ∑ b : Bool,
            |(1-2*bit a)*(1-2*bit b)*
              ccov E.design (fun z => z i = a ∧ z j = b)
                (E.outcome i) (E.outcome j)| := by
          apply (Finset.abs_sum_le_sum_abs _ _).trans
          exact Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
        _ ≤ ∑ _a : Bool, ∑ _b : Bool, k^4 :=
          Finset.sum_le_sum (fun a _ => Finset.sum_le_sum
            (fun b _ => correctedBias_signed_ccov_bound E k q s hr hb i j (Ne.symm hji) a b))
        _ = _ := by simp [Fintype.sum_bool]; ring
    · simp only [hji, ite_false, correctedBias_ccov_nonedge E hb i j (Ne.symm hji) hD,
        mul_zero, Finset.sum_const_zero, abs_zero, d, hD, mul_zero, le_refl]

private lemma correctedBias_B2_bound {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (hb : Bernoulli E) :
    |B2 E| ≤ 4*k^4*(dAvg E-1)/dAvg E := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hd : 0 < dAvg E := zero_lt_one.trans_le (average_degree_at_least_one E hn)
  unfold B2
  rw [abs_div, abs_of_pos (mul_pos hnR hd)]
  calc
    _ ≤ (∑ i, ∑ j, (4*k^4)*(if j = i then 0 else d E i j))/((n:ℝ)*dAvg E) := by
      apply div_le_div_of_nonneg_right _ (mul_pos hnR hd).le
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j _ => correctedBias_B2_support E k q s hr hb i j))
    _ = (4*k^4)*((n:ℝ)*(dAvg E-1))/((n:ℝ)*dAvg E) := by
      simp only [← Finset.mul_sum, correctedBias_dependent_count hn E]
    _ = _ := by field_simp <;> ring

private lemma correctedBias_msq_bound {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (hb : Bernoulli E) :
    0 ≤ msq E ∧ msq E ≤ 4*k^4 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hmean (i : Fin n) : |mean E.design (effect E i)| ≤ 2*k^2 := by
    have ht := correctedBias_single_mean hn E k q s hr i true
    have hf := correctedBias_single_mean hn E k q s hr i false
    rw [conditional_observed_eq_potential_mean E hb] at ht hf
    change |mean E.design (fun z => potential E i true z-potential E i false z)| ≤ _
    rw [mean_sub]
    exact (abs_sub _ _).trans (by linarith)
  have hsq (i : Fin n) : mean E.design (effect E i)^2 ≤ 4*k^4 := by
    have h := sq_le_sq₀ (abs_nonneg (mean E.design (effect E i)))
      (by positivity : 0 ≤ 2*k^2)
    have hh := h.mpr (hmean i)
    nlinarith [sq_abs (mean E.design (effect E i))]
  unfold msq
  refine ⟨div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hnR.le, ?_⟩
  apply (div_le_iff₀ hnR).2
  calc
    _ ≤ ∑ _i : Fin n, 4*k^4 := Finset.sum_le_sum (fun i _ => hsq i)
    _ = _ := by simp; ring

/-- T12: the finite upper bounds, with every published hypothesis retained. -/
theorem corrected_bias_term_bounds_proof {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hReg : Regular E k q s) (hQ : 4 ≤ q) (hBER : Bernoulli E) :
    |B1 E| ≤ 12*k^4*(C1 E-1)/dAvg E ∧
    |B2 E| ≤ 4*k^4*(dAvg E-1)/dAvg E ∧ |B2 E| ≤ 4*k^4 ∧
    0 ≤ msq E ∧ msq E ≤ 4*k^4 := by
  have hB2 := correctedBias_B2_bound hn E k q s hReg hBER
  have hd : 0 < dAvg E := zero_lt_one.trans_le (average_degree_at_least_one E hn)
  refine ⟨correctedBias_B1_bound hn E k q s hReg hBER, hB2, ?_,
    correctedBias_msq_bound hn E k q s hReg hBER⟩
  apply hB2.trans
  apply (div_le_iff₀ hd).2
  nlinarith [pow_nonneg (sq_nonneg k) 2]

end
end AronowAudit.P009.Wave1
