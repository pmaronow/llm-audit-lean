import AronowAudit.P009.P009_BernoulliCompletion
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
Finite variance-bias identities and conservative average-degree inflation bounds.
-/
namespace AronowAudit.P009.Wave1

open scoped BigOperators Topology
open Filter
open BernoulliCompletion

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000

/-! Finite-law algebra, concentration, and exact centering. -/

private lemma variance_bias_limit_d_symm {n : ℕ} (E : Experiment n) (i j : Fin n) :
    d E i j = d E j i := by
  have h : Dependent E i j ↔ Dependent E j i := by
    constructor <;> rintro ⟨l, hl, hr⟩ <;> exact ⟨l, hr, hl⟩
  simp only [d, h]

private lemma variance_bias_limit_degree_one {n : ℕ} (E : Experiment n) (i : Fin n) :
    1 ≤ degree E i := by
  have hd : d E i i = 1 := if_pos ⟨i, Or.inl rfl, Or.inl rfl⟩
  rw [← hd]
  exact Finset.single_le_sum (fun j _ => by unfold d; split_ifs <;> norm_num)
    (Finset.mem_univ i)

private lemma variance_bias_limit_sum_variance {Ω U : Type*} [Fintype Ω] [Fintype U]
    (P : Law Ω) (X : U → Ω → ℝ) :
    var P (fun z => ∑ i, X i z) = ∑ i, ∑ j, cov P (X i) (X j) := by
  simpa only [one_mul] using
    (weighted_variance_absolute P X (fun _ => 1) 1
      (fun _ => ⟨by norm_num, le_rfl⟩)).1

private lemma variance_bias_limit_cov_nonedge {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : ¬ Dependent E i j)
    (f g : Assignment n → ℝ)
    (hf : DependsOn f {l | Interferes E l i})
    (hg : DependsOn g {l | Interferes E l j}) : cov E.design f g = 0 := by
  have hg' : DependsOn g {l | Interferes E l i}ᶜ := by
    apply DependsOn.mono _ hg
    intro l hl hi
    exact hij ⟨l, hi, hl⟩
  rw [covariance_product_formula,
    mean_product_of_dependsOn E hb _ _ _ hf hg', sub_self]

private lemma variance_bias_limit_cov_le_half {Ω : Type*} [Fintype Ω]
    (P : Law Ω) (f g : Ω → ℝ) : cov P f g ≤ (var P f + var P g)/2 := by
  have hvar := variance_nonnegative P (fun z => f z-g z)
  have he : var P (fun z => f z-g z) = var P f+var P g-2*cov P f g := by
    unfold var cov
    rw [mean_sub]
    calc
      _ = mean P (fun z =>
          (f z-mean P f)*(f z-mean P f) +
          (g z-mean P g)*(g z-mean P g) -
          2*((f z-mean P f)*(g z-mean P g))) := by
        congr 1; funext z; ring
      _ = _ := by rw [mean_sub, mean_add, mean_const_mul]
  rw [he] at hvar
  linarith

/-- A graph bound valid for every family with the indicated parent sets. -/
private lemma variance_bias_limit_graph_bound {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (X : Fin n → Assignment n → ℝ)
    (hX : ∀ i, DependsOn (X i) {l | Interferes E l i}) :
    var E.design (fun z => ∑ i, X i z) ≤
      ∑ i, degree E i * var E.design (X i) := by
  have hc (i j : Fin n) : cov E.design (X i) (X j) ≤
      d E i j*((var E.design (X i)+var E.design (X j))/2) := by
    by_cases hij : Dependent E i j
    · simpa only [d, hij, ite_true, one_mul] using
        variance_bias_limit_cov_le_half E.design (X i) (X j)
    · simp only [d, hij, ite_false, zero_mul,
        variance_bias_limit_cov_nonedge E hb i j hij _ _ (hX i) (hX j), le_refl]
  rw [variance_bias_limit_sum_variance]
  calc
    _ ≤ ∑ i, ∑ j, d E i j*((var E.design (X i)+var E.design (X j))/2) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hc i j))
    _ = ((∑ i, ∑ j, d E i j*var E.design (X i)) +
        (∑ i, ∑ j, d E i j*var E.design (X j)))/2 := by
      simp only [← mul_div_assoc, mul_add, ← Finset.sum_div, Finset.sum_add_distrib]
    _ = ∑ i, degree E i*var E.design (X i) := by
      have hs : (∑ i, ∑ j, d E i j*var E.design (X j)) =
          ∑ i, degree E i*var E.design (X i) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [degree, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [variance_bias_limit_d_symm E i j]
      rw [hs]
      simp only [← Finset.sum_mul, degree]
      ring

private def variance_bias_limit_U {n : ℕ} (E : Experiment n) (i : Fin n)
    (z : Assignment n) : ℝ :=
  (if z i then E.outcome i z else 0)/marginal E i true -
    (if z i then 0 else E.outcome i z)/marginal E i false

private lemma variance_bias_limit_U_depends {n : ℕ} (E : Experiment n) (i : Fin n) :
    DependsOn (variance_bias_limit_U E i) {l | Interferes E l i} := by
  intro z z' hz
  have hi := hz i (Or.inl rfl)
  simp only [variance_bias_limit_U, hi, outcome_dependsOn E i hz]

private lemma variance_bias_limit_ht_sum {n : ℕ} (E : Experiment n) :
    ht E = fun z => (∑ i, variance_bias_limit_U E i z)/(n:ℝ) := by
  funext z
  simp only [ht, muHat, variance_bias_limit_U, Finset.sum_sub_distrib, sub_div]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hzi : z i <;> simp [hzi]

private lemma variance_bias_limit_U_mean {n : ℕ} (E : Experiment n) (i : Fin n) :
    mean E.design (variance_bias_limit_U E i) =
      cmean E.design (fun z => z i = true) (E.outcome i) -
      cmean E.design (fun z => z i = false) (E.outcome i) := by
  have he : variance_bias_limit_U E i = fun z =>
      (if z i = true then E.outcome i z else 0)/marginal E i true -
      (if z i = false then E.outcome i z else 0)/marginal E i false := by
    funext z
    cases hzi : z i <;> simp [variance_bias_limit_U, hzi]
  rw [he, mean_sub, mean_div, mean_div]
  simp only [cmean, marginal]
  congr 2 <;> congr 1 <;> funext z <;> split_ifs <;> rfl

/-- This contribution identity requires no Regular assumption. -/
private lemma variance_bias_limit_sigma_identity {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i : Fin n) :
    sigmaSq E i =
      cmean E.design (fun z => z i = true) (fun z => E.outcome i z^2)/marginal E i true +
      cmean E.design (fun z => z i = false) (fun z => E.outcome i z^2)/marginal E i false -
      mean E.design (effect E i)^2 := by
  have hmean : mean E.design (variance_bias_limit_U E i) = mean E.design (effect E i) := by
    rw [variance_bias_limit_U_mean E i, conditional_observed_eq_potential_mean E hb,
      conditional_observed_eq_potential_mean E hb]
    exact (mean_sub E.design _ _).symm
  have hs : (fun z => (variance_bias_limit_U E i z)^2) = fun z =>
      (if z i then E.outcome i z^2 else 0)/(marginal E i true)^2 +
      (if z i then 0 else E.outcome i z^2)/(marginal E i false)^2 := by
    funext z
    cases hzi : z i <;> simp [variance_bias_limit_U, hzi, div_pow]
  change var E.design (variance_bias_limit_U E i) = _
  rw [variance_second_moment, hmean, hs, mean_add, mean_div, mean_div]
  unfold cmean
  have ht : (fun z : Assignment n => if z i = true then E.outcome i z^2 else 0) =
      (fun z => if z i then E.outcome i z^2 else 0) := by
    funext z; cases z i <;> rfl
  have hf : (fun z : Assignment n => if z i = false then E.outcome i z^2 else 0) =
      (fun z => if z i then 0 else E.outcome i z^2) := by
    funext z; cases z i <;> rfl
  simp only [ht, hf]
  change _ = _ / marginal E i true / marginal E i true +
    _ / marginal E i false / marginal E i false - _
  ring

private lemma variance_bias_limit_sigma_average {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) :
    (∑ i, sigmaSq E i)/(n:ℝ) = aVariance E-msq E := by
  simp only [variance_bias_limit_sigma_identity E hb, Finset.sum_sub_distrib,
    sub_div, aVariance, msq]

private lemma variance_bias_limit_vber_mean {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (hb : Bernoulli E) :
    mean E.design (fun z => (n:ℝ)*vBER E z) = aVariance E := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (fun z => (n:ℝ)*vBER E z) = fun z =>
      (∑ i, ((if z i then E.outcome i z^2 else 0)/marginal E i true^2 +
        (if z i then 0 else E.outcome i z^2)/marginal E i false^2))/(n:ℝ) := by
    funext z; unfold vBER; field_simp [hn0] <;> ring
  rw [he, mean_div, mean_sum]
  unfold aVariance
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mean_add, mean_div, mean_div]
  unfold cmean
  have ht : (fun z : Assignment n => if z i = true then E.outcome i z^2 else 0) =
      (fun z => if z i then E.outcome i z^2 else 0) := by
    funext z; cases z i <;> rfl
  have hf : (fun z : Assignment n => if z i = false then E.outcome i z^2 else 0) =
      (fun z => if z i then 0 else E.outcome i z^2) := by
    funext z; cases z i <;> rfl
  simp only [ht, hf]
  change _ = _ / marginal E i true / marginal E i true +
    _ / marginal E i false / marginal E i false
  ring

private lemma variance_bias_limit_arm_square_variance {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (k q s : ℝ) (hr : Regular E k q s) (hq : 4 ≤ q)
    (hb : Bernoulli E) (b : Bool) :
    var E.design (fun z => (∑ i, (marginal E i b)⁻¹^2 * armVariable E b 2 i z)/(n:ℝ)) ≤
      k^8*dAvg E/(n:ℝ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hc (i j : Fin n) : |cov E.design (armVariable E b 2 i) (armVariable E b 2 j)| ≤
      d E i j*k^4 := by
    by_cases hij : Dependent E i j
    · simpa only [d, hij, ite_true, one_mul, show 2*2=4 by norm_num] using
        (corrected_moment_covariance E k q hr.1 hr.2.1 hr.2.2.2.2.1
          2 (by norm_num; exact hq) i j b).2.2.2.2.2.2
    · simp only [covariance_nonedge E hb i j hij b 2, abs_zero, d, hij,
        ite_false, zero_mul, le_refl]
  have hw (i : Fin n) : 0 < (marginal E i b)⁻¹^2 ∧ (marginal E i b)⁻¹^2 ≤ k^2 := by
    have hh := regular_marginal_bounds E k q s hr i b
    exact ⟨sq_pos_of_pos (inv_pos.mpr hh.2.2.1),
      pow_le_pow_left₀ (inv_nonneg.mpr hh.2.2.1.le) hh.2.2.2 2⟩
  rw [variance_div]
  calc
    _ ≤ ((k^2)^2 * ∑ i, ∑ j,
        |cov E.design (armVariable E b 2 i) (armVariable E b 2 j)|)/(n:ℝ)^2 :=
      div_le_div_of_nonneg_right
        (weighted_variance_absolute E.design _ _ _ hw).2 (sq_nonneg _)
    _ ≤ ((k^2)^2 * ∑ i, ∑ j, d E i j*k^4)/(n:ℝ)^2 := by
      gcongr with i j
      exact hc i j
    _ = k^8*dAvg E/(n:ℝ) := by
      simp only [dAvg, degree, ← Finset.sum_mul]
      field_simp
      <;> ring

private lemma variance_bias_limit_vber_variance {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (k q s : ℝ) (hr : Regular E k q s) (hq : 4 ≤ q)
    (hb : Bernoulli E) :
    var E.design (fun z => (n:ℝ)*vBER E z) ≤ 4*k^8*dAvg E/(n:ℝ) := by
  let T := fun b : Bool => fun z : Assignment n =>
    (∑ i, (marginal E i b)⁻¹^2 * armVariable E b 2 i z)/(n:ℝ)
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (fun z => (n:ℝ)*vBER E z) = fun z => T true z-(-T false z) := by
    funext z
    let R := fun i =>
      (if z i then E.outcome i z^2 else 0)/marginal E i true^2 +
      (if z i then 0 else E.outcome i z^2)/marginal E i false^2
    calc
      _ = (∑ i, R i)/(n:ℝ) := by
        change (n:ℝ)*((∑ i, R i)/(n:ℝ)^2) = _
        field_simp [hn0]
        <;> ring
      _ = T true z+T false z := by
        dsimp [T]
        rw [← add_div, ← Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        dsimp [R]
        cases hzi : z i <;> simp [armVariable, hzi, div_eq_mul_inv, inv_pow, mul_comm]
      _ = _ := by ring
  have hneg : var E.design (fun z => -T false z) = var E.design (T false) := by
    simp only [variance_second_moment]
    have hm : mean E.design (fun z => -T false z) = -mean E.design (T false) := by
      simpa using mean_const_mul E.design (-1) (T false)
    simp only [neg_sq, hm]
  rw [he]
  have hv := variance_sub_le E.design (T true) (fun z => -T false z)
  rw [hneg] at hv
  have ht := variance_bias_limit_arm_square_variance hn E k q s hr hq hb true
  have hf := variance_bias_limit_arm_square_variance hn E k q s hr hq hb false
  change var E.design (T true) ≤ _ at ht
  change var E.design (T false) ≤ _ at hf
  calc
    _ ≤ 2 * (var E.design (T true) + var E.design (T false)) := hv
    _ ≤ 2 * (k^8*dAvg E/(n:ℝ) + k^8*dAvg E/(n:ℝ)) := by linarith
    _ = _ := by ring

/-- A second-moment bound tending to zero gives changing-space convergence in
probability, without a mean-zero assumption. Strict and non-strict cutoffs are
kept separate. -/
private lemma variance_bias_limit_probability_of_mse (S : Study)
    (X : (t : ℕ) → Assignment (S.N t) → ℝ) (a : ℕ → ℝ)
    (ha : Tendsto a atTop (nhds 0))
    (hX : ∀ t, mean (S.experiment t).design (fun z => X t z^2) ≤ a t) :
    InProbability S X := by
  intro ε hε
  have hupper : Tendsto (fun t => a t/ε^2) atTop (nhds 0) := by
    simpa using ha.div_const (ε^2)
  apply squeeze_zero (fun t => probability_nonnegative _ _)
    (fun t => (finite_probability_mono _ _ _ (fun z hz => hz.le)).trans
      ((second_moment_tail _ (X t) ε hε).trans
        (div_le_div_of_nonneg_right (hX t) (sq_nonneg ε)))) hupper

private lemma variance_bias_limit_centered_mse {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (k q s : ℝ) (hr : Regular E k q s) (hq : 4 ≤ q)
    (hb : Bernoulli E) :
    mean E.design (fun z => ((n:ℝ)*vBER E z-aVariance E)^2) ≤
      4*k^8*dAvg E/(n:ℝ) := by
  rw [← variance_bias_limit_vber_mean hn E hb, centered_square_mean]
  exact variance_bias_limit_vber_variance hn E k q s hr hq hb

private lemma variance_bias_limit_scaled_probability (S : Study) (k q s : ℝ)
    (hr : RegularSequence S k q s) (hq : 4 ≤ q)
    (hb : ∀ t, Bernoulli (S.experiment t)) :
    InProbability S (fun t z =>
      (size S t*vBER (S.experiment t) z-aVariance (S.experiment t))/dAvg (S.experiment t)) := by
  have hn : Tendsto (size S) atTop atTop := tendsto_natCast_atTop_iff.mpr S.grows
  apply variance_bias_limit_probability_of_mse S _ (fun t => 4*k^8/size S t)
    (hn.const_div_atTop _)
  intro t
  let E := S.experiment t
  have hnR : 0 < size S t := by dsimp [size]; exact_mod_cast S.positive t
  have hd := average_degree_at_least_one E (S.positive t)
  have hd0 : 0 < dAvg E := lt_of_lt_of_le zero_lt_one hd
  simp_rw [div_pow]
  rw [mean_div]
  calc
    _ ≤ (4*k^8*dAvg E/size S t)/(dAvg E)^2 :=
      div_le_div_of_nonneg_right
        (variance_bias_limit_centered_mse (S.positive t) E k q s (hr t) hq (hb t))
        (sq_nonneg _)
    _ = (4*k^8/size S t)/dAvg E := by field_simp <;> ring
    _ ≤ 4*k^8/size S t := div_le_self (by positivity) hd

/-- Under a Bernoulli design, the mean of an arbitrary function restricted to
one treatment coordinate equals the coordinate's marginal probability times
the mean with that coordinate fixed. -/
private lemma variance_bias_limit_one_numerator {n : ℕ} (E : Experiment n)
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

private lemma variance_bias_limit_two_numerator {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (f : Assignment n → ℝ) :
    mean E.design (fun z => if z i = a ∧ z j = b then f z else 0) =
      (marginal E i a*marginal E j b) *
        mean E.design (fun z => f (Function.update (Function.update z i a) j b)) := by
  have he : (fun z : Assignment n => if z i = a ∧ z j = b then f z else 0) =
      fun z => if z i = a then (if z j = b then f z else 0) else 0 := by
    funext z; split_ifs <;> simp_all
  rw [he, variance_bias_limit_one_numerator E hb i a]
  simp only [Function.update_of_ne (Ne.symm hij)]
  rw [variance_bias_limit_one_numerator E hb j b]
  have hu (z : Assignment n) : Function.update (Function.update z j b) i a =
      Function.update (Function.update z i a) j b := by
    funext l
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
      simp_all [Function.update]
  simp_rw [hu]
  ring

private lemma variance_bias_limit_two_prob {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool) :
    prob E.design (fun z => z i = a ∧ z j = b) = marginal E i a*marginal E j b := by
  have h := variance_bias_limit_two_numerator E hb i j hij a b (fun _ => 1)
  simp only [mean_const, mul_one] at h
  rw [← h]
  unfold prob
  congr 1
  funext z
  split_ifs <;> rfl

private lemma variance_bias_limit_two_cmean {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (f : Assignment n → ℝ) :
    cmean E.design (fun z => z i = a ∧ z j = b) f =
      mean E.design (fun z => f (Function.update (Function.update z i a) j b)) := by
  rw [cmean, variance_bias_limit_two_prob E hb i j hij]
  calc
    _ = (mean E.design (fun z => if z i = a ∧ z j = b then f z else 0)) /
        (marginal E i a*marginal E j b) := by
      congr 1
      congr 1
      funext z
      split_ifs <;> rfl
    _ = _ := by
      rw [variance_bias_limit_two_numerator E hb i j hij]
      exact mul_div_cancel_left₀ _ (mul_ne_zero
        (marginal_pos E hb i a).ne' (marginal_pos E hb j b).ne')

private lemma variance_bias_limit_coordinate_partition {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i : Fin n) (f : Assignment n → ℝ) :
    mean E.design f = ∑ a : Bool, marginal E i a *
      mean E.design (fun z => f (Function.update z i a)) := by
  simp only [← variance_bias_limit_one_numerator E hb, Fintype.sum_bool]
  rw [← mean_add]
  congr 1
  funext z
  cases z i <;> simp

private lemma variance_bias_limit_conditional_affine {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool) :
    cmean E.design (fun z => z i = a ∧ z j = b) (E.outcome i) =
      cmean E.design (fun z => z i = a) (E.outcome i) +
        (bit b-marginal E j true)*xi E i j a := by
  let m := fun b : Bool => mean E.design (fun z =>
    E.outcome i (Function.update (Function.update z i a) j b))
  have hx : xi E i j a = m true-m false := by
    exact mean_sub E.design _ _
  have hmix : cmean E.design (fun z => z i = a) (E.outcome i) =
      marginal E j true*m true+marginal E j false*m false := by
    rw [conditional_observed_eq_potential_mean E hb]
    rw [variance_bias_limit_coordinate_partition E hb j (potential E i a)]
    simp only [Fintype.sum_bool, potential]
    have hu (z : Assignment n) (b : Bool) :
        Function.update (Function.update z j b) i a =
          Function.update (Function.update z i a) j b := by
      funext l
      by_cases hli : l = i <;> by_cases hlj : l = j <;>
        simp_all [Function.update]
    simp_rw [hu]
    rfl
  rw [variance_bias_limit_two_cmean E hb i j hij, hmix, hx]
  change m b = _
  have hp : marginal E j false = 1-marginal E j true := by
    linarith [marginal_partition E j]
  rw [hp]
  cases b <;> simp only [bit, Bool.false_eq_true, ite_false, ite_true] <;> ring

private lemma variance_bias_limit_cmean_product {Ω : Type*} [Fintype Ω]
    (P : Law Ω) (A : Ω → Prop) (hA : prob P A ≠ 0) (f g : Ω → ℝ) :
    cmean P A (fun z => f z*g z) = ccov P A f g + cmean P A f*cmean P A g := by
  have hlin (u v : Ω → ℝ) : cmean P A (fun z => u z+v z) = cmean P A u+cmean P A v := by
    unfold cmean
    rw [← add_div, ← mean_add]
    congr 2
    funext z; split_ifs <;> ring
  have hsub (u v : Ω → ℝ) : cmean P A (fun z => u z-v z) = cmean P A u-cmean P A v := by
    unfold cmean
    rw [← sub_div, ← mean_sub]
    congr 2
    funext z; split_ifs <;> ring
  have hmul (c : ℝ) (u : Ω → ℝ) : cmean P A (fun z => c*u z) = c*cmean P A u := by
    unfold cmean
    rw [← mul_div_assoc, ← mean_const_mul]
    congr 2
    funext z; split_ifs <;> ring
  have hconst (c : ℝ) : cmean P A (fun _ => c) = c := by
    unfold cmean prob
    have he : (fun z : Ω => if A z then c else 0) =
        fun z => c*(if A z then 1 else 0) := by
      funext z; split_ifs <;> ring
    rw [he, mean_const_mul]
    have hm : (mean P (fun z => if A z then (1 : ℝ) else 0)) = prob P A := by
      unfold prob
      congr 1 <;> funext z <;> split_ifs <;> rfl
    rw [hm, mul_div_cancel_right₀ _ hA]
  unfold ccov
  have he : (fun z => (f z-cmean P A f)*(g z-cmean P A g)) =
      fun z => f z*g z-cmean P A f*g z-cmean P A g*f z+cmean P A f*cmean P A g := by
    funext z; ring
  rw [he, hlin, hsub, hsub, hmul, hmul, hconst]
  ring

private lemma variance_bias_limit_pair_partition {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (f : Assignment n → ℝ) :
    mean E.design f = ∑ a : Bool, ∑ b : Bool,
      (marginal E i a*marginal E j b)*
        cmean E.design (fun z => z i = a ∧ z j = b) f := by
  have hweight (a b : Bool) : (marginal E i a*marginal E j b)*
      cmean E.design (fun z => z i = a ∧ z j = b) f =
      mean E.design (fun z => if z i = a ∧ z j = b then f z else 0) := by
    rw [cmean, variance_bias_limit_two_prob E hb i j hij,
      mul_div_cancel₀ _ (mul_ne_zero
        (marginal_pos E hb i a).ne' (marginal_pos E hb j b).ne')]
    congr 1
    funext z
    split_ifs <;> rfl
  simp_rw [hweight]
  simp only [Fintype.sum_bool]
  rw [← mean_add, ← mean_add, ← mean_add]
  congr 1
  funext z
  cases z i <;> cases z j <;> simp

/-- Off-diagonal covariance decomposes into an interference product, two
cross terms, and the weighted conditional covariances over the four treatment cells. -/
private lemma variance_bias_limit_offdiag {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) :
    cov E.design (variance_bias_limit_U E i) (variance_bias_limit_U E j) =
      xiBreve E i j*xiBreve E j i +
      yBreve E j*(xi E i j true-xi E i j false) +
      yBreve E i*(xi E j i true-xi E j i false) +
      ∑ a : Bool, ∑ b : Bool, (1-2*bit a)*(1-2*bit b)*
        ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j) := by
  have hcell (a b : Bool) :
      cmean E.design (fun z => z i = a ∧ z j = b)
        (fun z => variance_bias_limit_U E i z*variance_bias_limit_U E j z) =
      ((2*bit a-1)*(2*bit b-1)/(marginal E i a*marginal E j b))*
        cmean E.design (fun z => z i = a ∧ z j = b)
          (fun z => E.outcome i z*E.outcome j z) := by
    unfold cmean
    rw [← mul_div_assoc, ← mean_const_mul]
    congr 2
    funext z
    by_cases hz : z i = a ∧ z j = b
    · rcases hz with ⟨hi, hj⟩
      simp only [hi, hj, and_self, ite_true, variance_bias_limit_U]
      cases a <;> cases b <;> simp [bit] <;>
        field_simp [(marginal_pos E hb i true).ne', (marginal_pos E hb i false).ne',
          (marginal_pos E hb j true).ne', (marginal_pos E hb j false).ne'] <;> ring
    · simp [hz]
  have hswap (a b : Bool) :
      cmean E.design (fun z => z i = a ∧ z j = b) (E.outcome j) =
        cmean E.design (fun z => z j = b ∧ z i = a) (E.outcome j) := by
    simp only [and_comm]
  have hprod (a b : Bool) := variance_bias_limit_cmean_product E.design
    (fun z => z i = a ∧ z j = b)
    (by rw [variance_bias_limit_two_prob E hb i j hij];
        exact mul_ne_zero (marginal_pos E hb i a).ne' (marginal_pos E hb j b).ne')
    (E.outcome i) (E.outcome j)
  rw [covariance_product_formula, variance_bias_limit_U_mean E i, variance_bias_limit_U_mean E j,
    variance_bias_limit_pair_partition E hb i j hij
      (fun z => variance_bias_limit_U E i z*variance_bias_limit_U E j z)]
  simp_rw [hcell]
  have hcancel (a b : Bool) (x : ℝ) :
      (marginal E i a*marginal E j b)*
      (((2*bit a-1)*(2*bit b-1)/(marginal E i a*marginal E j b))*x) =
      (2*bit a-1)*(2*bit b-1)*x := by
    field_simp [(marginal_pos E hb i a).ne', (marginal_pos E hb j b).ne']
  simp_rw [hcancel, hprod]
  simp_rw [variance_bias_limit_conditional_affine E hb i j hij,
    hswap, variance_bias_limit_conditional_affine E hb j i (Ne.symm hij)]
  simp only [Fintype.sum_bool, bit, Bool.false_eq_true, ite_false, ite_true,
    xiBreve, yBreve]
  -- The four cell covariance terms cancel literally; the rest is a polynomial.
  ring

private lemma variance_bias_limit_decomposition {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (hb : Bernoulli E) :
    (n:ℝ)/dAvg E*var E.design (ht E) =
      aVariance E/dAvg E-msq E/dAvg E+B1 E+B2 E := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd0 : dAvg E ≠ 0 := (lt_of_lt_of_le zero_lt_one
    (average_degree_at_least_one E hn)).ne'
  have hs : (∑ i, ∑ j, cov E.design
      (variance_bias_limit_U E i) (variance_bias_limit_U E j)) =
      (∑ i, sigmaSq E i) + ∑ i, ∑ j, if j = i then 0 else
        cov E.design (variance_bias_limit_U E i) (variance_bias_limit_U E j) := by
    have hrow (i : Fin n) : (∑ j, cov E.design
        (variance_bias_limit_U E i) (variance_bias_limit_U E j)) =
        sigmaSq E i + ∑ j, if j = i then 0 else
          cov E.design (variance_bias_limit_U E i) (variance_bias_limit_U E j) := by
      calc
        _ = ∑ j, ((if j = i then sigmaSq E i else 0) +
            (if j = i then 0 else cov E.design
              (variance_bias_limit_U E i) (variance_bias_limit_U E j))) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hji : j = i
          · subst j
            simp only [ite_true, add_zero]
            rfl
          · simp only [hji, ite_false, zero_add]
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    simp_rw [hrow, Finset.sum_add_distrib]
  let C := fun i j : Fin n => if j = i then 0 else
    yBreve E j*(xi E i j true-xi E i j false)
  have hcross : (∑ i, ∑ j, if j = i then 0 else
      yBreve E i*(xi E j i true-xi E j i false)) = ∑ i, ∑ j, C i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [C, eq_comm]
  have hoff : (∑ i, ∑ j, if j = i then 0 else
      cov E.design (variance_bias_limit_U E i) (variance_bias_limit_U E j)) =
      (n:ℝ)*dAvg E*(B1 E+B2 E) := by
    have hpair (i j : Fin n) : (if j = i then 0 else
        cov E.design (variance_bias_limit_U E i) (variance_bias_limit_U E j)) =
        (if j = i then 0 else xiBreve E i j*xiBreve E j i) + C i j +
        (if j = i then 0 else yBreve E i*(xi E j i true-xi E j i false)) +
        (if j = i then 0 else ∑ a : Bool, ∑ b : Bool,
          (1-2*bit a)*(1-2*bit b)*
          ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j)) := by
      by_cases hji : j = i
      · simp [hji, C]
      · simp only [hji, ite_false, C]
        exact variance_bias_limit_offdiag E hb i j (Ne.symm hji)
    simp_rw [hpair, Finset.sum_add_distrib]
    rw [hcross]
    unfold B1 B2
    have hb1 (i j : Fin n) : (if j = i then 0 else
        xiBreve E i j*xiBreve E j i + 2*yBreve E j*(xi E i j true-xi E i j false)) =
        (if j = i then 0 else xiBreve E i j*xiBreve E j i) + 2*C i j := by
      split_ifs <;> simp [C, *] <;> ring
    simp_rw [hb1, Finset.sum_add_distrib, ← Finset.mul_sum]
    field_simp
    <;> ring
  rw [variance_bias_limit_ht_sum, variance_div, variance_bias_limit_sum_variance, hs, hoff]
  have hsigma : (∑ i, sigmaSq E i) = (aVariance E-msq E)*(n:ℝ) :=
    (div_eq_iff hn0).mp (variance_bias_limit_sigma_average E hb)
  rw [hsigma]
  field_simp [hn0, hd0]
  <;> ring

private lemma variance_bias_limit_noI_dAvg {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (h : NoInterference E) : dAvg E = 1 := by
  have hinter (l i : Fin n) : Interferes E l i ↔ l = i := by
    constructor
    · rintro (he | ⟨z, z', hag, hne⟩)
      · exact he
      · by_contra hli
        exact hne (h i z z' (hag i (Ne.symm hli)))
    · exact Or.inl
  have hd (i j : Fin n) : d E i j = if i = j then 1 else 0 := by
    simp only [d, Dependent, hinter]
    congr 1
    apply propext
    constructor
    · rintro ⟨l, rfl, rfl⟩; rfl
    · intro hij; exact ⟨i, rfl, hij⟩
  have hdeg (i : Fin n) : degree E i = 1 := by simp [degree, hd]
  simp [dAvg, hdeg, hn.ne']

private lemma variance_bias_limit_noI_B2 {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (h : NoInterference E) : B2 E = 0 := by
  have hc (i j : Fin n) (hij : i ≠ j) (a b : Bool) :
      ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j) = 0 := by
    let c := E.outcome i (fun _ => a)
    have hm : cmean E.design (fun z => z i = a ∧ z j = b) (E.outcome i) = c := by
      rw [variance_bias_limit_two_cmean E hb i j hij]
      have he : (fun z => E.outcome i (Function.update (Function.update z i a) j b)) =
          fun _ => c := by
        funext z
        apply h i
        simp [Function.update_of_ne hij]
      rw [he, mean_const]
    unfold ccov
    rw [hm]
    have he : (fun z : Assignment n => if z i = a ∧ z j = b then
        (E.outcome i z-c)*(E.outcome j z-
          cmean E.design (fun z => z i = a ∧ z j = b) (E.outcome j)) else 0) = fun _ => 0 := by
      funext z
      split_ifs with hz
      · have hi : E.outcome i z = c := h i z (fun _ => a) hz.1
        simp [hi]
      · rfl
    rw [cmean]
    have hnum : (mean E.design (fun z => if z i = a ∧ z j = b then
        (E.outcome i z-c)*(E.outcome j z-
          cmean E.design (fun z => z i = a ∧ z j = b) (E.outcome j)) else 0)) = 0 := by
      rw [he, mean_const]
    calc
      _ = (mean E.design (fun z => if z i = a ∧ z j = b then
        (E.outcome i z-c)*(E.outcome j z-
          cmean E.design (fun z => z i = a ∧ z j = b) (E.outcome j)) else 0)) /
          prob E.design (fun z => z i = a ∧ z j = b) := by
        congr 1
        congr 1
        funext z
        split_ifs <;> rfl
      _ = 0 := by rw [hnum, zero_div]

  unfold B2
  have hs : (∑ i, ∑ j, if j = i then 0 else
      ∑ a : Bool, ∑ b : Bool, (1-2*bit a)*(1-2*bit b)*
        ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    by_cases hij : j = i
    · simp [hij]
    · simp [hij, hc i j (Ne.symm hij)]
  rw [hs, zero_div]

theorem variance_bias_limit_proof (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hQ : 4 ≤ q)
    (hBER : ∀ t, Bernoulli (S.experiment t)) :
    InProbability S (fun t z => let E := S.experiment t
      size S t/dAvg E*(vBER E z-var E.design (ht E)) - (msq E/dAvg E-B1 E-B2 E)) ∧
    ((∀ t, NoInterference (S.experiment t)) →
      InProbability S (fun t z => let E := S.experiment t
        size S t*(vBER E z-var E.design (ht E))-msq E)) := by
  have hcenter := variance_bias_limit_scaled_probability S k q s hReg hQ hBER
  have he (t : ℕ) (z : Assignment (S.N t)) :
      size S t/dAvg (S.experiment t)*(vBER (S.experiment t) z-
        var (S.experiment t).design (ht (S.experiment t))) -
        (msq (S.experiment t)/dAvg (S.experiment t)-B1 (S.experiment t)-B2 (S.experiment t)) =
      (size S t*vBER (S.experiment t) z-aVariance (S.experiment t))/dAvg (S.experiment t) := by
    have hdec := variance_bias_limit_decomposition (S.positive t) (S.experiment t) (hBER t)
    change size S t/dAvg (S.experiment t)*var (S.experiment t).design (ht (S.experiment t)) = _ at hdec
    have hd0 : dAvg (S.experiment t) ≠ 0 := (lt_of_lt_of_le zero_lt_one
      (average_degree_at_least_one _ (S.positive t))).ne'
    field_simp [hd0] at hdec ⊢
    nlinarith [hdec]
  have hfirst : InProbability S (fun t z => let E := S.experiment t
      size S t/dAvg E*(vBER E z-var E.design (ht E)) - (msq E/dAvg E-B1 E-B2 E)) := by
    simpa only [he] using hcenter
  refine ⟨hfirst, ?_⟩
  intro hNo
  have hb1 (t : ℕ) : B1 (S.experiment t) = 0 :=
    (no_interference_B1_zero (S.positive t) _ (hNo t)
      (fun i => ⟨marginal_pos _ (hBER t) i true, marginal_pos _ (hBER t) i false⟩)).2
  have hd (t : ℕ) : dAvg (S.experiment t) = 1 :=
    variance_bias_limit_noI_dAvg (S.positive t) _ (hNo t)
  have hb2 (t : ℕ) : B2 (S.experiment t) = 0 :=
    variance_bias_limit_noI_B2 _ (hBER t) (hNo t)
  simpa only [hd, hb1, hb2, div_one, sub_zero] using hfirst

/-! Average-degree inflation bounds without a Regular assumption. -/

private lemma average_inflation_conservative_graph_variance {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (hb : Bernoulli E) :
    (n:ℝ)*var E.design (ht E) ≤ (∑ i, degree E i*sigmaSq E i)/(n:ℝ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  rw [variance_bias_limit_ht_sum, variance_div]
  calc
    _ = var E.design (fun z => ∑ i, variance_bias_limit_U E i z)/(n:ℝ) := by
      field_simp <;> ring
    _ ≤ (∑ i, degree E i*var E.design (variance_bias_limit_U E i))/(n:ℝ) :=
      div_le_div_of_nonneg_right
        (variance_bias_limit_graph_bound E hb _ (variance_bias_limit_U_depends E)) hnR.le
    _ = _ := rfl

private lemma average_inflation_conservative_cauchy {n : ℕ} (hn : 0 < n)
    (E : Experiment n) :
    |(∑ i, degree E i*(sigmaSq E i-(∑ j, sigmaSq E j)/(n:ℝ)))/(n:ℝ)| ≤
      dRMS E*sdSigmaSq E := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (degree E) (fun i => sigmaSq E i-(∑ j, sigmaSq E j)/(n:ℝ))
  have hnorm : ((∑ i, degree E i*(sigmaSq E i-(∑ j, sigmaSq E j)/(n:ℝ)))/(n:ℝ))^2 ≤
      ((∑ i, degree E i^2)/(n:ℝ))*
        ((∑ i, (sigmaSq E i-(∑ j, sigmaSq E j)/(n:ℝ))^2)/(n:ℝ)) := by
    convert div_le_div_of_nonneg_right hsq (sq_nonneg (n:ℝ)) using 1 <;> ring
  calc
    _ ≤ Real.sqrt (((∑ i, degree E i^2)/(n:ℝ))*
        ((∑ i, (sigmaSq E i-(∑ j, sigmaSq E j)/(n:ℝ))^2)/(n:ℝ))) :=
      Real.abs_le_sqrt hnorm
    _ = dRMS E*sdSigmaSq E := by
      rw [Real.sqrt_mul (by positivity)]
      rfl

private lemma average_inflation_conservative_finite_bound {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (hb : Bernoulli E) :
    (n:ℝ)/dAvg E*var E.design (ht E) ≤
      aVariance E+dRMS E*sdSigmaSq E/dAvg E := by
  let m := (∑ i, sigmaSq E i)/(n:ℝ)
  have hd : 0 < dAvg E := lt_of_lt_of_le zero_lt_one (average_degree_at_least_one E hn)
  have hm : m ≤ aVariance E := by
    have hmsq : 0 ≤ msq E := by unfold msq; positivity
    dsimp [m]
    rw [variance_bias_limit_sigma_average E hb]
    linarith
  have hsplit : (∑ i, degree E i*sigmaSq E i)/(n:ℝ) =
      dAvg E*m + (∑ i, degree E i*(sigmaSq E i-m))/(n:ℝ) := by
    calc
      _ = (∑ i, (degree E i*m+degree E i*(sigmaSq E i-m)))/(n:ℝ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ((∑ i, degree E i)*m)/(n:ℝ) +
          (∑ i, degree E i*(sigmaSq E i-m))/(n:ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, add_div]
      _ = _ := by unfold dAvg; ring
  have hcs := average_inflation_conservative_cauchy hn E
  change |(∑ i, degree E i*(sigmaSq E i-m))/(n:ℝ)| ≤ _ at hcs
  have hbnd : (n:ℝ)*var E.design (ht E) ≤
      dAvg E*aVariance E+dRMS E*sdSigmaSq E := by
    calc
      _ ≤ (∑ i, degree E i*sigmaSq E i)/(n:ℝ) :=
        average_inflation_conservative_graph_variance hn E hb
      _ = _ := hsplit
      _ ≤ dAvg E*aVariance E+dRMS E*sdSigmaSq E :=
        add_le_add (mul_le_mul_of_nonneg_left hm hd.le) ((le_abs_self _).trans hcs)
  calc
    _ = ((n:ℝ)*var E.design (ht E))/dAvg E := by ring
    _ ≤ (dAvg E*aVariance E+dRMS E*sdSigmaSq E)/dAvg E :=
      div_le_div_of_nonneg_right hbnd hd.le
    _ = _ := by field_simp <;> ring

private lemma average_inflation_conservative_rms_positive {n : ℕ} (hn : 0 < n)
    (E : Experiment n) : 0 < dRMS E := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hs : (n:ℝ) ≤ ∑ i, degree E i^2 := by
    calc
      _ = ∑ _i : Fin n, (1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => by
        have hi := variance_bias_limit_degree_one E i
        nlinarith [sq_nonneg (degree E i-1)])
  unfold dRMS
  apply Real.sqrt_pos.2
  exact div_pos (lt_of_lt_of_le hnR hs) hnR

private lemma average_inflation_conservative_restricted_concentration (S : Study)
    (k q s : ℝ) (hr : RegularSequence S k q s) (hq : 4 ≤ q)
    (hb : ∀ t, Bernoulli (S.experiment t)) (hrest : Restricted S) :
    InProbability S (fun t z => size S t*vBER (S.experiment t) z-aVariance (S.experiment t)) := by
  apply variance_bias_limit_probability_of_mse S _
    (fun t => 4*k^8*(dAvg (S.experiment t)/size S t))
  · simpa using hrest.const_mul (4*k^8)
  · intro t
    simpa only [mul_div_assoc, size] using
      variance_bias_limit_centered_mse (S.positive t) _ k q s (hr t) hq (hb t)

/-- An event with a vanishing deterministic negative allowance has vanishing
lower tails. The ε/4 strict tail avoids any equality-at-the-cutoff issue. -/
private lemma average_inflation_conservative_tail_bridge (S : Study)
    (X Y : (t : ℕ) → Assignment (S.N t) → ℝ) (r : ℕ → ℝ)
    (hX : InProbability S X) (hr : Tendsto r atTop (nhds 0))
    (hXY : ∀ t z, X t z-r t ≤ Y t z) :
    ∀ ε > 0, Tendsto (fun t => prob (S.experiment t).design (fun z => Y t z ≤ -ε))
      atTop (nhds 0) := by
  intro ε hε
  have hrsmall : ∀ᶠ t in atTop, r t < ε/2 := hr.eventually_lt_const (by positivity)
  apply squeeze_zero' (Eventually.of_forall (fun t => probability_nonnegative _ _))
    _ (hX (ε/4) (by positivity))
  filter_upwards [hrsmall] with t ht
  apply finite_probability_mono
  intro z hz
  have hl : X t z ≤ -ε+r t := by linarith [hXY t z]
  have hab : -X t z ≤ |X t z| := neg_le_abs _
  linarith

theorem average_inflation_conservative_proof (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hQ : 4 ≤ q)
    (hBER : ∀ t, Bernoulli (S.experiment t)) (hRestricted : Restricted S)
    (hSD : LittleO (fun t => sdSigmaSq (S.experiment t))
      (fun t => dAvg (S.experiment t)/dRMS (S.experiment t))) :
    Conservative S (fun t => vAVG (S.experiment t)) := by
  let r := fun t => dRMS (S.experiment t)*sdSigmaSq (S.experiment t)/dAvg (S.experiment t)
  let X := fun t z => size S t*vBER (S.experiment t) z-aVariance (S.experiment t)
  let Y := fun t z => size S t/dAvg (S.experiment t)*
    (vAVG (S.experiment t) z-var (S.experiment t).design (ht (S.experiment t)))
  have hr : Tendsto r atTop (nhds 0) := by
    have he (t : ℕ) : sdSigmaSq (S.experiment t)/
        (dAvg (S.experiment t)/dRMS (S.experiment t)) = r t := by
      have hd : dAvg (S.experiment t) ≠ 0 := (lt_of_lt_of_le zero_lt_one
        (average_degree_at_least_one _ (S.positive t))).ne'
      have hR := (average_inflation_conservative_rms_positive (S.positive t) (S.experiment t)).ne'
      dsimp [r]
      field_simp [hd, hR]
      <;> ring
    simpa only [LittleO, he] using hSD
  have hX : InProbability S X :=
    average_inflation_conservative_restricted_concentration S k q s hReg hQ hBER hRestricted
  have hXY (t : ℕ) (z : Assignment (S.N t)) : X t z-r t ≤ Y t z := by
    have hbnd := average_inflation_conservative_finite_bound (S.positive t) _ (hBER t)
    have hd0 : dAvg (S.experiment t) ≠ 0 := (lt_of_lt_of_le zero_lt_one
      (average_degree_at_least_one _ (S.positive t))).ne'
    have he : Y t z = size S t*vBER (S.experiment t) z-
        size S t/dAvg (S.experiment t)*var (S.experiment t).design (ht (S.experiment t)) := by
      dsimp [Y, vAVG]
      field_simp [hd0]
      <;> ring
    rw [he]
    dsimp [X, r]
    change size S t/dAvg (S.experiment t)*var (S.experiment t).design (ht (S.experiment t)) ≤ _ at hbnd
    linarith
  refine ⟨fun _ => 0, ?_, tendsto_const_nhds⟩
  exact average_inflation_conservative_tail_bridge S X Y r hX hr hXY

/-! Two unconditional finite average-degree inflation inequalities. -/

theorem average_inflation_finite_proof {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (hBER : Bernoulli E) :
    (n:ℝ)*var E.design (ht E) ≤ (∑ i, degree E i*sigmaSq E i)/(n:ℝ) ∧
    (n:ℝ)/dAvg E*var E.design (ht E) ≤
      aVariance E+dRMS E*sdSigmaSq E/dAvg E := by
  exact ⟨average_inflation_conservative_graph_variance hn E hBER,
    average_inflation_conservative_finite_bound hn E hBER⟩

end
end AronowAudit.P009.Wave1
