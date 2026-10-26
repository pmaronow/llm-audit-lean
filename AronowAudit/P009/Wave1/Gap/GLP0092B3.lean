import AronowAudit.P009.P009_BernoulliCompletion

/-!
Finite variance-bias identities (T47) and the spectral inflation bound (T50).
-/
namespace AronowAudit.P009.Wave1

open scoped BigOperators Topology
open Filter
open BernoulliCompletion

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000

private lemma t47b3_d_symm {n : ℕ} (E : Experiment n) (i j : Fin n) :
    d E i j = d E j i := by
  have h : Dependent E i j ↔ Dependent E j i := by
    constructor <;> rintro ⟨l, hl, hr⟩ <;> exact ⟨l, hr, hl⟩
  simp only [d, h]

private lemma t47b3_sum_variance {Ω U : Type*} [Fintype Ω] [Fintype U]
    (P : Law Ω) (X : U → Ω → ℝ) :
    var P (fun z => ∑ i, X i z) = ∑ i, ∑ j, cov P (X i) (X j) := by
  simpa only [one_mul] using
    (weighted_variance_absolute P X (fun _ => 1) 1
      (fun _ => ⟨by norm_num, le_rfl⟩)).1

private lemma t47b3_cov_nonedge {n : ℕ} (E : Experiment n)
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

private def t47b3_U {n : ℕ} (E : Experiment n) (i : Fin n)
    (z : Assignment n) : ℝ :=
  (if z i then E.outcome i z else 0)/marginal E i true -
    (if z i then 0 else E.outcome i z)/marginal E i false

private lemma t47b3_U_depends {n : ℕ} (E : Experiment n) (i : Fin n) :
    DependsOn (t47b3_U E i) {l | Interferes E l i} := by
  intro z z' hz
  have hi := hz i (Or.inl rfl)
  simp only [t47b3_U, hi, outcome_dependsOn E i hz]

private lemma t47b3_ht_sum {n : ℕ} (E : Experiment n) :
    ht E = fun z => (∑ i, t47b3_U E i z)/(n:ℝ) := by
  funext z
  simp only [ht, muHat, t47b3_U, Finset.sum_sub_distrib, sub_div]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hzi : z i <;> simp [hzi]

private lemma t47b3_U_mean {n : ℕ} (E : Experiment n) (i : Fin n) :
    mean E.design (t47b3_U E i) =
      cmean E.design (fun z => z i = true) (E.outcome i) -
      cmean E.design (fun z => z i = false) (E.outcome i) := by
  have he : t47b3_U E i = fun z =>
      (if z i = true then E.outcome i z else 0)/marginal E i true -
      (if z i = false then E.outcome i z else 0)/marginal E i false := by
    funext z
    cases hzi : z i <;> simp [t47b3_U, hzi]
  rw [he, mean_sub, mean_div, mean_div]
  simp only [cmean, marginal]
  congr 2 <;> congr 1 <;> funext z <;> split_ifs <;> rfl

/-- This contribution identity requires no Regular assumption. -/
private lemma t47b3_sigma_identity {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i : Fin n) :
    sigmaSq E i =
      cmean E.design (fun z => z i = true) (fun z => E.outcome i z^2)/marginal E i true +
      cmean E.design (fun z => z i = false) (fun z => E.outcome i z^2)/marginal E i false -
      mean E.design (effect E i)^2 := by
  have hmean : mean E.design (t47b3_U E i) = mean E.design (effect E i) := by
    rw [t47b3_U_mean E i, conditional_observed_eq_potential_mean E hb,
      conditional_observed_eq_potential_mean E hb]
    exact (mean_sub E.design _ _).symm
  have hs : (fun z => (t47b3_U E i z)^2) = fun z =>
      (if z i then E.outcome i z^2 else 0)/(marginal E i true)^2 +
      (if z i then 0 else E.outcome i z^2)/(marginal E i false)^2 := by
    funext z
    cases hzi : z i <;> simp [t47b3_U, hzi, div_pow]
  change var E.design (t47b3_U E i) = _
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

private lemma t47b3_sigma_average {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) :
    (∑ i, sigmaSq E i)/(n:ℝ) = aVariance E-msq E := by
  simp only [t47b3_sigma_identity E hb, Finset.sum_sub_distrib,
    sub_div, aVariance, msq]

private lemma t47b3_vber_mean {n : ℕ} (hn : 0 < n)
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

private lemma t47b3_arm_square_variance {n : ℕ} (hn : 0 < n)
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

private lemma t47b3_vber_variance {n : ℕ} (hn : 0 < n)
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
  have ht := t47b3_arm_square_variance hn E k q s hr hq hb true
  have hf := t47b3_arm_square_variance hn E k q s hr hq hb false
  change var E.design (T true) ≤ _ at ht
  change var E.design (T false) ≤ _ at hf
  calc
    _ ≤ 2 * (var E.design (T true) + var E.design (T false)) := hv
    _ ≤ 2 * (k^8*dAvg E/(n:ℝ) + k^8*dAvg E/(n:ℝ)) := by linarith
    _ = _ := by ring

private lemma t47b3_one_numerator {n : ℕ} (E : Experiment n)
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

private lemma t47b3_two_numerator {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (f : Assignment n → ℝ) :
    mean E.design (fun z => if z i = a ∧ z j = b then f z else 0) =
      (marginal E i a*marginal E j b) *
        mean E.design (fun z => f (Function.update (Function.update z i a) j b)) := by
  have he : (fun z : Assignment n => if z i = a ∧ z j = b then f z else 0) =
      fun z => if z i = a then (if z j = b then f z else 0) else 0 := by
    funext z; split_ifs <;> simp_all
  rw [he, t47b3_one_numerator E hb i a]
  simp only [Function.update_of_ne (Ne.symm hij)]
  rw [t47b3_one_numerator E hb j b]
  have hu (z : Assignment n) : Function.update (Function.update z j b) i a =
      Function.update (Function.update z i a) j b := by
    funext l
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
      simp_all [Function.update]
  simp_rw [hu]
  ring

private lemma t47b3_two_prob {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool) :
    prob E.design (fun z => z i = a ∧ z j = b) = marginal E i a*marginal E j b := by
  have h := t47b3_two_numerator E hb i j hij a b (fun _ => 1)
  simp only [mean_const, mul_one] at h
  rw [← h]
  unfold prob
  congr 1
  funext z
  split_ifs <;> rfl

private lemma t47b3_two_cmean {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (f : Assignment n → ℝ) :
    cmean E.design (fun z => z i = a ∧ z j = b) f =
      mean E.design (fun z => f (Function.update (Function.update z i a) j b)) := by
  rw [cmean, t47b3_two_prob E hb i j hij]
  calc
    _ = (mean E.design (fun z => if z i = a ∧ z j = b then f z else 0)) /
        (marginal E i a*marginal E j b) := by
      congr 1
      congr 1
      funext z
      split_ifs <;> rfl
    _ = _ := by
      rw [t47b3_two_numerator E hb i j hij]
      exact mul_div_cancel_left₀ _ (mul_ne_zero
        (marginal_pos E hb i a).ne' (marginal_pos E hb j b).ne')

private lemma t47b3_coordinate_partition {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i : Fin n) (f : Assignment n → ℝ) :
    mean E.design f = ∑ a : Bool, marginal E i a *
      mean E.design (fun z => f (Function.update z i a)) := by
  simp only [← t47b3_one_numerator E hb, Fintype.sum_bool]
  rw [← mean_add]
  congr 1
  funext z
  cases z i <;> simp

private lemma t47b3_conditional_affine {n : ℕ} (E : Experiment n)
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
    rw [t47b3_coordinate_partition E hb j (potential E i a)]
    simp only [Fintype.sum_bool, potential]
    have hu (z : Assignment n) (b : Bool) :
        Function.update (Function.update z j b) i a =
          Function.update (Function.update z i a) j b := by
      funext l
      by_cases hli : l = i <;> by_cases hlj : l = j <;>
        simp_all [Function.update]
    simp_rw [hu]
    rfl
  rw [t47b3_two_cmean E hb i j hij, hmix, hx]
  change m b = _
  have hp : marginal E j false = 1-marginal E j true := by
    linarith [marginal_partition E j]
  rw [hp]
  cases b <;> simp only [bit, Bool.false_eq_true, ite_false, ite_true] <;> ring

private lemma t47b3_cmean_product {Ω : Type*} [Fintype Ω]
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

private lemma t47b3_pair_partition {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (f : Assignment n → ℝ) :
    mean E.design f = ∑ a : Bool, ∑ b : Bool,
      (marginal E i a*marginal E j b)*
        cmean E.design (fun z => z i = a ∧ z j = b) f := by
  have hweight (a b : Bool) : (marginal E i a*marginal E j b)*
      cmean E.design (fun z => z i = a ∧ z j = b) f =
      mean E.design (fun z => if z i = a ∧ z j = b then f z else 0) := by
    rw [cmean, t47b3_two_prob E hb i j hij,
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

/-- Keep both cross terms at the pair level; their equality is used only
AFTER summing over ordered pairs. -/
private lemma t47b3_offdiag {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) :
    cov E.design (t47b3_U E i) (t47b3_U E j) =
      xiBreve E i j*xiBreve E j i +
      yBreve E j*(xi E i j true-xi E i j false) +
      yBreve E i*(xi E j i true-xi E j i false) +
      ∑ a : Bool, ∑ b : Bool, (1-2*bit a)*(1-2*bit b)*
        ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j) := by
  have hcell (a b : Bool) :
      cmean E.design (fun z => z i = a ∧ z j = b)
        (fun z => t47b3_U E i z*t47b3_U E j z) =
      ((2*bit a-1)*(2*bit b-1)/(marginal E i a*marginal E j b))*
        cmean E.design (fun z => z i = a ∧ z j = b)
          (fun z => E.outcome i z*E.outcome j z) := by
    unfold cmean
    rw [← mul_div_assoc, ← mean_const_mul]
    congr 2
    funext z
    by_cases hz : z i = a ∧ z j = b
    · rcases hz with ⟨hi, hj⟩
      simp only [hi, hj, and_self, ite_true, t47b3_U]
      cases a <;> cases b <;> simp [bit] <;>
        field_simp [(marginal_pos E hb i true).ne', (marginal_pos E hb i false).ne',
          (marginal_pos E hb j true).ne', (marginal_pos E hb j false).ne'] <;> ring
    · simp [hz]
  have hswap (a b : Bool) :
      cmean E.design (fun z => z i = a ∧ z j = b) (E.outcome j) =
        cmean E.design (fun z => z j = b ∧ z i = a) (E.outcome j) := by
    simp only [and_comm]
  have hprod (a b : Bool) := t47b3_cmean_product E.design
    (fun z => z i = a ∧ z j = b)
    (by rw [t47b3_two_prob E hb i j hij];
        exact mul_ne_zero (marginal_pos E hb i a).ne' (marginal_pos E hb j b).ne')
    (E.outcome i) (E.outcome j)
  rw [covariance_product_formula, t47b3_U_mean E i, t47b3_U_mean E j,
    t47b3_pair_partition E hb i j hij
      (fun z => t47b3_U E i z*t47b3_U E j z)]
  simp_rw [hcell]
  have hcancel (a b : Bool) (x : ℝ) :
      (marginal E i a*marginal E j b)*
      (((2*bit a-1)*(2*bit b-1)/(marginal E i a*marginal E j b))*x) =
      (2*bit a-1)*(2*bit b-1)*x := by
    field_simp [(marginal_pos E hb i a).ne', (marginal_pos E hb j b).ne']
  simp_rw [hcancel, hprod]
  simp_rw [t47b3_conditional_affine E hb i j hij,
    hswap, t47b3_conditional_affine E hb j i (Ne.symm hij)]
  simp only [Fintype.sum_bool, bit, Bool.false_eq_true, ite_false, ite_true,
    xiBreve, yBreve]
  -- The four cell covariance terms cancel literally; the rest is a polynomial.
  ring

private lemma t47b3_decomposition {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (hb : Bernoulli E) :
    (n:ℝ)/dAvg E*var E.design (ht E) =
      aVariance E/dAvg E-msq E/dAvg E+B1 E+B2 E := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd0 : dAvg E ≠ 0 := (lt_of_lt_of_le zero_lt_one
    (average_degree_at_least_one E hn)).ne'
  have hs : (∑ i, ∑ j, cov E.design
      (t47b3_U E i) (t47b3_U E j)) =
      (∑ i, sigmaSq E i) + ∑ i, ∑ j, if j = i then 0 else
        cov E.design (t47b3_U E i) (t47b3_U E j) := by
    have hrow (i : Fin n) : (∑ j, cov E.design
        (t47b3_U E i) (t47b3_U E j)) =
        sigmaSq E i + ∑ j, if j = i then 0 else
          cov E.design (t47b3_U E i) (t47b3_U E j) := by
      calc
        _ = ∑ j, ((if j = i then sigmaSq E i else 0) +
            (if j = i then 0 else cov E.design
              (t47b3_U E i) (t47b3_U E j))) := by
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
      cov E.design (t47b3_U E i) (t47b3_U E j)) =
      (n:ℝ)*dAvg E*(B1 E+B2 E) := by
    have hpair (i j : Fin n) : (if j = i then 0 else
        cov E.design (t47b3_U E i) (t47b3_U E j)) =
        (if j = i then 0 else xiBreve E i j*xiBreve E j i) + C i j +
        (if j = i then 0 else yBreve E i*(xi E j i true-xi E j i false)) +
        (if j = i then 0 else ∑ a : Bool, ∑ b : Bool,
          (1-2*bit a)*(1-2*bit b)*
          ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j)) := by
      by_cases hji : j = i
      · simp [hji, C]
      · simp only [hji, ite_false, C]
        exact t47b3_offdiag E hb i j (Ne.symm hji)
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
  rw [t47b3_ht_sum, variance_div, t47b3_sum_variance, hs, hoff]
  have hsigma : (∑ i, sigmaSq E i) = (aVariance E-msq E)*(n:ℝ) :=
    (div_eq_iff hn0).mp (t47b3_sigma_average E hb)
  rw [hsigma]
  field_simp [hn0, hd0]
  <;> ring

private lemma t47b3_variance_sub_const {Ω : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → ℝ) (c : ℝ) :
    var P (fun z => X z-c) = var P X := by
  unfold var cov
  rw [mean_sub, mean_const]
  congr 1
  funext z
  ring

/-- T47: six finite identities and bounds. -/
theorem variance_bias_finite_proof {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hReg : Regular E k q s) (hQ : 4 ≤ q) (hBER : Bernoulli E) :
    mean E.design (fun z => (n:ℝ)*vBER E z) = aVariance E ∧
    var E.design (fun z => (n:ℝ)*vBER E z) ≤ 4*k^8*dAvg E/(n:ℝ) ∧
    (∀ i, sigmaSq E i =
      cmean E.design (fun z => z i = true) (fun z => E.outcome i z^2)/marginal E i true +
      cmean E.design (fun z => z i = false) (fun z => E.outcome i z^2)/marginal E i false -
      mean E.design (effect E i)^2) ∧
    (n:ℝ)/dAvg E*var E.design (ht E) = aVariance E/dAvg E-msq E/dAvg E+B1 E+B2 E ∧
    (n:ℝ)/dAvg E*(mean E.design (vBER E)-var E.design (ht E)) = msq E/dAvg E-B1 E-B2 E ∧
    var E.design (fun z => (n:ℝ)/dAvg E*(vBER E z-var E.design (ht E))) ≤
      4*k^8/((n:ℝ)*dAvg E) := by
  have hm := t47b3_vber_mean hn E hBER
  have hv := t47b3_vber_variance hn E k q s hReg hQ hBER
  have hdec := t47b3_decomposition hn E hBER
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd0 : dAvg E ≠ 0 := (lt_of_lt_of_le zero_lt_one
    (average_degree_at_least_one E hn)).ne'
  have hmV : (n:ℝ)*mean E.design (vBER E) = aVariance E := by
    simpa only [mean_const_mul] using hm
  refine ⟨hm, hv, t47b3_sigma_identity E hBER, hdec, ?_, ?_⟩
  · calc
      _ = ((n:ℝ)*mean E.design (vBER E))/dAvg E -
          (n:ℝ)/dAvg E*var E.design (ht E) := by ring
      _ = _ := by rw [hmV, hdec]; ring
  · have he : (fun z => (n:ℝ)/dAvg E*(vBER E z-var E.design (ht E))) =
        fun z => ((n:ℝ)*vBER E z-(n:ℝ)*var E.design (ht E))/dAvg E := by
      funext z
      ring
    rw [he, variance_div, t47b3_variance_sub_const]
    calc
      _ ≤ (4*k^8*dAvg E/(n:ℝ))/(dAvg E)^2 :=
        div_le_div_of_nonneg_right hv (sq_nonneg _)
      _ = _ := by field_simp [hn0, hd0]

/-! T50: spectral inflation bounds via the Rayleigh quotient. -/

private lemma t50b3_d_nonneg {n : ℕ} (E : Experiment n) (i j : Fin n) :
    0 ≤ d E i j := by unfold d; split_ifs <;> norm_num

private lemma t50b3_cov_zero {n : ℕ} (E : Experiment n) (hBER : Bernoulli E)
    (i j : Fin n) (hij : ¬ Dependent E i j) :
    cov E.design (t47b3_U E i) (t47b3_U E j) = 0 :=
  t47b3_cov_nonedge E hBER i j hij _ _ (t47b3_U_depends E i) (t47b3_U_depends E j)

private lemma t50b3_max_degree {n : ℕ} (hn : 0 < n) (E : Experiment n) :
    (∀ i, degree E i ≤ dMax E) ∧ 1 ≤ dMax E ∧ dAvg E ≤ dMax E := by
  have hb : BddAbove (Set.range (degree E)) := (Set.finite_range _).bddAbove
  have hi (i : Fin n) : degree E i ≤ dMax E := le_csSup hb ⟨i, rfl⟩
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have havg : dAvg E ≤ dMax E := by
    rw [dAvg, div_le_iff₀ hnR]
    simpa [nsmul_eq_mul, mul_comm] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  exact ⟨hi, (average_degree_at_least_one E hn).trans havg, havg⟩

private lemma t50b3_quad_max {n : ℕ} (hn : 0 < n) (E : Experiment n) (v : Fin n → ℝ) :
    quadD E v ≤ dMax E*(∑ i, v i^2) := by
  have hentry (i j : Fin n) : v i*d E i j*v j ≤ d E i j*((v i^2+v j^2)/2) := by
    have hh := mul_nonneg (t50b3_d_nonneg E i j) (sq_nonneg (v i-v j))
    nlinarith
  have hs : (∑ i, ∑ j, d E i j*((v i^2+v j^2)/2)) = ∑ i, degree E i*v i^2 := by
    simp_rw [← mul_div_assoc, mul_add, ← Finset.sum_div, Finset.sum_add_distrib]
    have hleft : (∑ i, ∑ j, d E i j*v i^2) = ∑ i, degree E i*v i^2 := by
      simp only [degree, ← Finset.sum_mul]
    have hright : (∑ i, ∑ j, d E i j*v j^2) = ∑ i, degree E i*v i^2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = ∑ j, d E i j*v i^2 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [t47b3_d_symm E j i]
        _ = _ := by simp only [degree, ← Finset.sum_mul]
    rw [hleft, hright]
    ring
  calc
    _ ≤ ∑ i, ∑ j, d E i j*((v i^2+v j^2)/2) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hentry i j))
    _ = ∑ i, degree E i*v i^2 := hs
    _ ≤ _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_right ((t50b3_max_degree hn E).1 i) (sq_nonneg _))

private lemma t50b3_rayleigh {n : ℕ} (hn : 0 < n) (E : Experiment n) :
    (∀ v : Fin n → ℝ, quadD E v ≤ lambdaMax E*(∑ i, v i^2)) ∧
    dAvg E ≤ lambdaMax E := by
  let R : Set ℝ := {r | ∃ v : Fin n → ℝ, (∑ i, v i^2)=1 ∧ r=quadD E v}
  have hR : BddAbove R := by
    refine ⟨dMax E, ?_⟩
    rintro r ⟨v, hv, rfl⟩
    simpa only [hv, mul_one] using t50b3_quad_max hn E v
  have hhom (v : Fin n → ℝ) (c : ℝ) :
      quadD E (fun i => c*v i) = c^2*quadD E v := by
    simp only [quadD, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hquad (v : Fin n → ℝ) : quadD E v ≤ lambdaMax E*(∑ i, v i^2) := by
    let T : ℝ := ∑ i, v i^2
    have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    by_cases hT0 : T=0
    · have hv0 (i : Fin n) : v i=0 := by
        have hle : v i^2 ≤ T := Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        nlinarith [sq_nonneg (v i)]
      simp [quadD, hv0]
    · have hTp : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
      have hs : (Real.sqrt T)^2=T := Real.sq_sqrt hT
      have hs0 : Real.sqrt T ≠ 0 := (Real.sqrt_pos.2 hTp).ne'
      let w := fun i => (Real.sqrt T)⁻¹*v i
      have hw : (∑ i, w i^2)=1 := by
        simp only [w, mul_pow, ← Finset.mul_sum]
        change ((Real.sqrt T)⁻¹)^2*T=1
        rw [inv_pow, hs]
        exact inv_mul_cancel₀ hT0
      have hle : quadD E w ≤ lambdaMax E := le_csSup hR ⟨w, hw, rfl⟩
      rw [hhom] at hle
      have he : (Real.sqrt T)⁻¹^2 = T⁻¹ := by rw [inv_pow, hs]
      rw [he] at hle
      have hh := mul_le_mul_of_nonneg_left hle hT
      have hcancel : T*(T⁻¹*quadD E v)=quadD E v := by rw [← mul_assoc, mul_inv_cancel₀ hT0, one_mul]
      rw [hcancel] at hh
      calc
        quadD E v ≤ T*lambdaMax E := hh
        _ = lambdaMax E*(∑ i, v i^2) := by dsimp [T] <;> ring
  refine ⟨hquad, ?_⟩
  have hone := hquad (fun _ => 1)
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hval : quadD E (fun _ => 1) = (n:ℝ)*dAvg E := by
    simp only [quadD, one_mul, mul_one, dAvg, degree]
    field_simp [hn0]
  rw [hval] at hone
  simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hone
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  nlinarith [hone]

/-- Finite spectral margin, proved directly from the Rayleigh definition. -/
private lemma t50b3_spectral_margin {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (hBER : Bernoulli E) :
    (n:ℝ)/lambdaMax E*var E.design (ht E) ≤ aVariance E-msq E ∧
      dAvg E ≤ lambdaMax E := by
  have hr := t50b3_rayleigh hn E
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hl : 0 < lambdaMax E :=
    lt_of_lt_of_le zero_lt_one ((average_degree_at_least_one E hn).trans hr.2)
  let v := fun i => Real.sqrt (sigmaSq E i)
  have hi (i : Fin n) : 0 ≤ sigmaSq E i := variance_nonnegative E.design _
  have hc (i j : Fin n) : cov E.design (t47b3_U E i) (t47b3_U E j) ≤ v i*d E i j*v j := by
    by_cases hij : Dependent E i j
    · have hh := (le_abs_self _).trans (covariance_cauchy_schwarz E.design (t47b3_U E i) (t47b3_U E j))
      change cov E.design (t47b3_U E i) (t47b3_U E j) ≤
        Real.sqrt (sigmaSq E i*sigmaSq E j) at hh
      simpa only [v, d, hij, if_true, mul_one, Real.sqrt_mul (hi i)] using hh
    · simp [d, hij, t50b3_cov_zero E hBER i j hij]
  have hv : var E.design (fun z => ∑ i, t47b3_U E i z) ≤ lambdaMax E*(∑ i, sigmaSq E i) := by
    calc
      _ ≤ quadD E v := by
        rw [t47b3_sum_variance]
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hc i j))
      _ ≤ lambdaMax E*(∑ i, v i^2) := hr.1 v
      _ = _ := by simp only [v, Real.sq_sqrt (hi _)]
  have hnorm : (n:ℝ)*var E.design (ht E) ≤ lambdaMax E*(aVariance E-msq E) := by
    rw [t47b3_ht_sum, variance_div]
    calc
      _ = var E.design (fun z => ∑ i, t47b3_U E i z)/(n:ℝ) := by
        field_simp [hnR.ne'] <;> ring
      _ ≤ (lambdaMax E*(∑ i, sigmaSq E i))/(n:ℝ) := div_le_div_of_nonneg_right hv hnR.le
      _ = _ := by rw [mul_div_assoc, t47b3_sigma_average E hBER]
  refine ⟨?_, hr.2⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ hl]
  nlinarith [hnorm]

private lemma t50b3_lambda_le_max {n : ℕ} (hn : 0 < n) (E : Experiment n) :
    lambdaMax E ≤ dMax E := by
  have hne : Set.Nonempty {r | ∃ v : Fin n → ℝ,
      (∑ i, v i^2) = 1 ∧ r = quadD E v} := by
    let i0 : Fin n := ⟨0, hn⟩
    let v : Fin n → ℝ := fun i => if i = i0 then 1 else 0
    refine ⟨quadD E v, v, ?_, rfl⟩
    simp [v]
  apply csSup_le hne
  rintro r ⟨v, hv, rfl⟩
  simpa only [hv, mul_one] using t50b3_quad_max hn E v

/-- T50: the Rayleigh bound, variance bound, and both degree comparisons. -/
theorem spectral_inflation_finite_proof {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (hBER : Bernoulli E) :
    (∀ v : Fin n → ℝ, quadD E v ≤ lambdaMax E*(∑ i, v i^2)) ∧
    (n:ℝ)/lambdaMax E*var E.design (ht E) ≤ aVariance E-msq E ∧
    dAvg E ≤ lambdaMax E ∧ lambdaMax E ≤ dMax E := by
  have hr := t50b3_rayleigh hn E
  exact ⟨hr.1, (t50b3_spectral_margin hn E hBER).1,
    hr.2, t50b3_lambda_le_max hn E⟩

end
end AronowAudit.P009.Wave1
