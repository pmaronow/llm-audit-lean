import AronowAudit.P009.P009_BernoulliCompletion
import AronowAudit.P009.P009_SharpnessCompletion

/-! Maximum-degree and spectral inflation bounds, and a one-source construction. -/
namespace AronowAudit.P009.Wave1

open scoped BigOperators Topology
open Filter

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

open BernoulliCompletion

/-- Unaveraged signed contribution for the maximum-degree and spectral inflation bounds. -/
private def t49_U {n : ℕ} (E : Experiment n) (i : Fin n) (z : Assignment n) : ℝ :=
  (if z i then E.outcome i z else 0)/marginal E i true -
    (if z i then 0 else E.outcome i z)/marginal E i false

private lemma t49_ht {n : ℕ} (E : Experiment n) :
    ht E = fun z => (∑ i, t49_U E i z)/(n:ℝ) := by
  funext z
  simp only [ht, muHat, ← sub_div, ← Finset.sum_sub_distrib, t49_U]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases z i <;> simp

private lemma t49_symm {n : ℕ} (E : Experiment n) (i j : Fin n) :
    d E i j = d E j i := by
  have h : Dependent E i j ↔ Dependent E j i := by
    constructor <;> rintro ⟨l, hi, hj⟩ <;> exact ⟨l, hj, hi⟩
  simp only [d, h]

private lemma t49_d_nonneg {n : ℕ} (E : Experiment n) (i j : Fin n) :
    0 ≤ d E i j := by unfold d; split_ifs <;> norm_num

private lemma t49_U_depends {n : ℕ} (E : Experiment n) (i : Fin n) :
    DependsOn (t49_U E i) {l | Interferes E l i} := by
  intro z z' h
  have hi := h i (Or.inl rfl)
  have hy := outcome_dependsOn E i h
  simp only [t49_U, hi, hy]

private lemma t49_cov_zero {n : ℕ} (E : Experiment n) (hBER : Bernoulli E)
    (i j : Fin n) (hij : ¬ Dependent E i j) :
    cov E.design (t49_U E i) (t49_U E j) = 0 := by
  have hj : DependsOn (t49_U E j) {l | Interferes E l i}ᶜ := by
    apply DependsOn.mono _ (t49_U_depends E j)
    intro l hl hi
    exact hij ⟨l, hi, hl⟩
  rw [covariance_product_formula,
    mean_product_of_dependsOn E hBER _ _ _ (t49_U_depends E i) hj, sub_self]

private lemma t49_variance_sum {n : ℕ} (E : Experiment n) :
    var E.design (fun z => ∑ i, t49_U E i z) =
      ∑ i, ∑ j, cov E.design (t49_U E i) (t49_U E j) := by
  simpa only [one_mul] using
    (weighted_variance_absolute E.design (t49_U E) (fun _ => (1:ℝ)) 1
      (fun _ => ⟨by norm_num, le_rfl⟩)).1

/-- The average contribution variance is A minus the mean squared effect.
This identity needs no regularity assumption. -/
private lemma t49_contribution_identity {n : ℕ} (E : Experiment n)
    (hBER : Bernoulli E) :
    (∑ i, sigmaSq E i)/(n:ℝ) = aVariance E-msq E := by
  have hu (i : Fin n) : mean E.design (t49_U E i) = mean E.design (effect E i) := by
    have he : t49_U E i = fun z =>
        (if z i = true then E.outcome i z else 0)/marginal E i true -
        (if z i = false then E.outcome i z else 0)/marginal E i false := by
      funext z; cases hz : z i <;> simp [t49_U, hz]
    rw [he, mean_sub, mean_div, mean_div]
    have hc (b : Bool) :
        mean E.design (fun z => if z i = b then E.outcome i z else 0) / marginal E i b =
          cmean E.design (fun z => z i = b) (E.outcome i) := by
      unfold cmean
      congr 1
      apply congrArg (mean E.design)
      funext z
      by_cases hz : z i = b <;> simp [hz]
    rw [hc, hc]
    rw [conditional_observed_eq_potential_mean E hBER,
      conditional_observed_eq_potential_mean E hBER]
    exact (mean_sub E.design _ _).symm
  have hs (i : Fin n) : mean E.design (fun z => (t49_U E i z)^2) =
      cmean E.design (fun z => z i = true) (fun z => E.outcome i z^2)/marginal E i true +
      cmean E.design (fun z => z i = false) (fun z => E.outcome i z^2)/marginal E i false := by
    have he : (fun z => (t49_U E i z)^2) = fun z =>
        (if z i = true then E.outcome i z^2 else 0)/marginal E i true^2 +
        (if z i = false then E.outcome i z^2 else 0)/marginal E i false^2 := by
      funext z
      cases hz : z i <;> simp [t49_U, hz, div_pow]
    rw [he, mean_add, mean_div, mean_div]
    unfold cmean
    change _ = (_/marginal E i true)/marginal E i true +
      (_/marginal E i false)/marginal E i false
    ring
  have hi (i : Fin n) : sigmaSq E i =
      cmean E.design (fun z => z i = true) (fun z => E.outcome i z^2)/marginal E i true +
      cmean E.design (fun z => z i = false) (fun z => E.outcome i z^2)/marginal E i false -
      mean E.design (effect E i)^2 := by
    change var E.design (t49_U E i) = _
    rw [variance_second_moment, hu, hs]
  simp only [hi, Finset.sum_sub_distrib, sub_div, aVariance, msq]

private lemma t49_max_degree {n : ℕ} (hn : 0 < n) (E : Experiment n) :
    (∀ i, degree E i ≤ dMax E) ∧ 1 ≤ dMax E ∧ dAvg E ≤ dMax E := by
  have hb : BddAbove (Set.range (degree E)) := (Set.finite_range _).bddAbove
  have hi (i : Fin n) : degree E i ≤ dMax E := le_csSup hb ⟨i, rfl⟩
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have havg : dAvg E ≤ dMax E := by
    rw [dAvg, div_le_iff₀ hnR]
    simpa [nsmul_eq_mul, mul_comm] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  exact ⟨hi, (average_degree_at_least_one E hn).trans havg, havg⟩

private lemma t49_graph_bound {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (hBER : Bernoulli E) :
    (n:ℝ)*var E.design (ht E) ≤ (∑ i, degree E i*sigmaSq E i)/(n:ℝ) := by
  have hc (i j : Fin n) : cov E.design (t49_U E i) (t49_U E j) ≤
      d E i j*((sigmaSq E i+sigmaSq E j)/2) := by
    by_cases hij : Dependent E i j
    · simp only [d, hij, if_true, one_mul]
      have hi : 0 ≤ sigmaSq E i := variance_nonnegative E.design _
      have hj : 0 ≤ sigmaSq E j := variance_nonnegative E.design _
      have hcs := covariance_cauchy_schwarz E.design (t49_U E i) (t49_U E j)
      change |cov E.design (t49_U E i) (t49_U E j)| ≤
        Real.sqrt (sigmaSq E i*sigmaSq E j) at hcs
      rw [Real.sqrt_mul hi] at hcs
      have hs : Real.sqrt (sigmaSq E i)*Real.sqrt (sigmaSq E j) ≤
          (sigmaSq E i+sigmaSq E j)/2 := by
        nlinarith [Real.sq_sqrt hi, Real.sq_sqrt hj,
          sq_nonneg (Real.sqrt (sigmaSq E i)-Real.sqrt (sigmaSq E j))]
      exact (le_abs_self _).trans (hcs.trans hs)
    · simp [d, hij, t49_cov_zero E hBER i j hij]
  have hsum : (∑ i, ∑ j, d E i j*((sigmaSq E i+sigmaSq E j)/2)) =
      ∑ i, degree E i*sigmaSq E i := by
    simp_rw [← mul_div_assoc, mul_add, ← Finset.sum_div, Finset.sum_add_distrib]
    have hleft : (∑ i, ∑ j, d E i j*sigmaSq E i) = ∑ i, degree E i*sigmaSq E i := by
      simp only [degree, ← Finset.sum_mul]
    have hright : (∑ i, ∑ j, d E i j*sigmaSq E j) = ∑ i, degree E i*sigmaSq E i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = ∑ j, d E i j*sigmaSq E i := by
          apply Finset.sum_congr rfl
          intro j _
          rw [t49_symm E j i]
        _ = _ := by simp only [degree, ← Finset.sum_mul]
    rw [hleft, hright]
    ring
  have hv : var E.design (fun z => ∑ i, t49_U E i z) ≤
      ∑ i, degree E i*sigmaSq E i := by
    rw [t49_variance_sum, ← hsum]
    exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hc i j))
  rw [t49_ht, variance_div]
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  calc
    _ = var E.design (fun z => ∑ i, t49_U E i z)/(n:ℝ) := by
      field_simp [hnR.ne'] <;> ring
    _ ≤ _ := div_le_div_of_nonneg_right hv hnR.le

private lemma t49_max_finite {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (hBER : Bernoulli E) :
    (n:ℝ)/dMax E*var E.design (ht E) ≤ aVariance E-msq E ∧ dAvg E ≤ dMax E := by
  have hb := t49_max_degree hn E
  have hb0 : 0 < dMax E := lt_of_lt_of_le zero_lt_one hb.2.1
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hsum : (∑ i, degree E i*sigmaSq E i) ≤ dMax E*(∑ i, sigmaSq E i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hb.1 i) (variance_nonnegative E.design _))
  have hv := (t49_graph_bound hn E hBER).trans
    (div_le_div_of_nonneg_right hsum hnR.le)
  rw [mul_div_assoc, t49_contribution_identity E hBER] at hv
  refine ⟨?_, hb.2.2⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ hb0]
  nlinarith [hv]

/-- Exact mean and variance bound for n times the conventional estimator. -/
private lemma t49_vber_moments {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hReg : Regular E k q s) (hQ : 4 ≤ q) (hBER : Bernoulli E) :
    mean E.design (fun z => (n:ℝ)*vBER E z) = aVariance E ∧
    var E.design (fun z => (n:ℝ)*vBER E z) ≤ 4*k^8*dAvg E/(n:ℝ) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  let X := fun b z => ∑ i, armVariable E b 2 i z/(marginal E i b)^2
  have he : (fun z => (n:ℝ)*vBER E z) = fun z => (X true z+X false z)/(n:ℝ) := by
    funext z
    simp only [X, vBER, ← Finset.sum_add_distrib, armVariable]
    have hh (i : Fin n) :
        (if z i then E.outcome i z^2 else 0)/marginal E i true^2 +
        (if z i then 0 else E.outcome i z^2)/marginal E i false^2 =
        (if z i=true then E.outcome i z^2 else 0)/marginal E i true^2 +
        (if z i=false then E.outcome i z^2 else 0)/marginal E i false^2 := by
      cases z i <;> simp
    simp_rw [hh]
    field_simp <;> ring
  have hm (b : Bool) : mean E.design (X b) = ∑ i,
      cmean E.design (fun z => z i=b) (fun z => E.outcome i z^2)/marginal E i b := by
    simp only [X, mean_sum, mean_div, armVariable, cmean]
    apply Finset.sum_congr rfl
    intro i _
    change mean E.design (fun z => if z i=b then E.outcome i z^2 else 0) /
        (marginal E i b)^2 =
      (mean E.design (fun z => if z i=b then E.outcome i z^2 else 0) /
        marginal E i b)/marginal E i b
    ring
  have hv (b : Bool) : var E.design (X b) ≤ k^8*(n:ℝ)*dAvg E := by
    have hp (i : Fin n) := regular_marginal_bounds E k q s hReg i b
    have hw : ∀ i, 0 < ((marginal E i b)^2)⁻¹ ∧ ((marginal E i b)^2)⁻¹ ≤ k^2 := by
      intro i
      rw [← inv_pow]
      exact ⟨sq_pos_of_pos (inv_pos.mpr (hp i).2.2.1),
        pow_le_pow_left₀ (inv_nonneg.mpr (hp i).2.2.1.le) (hp i).2.2.2 2⟩
    have hc (i j : Fin n) : |cov E.design (armVariable E b 2 i) (armVariable E b 2 j)| ≤ d E i j*k^4 := by
      by_cases hij : Dependent E i j
      · simpa only [d, hij, if_true, one_mul] using
          (corrected_moment_covariance E k q hReg.1 hReg.2.1 hReg.2.2.2.2.1
            2 (by norm_num; linarith) i j b).2.2.2.2.2.2
      · simp [d, hij, covariance_nonedge E hBER i j hij b 2]
    have hweight := (weighted_variance_absolute E.design (armVariable E b 2)
      (fun i => ((marginal E i b)^2)⁻¹) (k^2) hw).2
    have hx : X b = fun z => ∑ i, ((marginal E i b)^2)⁻¹*armVariable E b 2 i z := by
      funext z; simp only [X, div_eq_mul_inv, mul_comm]
    rw [hx]
    calc
      _ ≤ (k^2)^2*(∑ i, ∑ j, |cov E.design (armVariable E b 2 i) (armVariable E b 2 j)|) := hweight
      _ ≤ (k^2)^2*(∑ i, ∑ j, d E i j*k^4) := by
        gcongr with i j
        exact hc i j
      _ = _ := by
        simp only [dAvg, degree, ← Finset.sum_mul]
        field_simp <;> ring
  constructor
  · rw [he, mean_div, mean_add, hm, hm]
    simp only [aVariance, Finset.sum_add_distrib]
  · rw [he, variance_div]
    have ha : var E.design (fun z => X true z+X false z) ≤
        2*(var E.design (X true)+var E.design (X false)) := by
      have hh := variance_sub_le E.design (X true) (fun z => -X false z)
      have hneg : var E.design (fun z => -X false z) = var E.design (X false) := by
        rw [variance_second_moment, variance_second_moment]
        have hh : mean E.design (fun z => -X false z) = -mean E.design (X false) := by
          simpa using mean_const_mul E.design (-1) (X false)
        simp [hh]
      simpa only [sub_neg_eq_add, hneg] using hh
    calc
      _ ≤ (2*(var E.design (X true)+var E.design (X false)))/(n:ℝ)^2 :=
        div_le_div_of_nonneg_right ha (sq_nonneg _)
      _ ≤ (2*(k^8*(n:ℝ)*dAvg E+k^8*(n:ℝ)*dAvg E))/(n:ℝ)^2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add (hv true) (hv false)) (by norm_num))
          (sq_nonneg _)
      _ = _ := by field_simp <;> ring

private lemma t49_msq_nonneg {n : ℕ} (E : Experiment n) : 0 ≤ msq E := by
  exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Nat.cast_nonneg _)

private lemma t49_mse {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hReg : Regular E k q s) (hQ : 4 ≤ q) (hBER : Bernoulli E) :
    mean E.design (fun z => ((n:ℝ)*vBER E z-aVariance E)^2) ≤
      4*k^8*dAvg E/(n:ℝ) := by
  have hm := t49_vber_moments hn E k q s hReg hQ hBER
  rw [← hm.1, centered_square_mean]
  exact hm.2

/-- Shared MAX/SR lower-tail proof.  The second branch uses the positive margin
before scaling, so it imposes no upper bound on the inflation factor. -/
private lemma t49_inflation_two_alternatives (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hQ : 4 ≤ q)
    (hBER : ∀ t, Bernoulli (S.experiment t)) (b : ℕ → ℝ)
    (hbd : ∀ t, dAvg (S.experiment t) ≤ b t)
    (hmargin : ∀ t, size S t/b t*var (S.experiment t).design (ht (S.experiment t)) ≤
      aVariance (S.experiment t)-msq (S.experiment t))
    (hAlt : LittleO b (fun t => Real.sqrt (size S t)*Real.sqrt (dAvg (S.experiment t))) ∨
      (Restricted S ∧ PositiveLiminf (fun t => msq (S.experiment t)))) :
    Conservative S (fun t z => b t*vBER (S.experiment t) z) := by
  let d := fun t => dAvg (S.experiment t)
  let A := fun t => aVariance (S.experiment t)
  let V := fun t => var (S.experiment t).design (ht (S.experiment t))
  let Z := fun t z => size S t*vBER (S.experiment t) z-A t
  have hn (t) : 0 < size S t := by
    dsimp [size]
    exact_mod_cast S.positive t
  have hd (t) : 0 < d t := lt_of_lt_of_le zero_lt_one (average_degree_at_least_one _ (S.positive t))
  have hb (t) : 0 < b t := (hd t).trans_le (hbd t)
  have hm (t) : msq (S.experiment t) ≤ A t-size S t/b t*V t := by
    dsimp [A, V]; linarith [hmargin t]
  have hZ (t) : mean (S.experiment t).design (fun z => (Z t z)^2) ≤
      4*k^8*d t/size S t := t49_mse (S.positive t) _ k q s (hReg t) hQ (hBER t)
  have he (t z) : size S t/d t*(b t*vBER (S.experiment t) z-V t) =
      b t/d t*(Z t z+(A t-size S t/b t*V t)) := by
    dsimp [Z]
    field_simp [(hb t).ne', (hd t).ne'] <;> ring
  refine ⟨fun _ => 0, ?_, tendsto_const_nhds⟩
  intro ε hε
  rcases hAlt with hsmall | ⟨hrest, c, hc, hevent⟩
  · let Q := fun t z => b t/d t*Z t z
    let R := fun t => b t/(Real.sqrt (size S t)*Real.sqrt (d t))
    have hR : Tendsto R atTop (nhds 0) := hsmall
    have hQm (t) : mean (S.experiment t).design (fun z => (Q t z)^2) ≤ 4*k^8*(R t)^2 := by
      have hsN := Real.sq_sqrt (hn t).le
      have hsD := Real.sq_sqrt (hd t).le
      calc
        _ = (b t/d t)^2*mean (S.experiment t).design (fun z => (Z t z)^2) := by
          simp only [Q, mul_pow, mean_const_mul]
        _ ≤ (b t/d t)^2*(4*k^8*d t/size S t) := mul_le_mul_of_nonneg_left (hZ t) (sq_nonneg _)
        _ = _ := by
          simp only [R, div_pow, mul_pow, hsN, hsD]
          field_simp [(hn t).ne', (hd t).ne'] <;> ring
    have hlim : Tendsto (fun t => 4*k^8*(R t)^2/ε^2) atTop (nhds 0) := by
      have hconst : Tendsto (fun _ : ℕ => 4*k^8) atTop (nhds (4*k^8)) := tendsto_const_nhds
      simpa using (hconst.mul (hR.pow 2)).div_const (ε^2)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    · intro t; exact probability_nonnegative _ _
    · intro t
      calc
        _ ≤ prob (S.experiment t).design (fun z => ε ≤ |Q t z|) := by
          apply finite_probability_mono
          intro z hz
          change size S t/d t*(b t*vBER (S.experiment t) z-V t) ≤ -ε at hz
          rw [he] at hz
          have hnon : 0 ≤ b t/d t*(A t-size S t/b t*V t) :=
            mul_nonneg (div_nonneg (hb t).le (hd t).le)
              ((t49_msq_nonneg _).trans (hm t))
          have hq : Q t z ≤ -ε := by dsimp [Q]; nlinarith
          exact le_trans (by linarith : ε ≤ -Q t z) (neg_le_abs _)
        _ ≤ mean (S.experiment t).design (fun z => (Q t z)^2)/ε^2 := second_moment_tail _ _ ε hε
        _ ≤ _ := div_le_div_of_nonneg_right (hQm t) (sq_nonneg _)
  · have hlim : Tendsto (fun t => (4*k^8*d t/size S t)/c^2) atTop (nhds 0) := by
      have hh : Tendsto (fun t => d t/size S t) atTop (nhds 0) := hrest
      have hconst : Tendsto (fun _ : ℕ => 4*k^8) atTop (nhds (4*k^8)) := tendsto_const_nhds
      have hh' := (hconst.mul hh).div_const (c^2)
      simpa only [mul_zero, zero_div, mul_div_assoc] using hh'
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    · exact Eventually.of_forall (fun t => probability_nonnegative _ _)
    · filter_upwards [hevent] with t ht
      calc
        _ ≤ prob (S.experiment t).design (fun z => c ≤ |Z t z|) := by
          apply finite_probability_mono
          intro z hz
          change size S t/d t*(b t*vBER (S.experiment t) z-V t) ≤ -ε at hz
          rw [he] at hz
          have hbr : 0 < b t/d t := div_pos (hb t) (hd t)
          have hneg : Z t z+(A t-size S t/b t*V t) < 0 := by
            by_contra hnot
            have hnon := mul_nonneg hbr.le (le_of_not_gt hnot)
            linarith
          exact le_trans (by linarith [hm t] : c ≤ -Z t z) (neg_le_abs _)
        _ ≤ mean (S.experiment t).design (fun z => (Z t z)^2)/c^2 := second_moment_tail _ _ c hc
        _ ≤ _ := div_le_div_of_nonneg_right (hZ t) (sq_nonneg _)


theorem maximum_inflation_conservative_proof (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hQ : 4 ≤ q)
    (hBER : ∀ t, Bernoulli (S.experiment t))
    (hAlt : LittleO (fun t => dMax (S.experiment t))
      (fun t => Real.sqrt (size S t)*Real.sqrt (dAvg (S.experiment t))) ∨
      (Restricted S ∧ PositiveLiminf (fun t => msq (S.experiment t)))) :
    Conservative S (fun t => vMAX (S.experiment t)) := by
  exact t49_inflation_two_alternatives S k q s hReg hQ hBER
    (fun t => dMax (S.experiment t))
    (fun t => (t49_max_finite (S.positive t) _ (hBER t)).2)
    (fun t => (t49_max_finite (S.positive t) _ (hBER t)).1) hAlt


theorem maximum_inflation_finite_proof {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (hBER : Bernoulli E) :
    (n:ℝ)/dMax E*var E.design (ht E) ≤ aVariance E-msq E ∧ dAvg E ≤ dMax E := by
  exact t49_max_finite hn E hBER

/-- The elementary symmetric-matrix upper bound also bounds the Rayleigh set. -/
private lemma t50_quad_max {n : ℕ} (hn : 0 < n) (E : Experiment n) (v : Fin n → ℝ) :
    quadD E v ≤ dMax E*(∑ i, v i^2) := by
  have hentry (i j : Fin n) : v i*d E i j*v j ≤ d E i j*((v i^2+v j^2)/2) := by
    have hh := mul_nonneg (t49_d_nonneg E i j) (sq_nonneg (v i-v j))
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
          rw [t49_symm E j i]
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
        mul_le_mul_of_nonneg_right ((t49_max_degree hn E).1 i) (sq_nonneg _))

private lemma t50_rayleigh {n : ℕ} (hn : 0 < n) (E : Experiment n) :
    (∀ v : Fin n → ℝ, quadD E v ≤ lambdaMax E*(∑ i, v i^2)) ∧
    dAvg E ≤ lambdaMax E := by
  let R : Set ℝ := {r | ∃ v : Fin n → ℝ, (∑ i, v i^2)=1 ∧ r=quadD E v}
  have hR : BddAbove R := by
    refine ⟨dMax E, ?_⟩
    rintro r ⟨v, hv, rfl⟩
    simpa only [hv, mul_one] using t50_quad_max hn E v
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
private lemma t50_spectral_margin {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (hBER : Bernoulli E) :
    (n:ℝ)/lambdaMax E*var E.design (ht E) ≤ aVariance E-msq E ∧
      dAvg E ≤ lambdaMax E := by
  have hr := t50_rayleigh hn E
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hl : 0 < lambdaMax E :=
    lt_of_lt_of_le zero_lt_one ((average_degree_at_least_one E hn).trans hr.2)
  let v := fun i => Real.sqrt (sigmaSq E i)
  have hi (i : Fin n) : 0 ≤ sigmaSq E i := variance_nonnegative E.design _
  have hc (i j : Fin n) : cov E.design (t49_U E i) (t49_U E j) ≤ v i*d E i j*v j := by
    by_cases hij : Dependent E i j
    · have hh := (le_abs_self _).trans (covariance_cauchy_schwarz E.design (t49_U E i) (t49_U E j))
      change cov E.design (t49_U E i) (t49_U E j) ≤
        Real.sqrt (sigmaSq E i*sigmaSq E j) at hh
      simpa only [v, d, hij, if_true, mul_one, Real.sqrt_mul (hi i)] using hh
    · simp [d, hij, t49_cov_zero E hBER i j hij]
  have hv : var E.design (fun z => ∑ i, t49_U E i z) ≤ lambdaMax E*(∑ i, sigmaSq E i) := by
    calc
      _ ≤ quadD E v := by
        rw [t49_variance_sum]
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hc i j))
      _ ≤ lambdaMax E*(∑ i, v i^2) := hr.1 v
      _ = _ := by simp only [v, Real.sq_sqrt (hi _)]
  have hnorm : (n:ℝ)*var E.design (ht E) ≤ lambdaMax E*(aVariance E-msq E) := by
    rw [t49_ht, variance_div]
    calc
      _ = var E.design (fun z => ∑ i, t49_U E i z)/(n:ℝ) := by
        field_simp [hnR.ne'] <;> ring
      _ ≤ (lambdaMax E*(∑ i, sigmaSq E i))/(n:ℝ) := div_le_div_of_nonneg_right hv hnR.le
      _ = _ := by rw [mul_div_assoc, t49_contribution_identity E hBER]
  refine ⟨?_, hr.2⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ hl]
  nlinarith [hnorm]


theorem spectral_inflation_conservative_proof (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hQ : 4 ≤ q)
    (hBER : ∀ t, Bernoulli (S.experiment t))
    (hAlt : LittleO (fun t => lambdaMax (S.experiment t))
      (fun t => Real.sqrt (size S t)*Real.sqrt (dAvg (S.experiment t))) ∨
      (Restricted S ∧ PositiveLiminf (fun t => msq (S.experiment t)))) :
    Conservative S (fun t => vSR (S.experiment t)) := by
  exact t49_inflation_two_alternatives S k q s hReg hQ hBER
    (fun t => lambdaMax (S.experiment t))
    (fun t => (t50_spectral_margin (S.positive t) _ (hBER t)).2)
    (fun t => (t50_spectral_margin (S.positive t) _ (hBER t)).1) hAlt

/-- Ceiling estimates, including the boundary cases n=1 and lambda=1. -/
private lemma p1_ceiling_bounds {n : ℕ} (hn : 0 < n) (lam : ℝ)
    (hLam : 0 < lam ∧ lam ≤ 1) :
    let M := ⌈Real.sqrt lam*(n:ℝ)⌉₊
    1 ≤ M ∧ M ≤ n ∧ Real.sqrt lam*(n:ℝ) ≤ M ∧
      lam*(n:ℝ)^2 ≤ (M:ℝ)^2 ∧ (n:ℝ)/(M:ℝ) ≤ 1/Real.sqrt lam := by
  let M := ⌈Real.sqrt lam*(n:ℝ)⌉₊
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.2 hLam.1
  have hs1 : Real.sqrt lam ≤ 1 := Real.sqrt_le_one.2 hLam.2
  have hM : 1 ≤ M := Nat.one_le_ceil_iff.2 (mul_pos hs hnR)
  have hMn : M ≤ n := Nat.ceil_le.2 (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs1 hnR.le)
  have hMlo : Real.sqrt lam*(n:ℝ) ≤ M := Nat.le_ceil _
  have hMR : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsq := Real.sq_sqrt hLam.1.le
  have hMsq : lam*(n:ℝ)^2 ≤ (M:ℝ)^2 := by
    have hh := (sq_le_sq₀ (mul_pos hs hnR).le hMR.le).2 hMlo
    rw [mul_pow, hsq] at hh
    exact hh
  refine ⟨hM, hMn, hMlo, hMsq, ?_⟩
  apply (div_le_div_iff₀ hMR hs).2
  nlinarith

private lemma p1_interferes {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (M : ℕ) (hM : 1 ≤ M) (hp : ∀ i b, 0 < marginal E i b) (l i : Fin n) :
    Interferes ({E with outcome := p1Outcome hn E M} : Experiment n) l i ↔
      l=i ∨ l=⟨0,hn⟩ ∧ i.val < M := by
  let o : Fin n := ⟨0,hn⟩
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hMR : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hA : 0 < (n:ℝ)/(M:ℝ) := div_pos hnR hMR
  constructor
  · rintro (he | ⟨z, z', hagree, hne⟩)
    · exact Or.inl he
    · by_cases hli : l=i
      · exact Or.inl hli
      · have hzi := hagree i (Ne.symm hli)
        have hi : i.val < M := by
          by_contra hi
          apply hne
          simp [p1Outcome, hi]
        have hlo : l=o := by
          by_contra hlo
          have hzo := hagree o (Ne.symm hlo)
          apply hne
          change p1Outcome hn E M i z = p1Outcome hn E M i z'
          simp only [p1Outcome, hi, if_true]
          rw [hzi, show z ⟨0,hn⟩ = z' ⟨0,hn⟩ from hzo]
        exact Or.inr ⟨hlo, hi⟩
  · rintro (he | ⟨rfl, hi⟩)
    · exact Or.inl he
    · refine Or.inr ⟨(fun _ => false), Function.update (fun _ => false) o true, ?_, ?_⟩
      · intro j hj
        simp [o, hj]
      · change p1Outcome hn E M i (fun _ => false) ≠
          p1Outcome hn E M i (Function.update (fun _ => false) o true)
        by_cases hio : i=o
        · subst i
          simp [p1Outcome, o, show 0 < M by omega, bit,
            ne_of_gt hA, ne_of_gt (hp ⟨0,hn⟩ true)]
        · simp [p1Outcome, hi, bit, Function.update_of_ne hio,
            o, ne_of_gt hA, ne_of_gt (hp i false)]

private lemma p1_dependent {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (M : ℕ) (hM : 1 ≤ M) (hp : ∀ i b, 0 < marginal E i b) (i j : Fin n) :
    Dependent ({E with outcome := p1Outcome hn E M} : Experiment n) i j ↔
      i=j ∨ i.val < M ∧ j.val < M := by
  simp only [Dependent, p1_interferes hn E M hM hp]
  constructor
  · rintro ⟨l, hi, hj⟩
    rcases hi with hi | ⟨hl, hi⟩ <;> rcases hj with hj | ⟨hl', hj⟩
    · exact Or.inl (hi.symm.trans hj)
    · have hival : i.val=0 := congrArg Fin.val (hi.symm.trans hl')
      exact Or.inr ⟨by omega, hj⟩
    · have hjval : j.val=0 := congrArg Fin.val (hj.symm.trans hl)
      exact Or.inr ⟨hi, by omega⟩
    · exact Or.inr ⟨hi, hj⟩
  · rintro (rfl | ⟨hi, hj⟩)
    · exact ⟨i, Or.inl rfl, Or.inl rfl⟩
    · exact ⟨⟨0,hn⟩, Or.inr ⟨rfl, hi⟩, Or.inr ⟨rfl, hj⟩⟩

private lemma p1_graph {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (M : ℕ) (hM : 1 ≤ M ∧ M ≤ n) (hp : ∀ i b, 0 < marginal E i b) :
    dAvg ({E with outcome := p1Outcome hn E M} : Experiment n) =
      (M:ℝ)^2/(n:ℝ)+((n:ℝ)-M)/(n:ℝ) := by
  let E' : Experiment n := {E with outcome := p1Outcome hn E M}
  have hrow (i : Fin n) : degree E' i = if i.val < M then (M:ℝ) else 1 := by
    unfold degree d
    simp only [E', p1_dependent hn E M hM.1 hp]
    by_cases hi : i.val < M
    · have he (j : Fin n) : (i=j ∨ i.val < M ∧ j.val < M) ↔ j.val < M := by
        constructor
        · rintro (rfl | ⟨_, hj⟩) <;> assumption
        · intro hj; exact Or.inr ⟨hi, hj⟩
      simp_rw [he]
      rw [SharpnessCompletion.prefix_count M hM.2]
      simp [hi]
    · simp [hi]
  have hrow' (i : Fin n) : (if i.val < M then (M:ℝ) else 1) =
      1+((M:ℝ)-1)*(if i.val < M then 1 else 0) := by split_ifs <;> ring
  change (∑ i, degree E' i)/(n:ℝ) = _
  simp_rw [hrow, hrow']
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, SharpnessCompletion.prefix_count M hM.2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

private lemma p1_bound {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (M : ℕ) (hM : 1 ≤ M) (hp : ∀ i b, 0 ≤ marginal E i b ∧ marginal E i b ≤ 1)
    (i : Fin n) (z : Assignment n) : |p1Outcome hn E M i z| ≤ (n:ℝ)/(M:ℝ) := by
  have hA : 0 ≤ (n:ℝ)/(M:ℝ) := by positivity
  have hbit : |bit (z ⟨0,hn⟩)| ≤ 1 := by cases z ⟨0,hn⟩ <;> norm_num [bit]
  have hcoef : |bit (z i)*marginal E i true-(1-bit (z i))*marginal E i false| ≤ 1 := by
    cases hz : z i
    · simpa [bit, hz, abs_of_nonneg (hp i false).1] using (hp i false).2
    · simpa [bit, hz, abs_of_nonneg (hp i true).1] using (hp i true).2
  by_cases hi : i.val < M
  · simp only [p1Outcome, hi, if_true, abs_mul, abs_of_nonneg hA]
    calc
      _ ≤ ((n:ℝ)/(M:ℝ))*1*1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hbit hA) hcoef
          (abs_nonneg _) (by simpa using hA)
      _ = _ := by ring
  · simp [p1Outcome, hi, hA]

private lemma p1_mean_bit {n : ℕ} (E : Experiment n) (i : Fin n) :
    mean E.design (fun z => bit (z i)) = marginal E i true := by
  unfold bit marginal prob
  congr 1
  funext z
  cases hz : z i <;> simp [hz]

/-- The source's effect is constant; every other active effect is source driven. -/
private lemma p1_effect {n : ℕ} (hn : 0 < n) (E : Experiment n) (M : ℕ)
    (i : Fin n) (z : Assignment n) :
    effect ({E with outcome := p1Outcome hn E M} : Experiment n) i z =
      if i.val < M then
        if i=⟨0,hn⟩ then (n:ℝ)/(M:ℝ)*marginal E i true
        else (n:ℝ)/(M:ℝ)*bit (z ⟨0,hn⟩)
      else 0 := by
  by_cases hi : i.val < M
  · by_cases hio : i=⟨0,hn⟩
    · subst i
      simp [effect, potential, p1Outcome, hi, bit]
    · have hoi : (⟨0,hn⟩ : Fin n) ≠ i := Ne.symm hio
      simp only [effect, potential, p1Outcome, hi, if_true,
        Function.update_self, Function.update_of_ne hoi,
        show bit true=(1:ℝ) from rfl, show bit false=(0:ℝ) from rfl,
        hio, if_false]
      have hpart := marginal_partition E i
      linear_combination ((n:ℝ)/(M:ℝ)*bit (z ⟨0,hn⟩))*hpart
  · simp [effect, potential, p1Outcome, hi]

private lemma p1_eate {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (M : ℕ) (hM : 1 ≤ M ∧ M ≤ n) :
    eate ({E with outcome := p1Outcome hn E M} : Experiment n) = marginal E ⟨0,hn⟩ true := by
  let E' : Experiment n := {E with outcome := p1Outcome hn E M}
  have hm (i : Fin n) : mean E.design (effect E' i) =
      ((n:ℝ)/(M:ℝ)*marginal E ⟨0,hn⟩ true)*(if i.val < M then 1 else 0) := by
    by_cases hi : i.val < M
    · by_cases hio : i=⟨0,hn⟩
      · subst i
        have he : effect E' ⟨0, hn⟩ = fun _ => (n:ℝ)/(M:ℝ)*marginal E ⟨0, hn⟩ true := by
          funext z
          simp [E', p1_effect, hi]
        rw [he, mean_const]
        simp [hi]
      · have he : effect E' i = fun z => (n:ℝ)/(M:ℝ)*bit (z ⟨0,hn⟩) := by
          funext z; simp only [E', p1_effect, hi, if_true, hio, if_false]
        rw [he, mean_const_mul, p1_mean_bit]
        simp [hi]
    · have he : effect E' i = fun _ => 0 := by funext z; simp [E', p1_effect, hi]
      rw [he, mean_const]
      simp [hi]
  change mean E.design (fun z => (∑ i, effect E' i z)/(n:ℝ)) = _
  rw [mean_div, mean_sum]
  simp_rw [hm]
  rw [← Finset.mul_sum, SharpnessCompletion.prefix_count M hM.2]
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hM0 : (M:ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  field_simp [hn0, hM0] <;> ring

private lemma p1_ht {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (M : ℕ) (hM : 1 ≤ M ∧ M ≤ n) (hp : ∀ i b, 0 < marginal E i b)
    (z : Assignment n) :
    ht ({E with outcome := p1Outcome hn E M} : Experiment n) z = bit (z ⟨0,hn⟩) := by
  let E' : Experiment n := {E with outcome := p1Outcome hn E M}
  have hterm (i : Fin n) : t49_U E' i z =
      ((n:ℝ)/(M:ℝ)*bit (z ⟨0,hn⟩))*(if i.val < M then 1 else 0) := by
    by_cases hi : i.val < M
    · simp only [t49_U, show marginal E' i true = marginal E i true from rfl,
        show marginal E' i false = marginal E i false from rfl]
      cases hsource : z ⟨0, hn⟩ <;> cases hz : z i <;>
        simp [E', p1Outcome, hi, hz, bit, hsource] <;>
        field_simp [(hp i false).ne', (hp i true).ne'] <;> ring
    · simp [t49_U, E', p1Outcome, hi]
  rw [t49_ht]
  change (∑ i, t49_U E' i z)/(n:ℝ) = _
  simp_rw [hterm]
  rw [← Finset.mul_sum, SharpnessCompletion.prefix_count M hM.2]
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hM0 : (M:ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  field_simp [hn0, hM0] <;> ring

private lemma p1_hajek_zero {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (M : ℕ) (z : Assignment n) (hz : z ⟨0,hn⟩=false) :
    hajek ({E with outcome := p1Outcome hn E M} : Experiment n) z=0 := by
  let E' : Experiment n := {E with outcome := p1Outcome hn E M}
  have hy (i : Fin n) : E'.outcome i z=0 := by simp [E', p1Outcome, hz, bit]
  change hajek E' z=0
  unfold hajek
  split_ifs <;> simp [muHat, hy]


theorem construction_p1_proof {n : ℕ} (hn : 0 < n) (E : Experiment n) (k q s lam : ℝ)
    (hReg : Regular E k q s) (hLam : 0 < lam ∧ lam ≤ 1) :
    let M := ⌈Real.sqrt lam*(n:ℝ)⌉₊
    let E' : Experiment n := {E with outcome := p1Outcome hn E M}
    dAvg E' = (M:ℝ)^2/(n:ℝ)+((n:ℝ)-M)/(n:ℝ) ∧ lam*(n:ℝ) ≤ dAvg E' ∧
    (∀ i z, |E'.outcome i z| ≤ 1/Real.sqrt lam) ∧
    eate E' = marginal E ⟨0,hn⟩ true ∧
    (∀ z, ht E' z = bit (z ⟨0,hn⟩) ∧ k⁻¹ ≤ |ht E' z-eate E'|) ∧
    k⁻¹ ≤ prob E'.design (fun z => k⁻¹ ≤ |hajek E' z-eate E'|) := by
  let M := ⌈Real.sqrt lam*(n:ℝ)⌉₊
  let E' : Experiment n := {E with outcome := p1Outcome hn E M}
  change dAvg E' = _ ∧ _
  have hceil := p1_ceiling_bounds hn lam hLam
  have hM : 1 ≤ M ∧ M ≤ n := ⟨hceil.1, hceil.2.1⟩
  have hp (i : Fin n) (b : Bool) := regular_marginal_bounds E k q s hReg i b
  have hp0 : ∀ i b, 0 < marginal E i b := fun i b => (hp i b).2.2.1
  have hp01 : ∀ i b, 0 ≤ marginal E i b ∧ marginal E i b ≤ 1 := by
    intro i b
    exact ⟨(hp0 i b).le, (hp i b).2.1.trans (by linarith [inv_pos.mpr hReg.1])⟩
  have hg : dAvg E' = (M:ℝ)^2/(n:ℝ)+((n:ℝ)-M)/(n:ℝ) := p1_graph hn E M hM hp0
  have he : eate E' = marginal E ⟨0,hn⟩ true := p1_eate hn E M hM
  have ht (z) : ht E' z = bit (z ⟨0,hn⟩) := p1_ht hn E M hM hp0 z
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  refine ⟨hg, ?_, ?_, he, ?_, ?_⟩
  · rw [hg, ← add_div]
    have hMn : (M:ℝ) ≤ n := by exact_mod_cast hM.2
    apply (le_div_iff₀ hnR).2
    nlinarith [hceil.2.2.2.1]
  · intro i z
    exact (p1_bound hn E M hM.1 hp01 i z).trans hceil.2.2.2.2
  · intro z
    refine ⟨ht z, ?_⟩
    rw [ht z, he]
    have hpart := marginal_partition E ⟨0,hn⟩
    cases hz : z ⟨0,hn⟩
    · simpa [bit, hz, abs_of_nonneg (hp0 ⟨0,hn⟩ true).le] using (hp ⟨0,hn⟩ true).1
    · have hp1 : 0 ≤ 1-marginal E ⟨0,hn⟩ true := by linarith [(hp0 ⟨0,hn⟩ false).le]
      simpa [bit, hz, abs_of_nonneg hp1] using
        (show k⁻¹ ≤ 1-marginal E ⟨0,hn⟩ true by linarith [(hp ⟨0,hn⟩ false).1])
  · have hinc : ∀ z, z ⟨0,hn⟩=false → k⁻¹ ≤ |hajek E' z-eate E'| := by
      intro z hz
      rw [p1_hajek_zero hn E M z hz, he]
      simpa only [zero_sub, abs_neg, abs_of_nonneg (hp0 ⟨0,hn⟩ true).le] using
        (hp ⟨0,hn⟩ true).1
    calc
      k⁻¹ ≤ marginal E ⟨0,hn⟩ false := (hp ⟨0,hn⟩ false).1
      _ ≤ _ := finite_probability_mono E.design _ _ hinc

end
end AronowAudit.P009.Wave1
