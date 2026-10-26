import AronowAudit.P009.P009_OneSourceCompletion
import AronowAudit.P009.P009_CompleteConditional
import Mathlib.Logic.Equiv.Fintype
import AronowAudit.P009.Wave1.Gap.GP0092B1

/-!
Asymptotic bounds for one-source and complete-randomization designs.
The one-source calculation uses conditional product-law identities and
affected-pair counts. The complete case uses permutation averaging to bound
covariance on disjoint parent sets.
-/

namespace AronowAudit.P009.Wave1
open scoped BigOperators
open Filter
open BernoulliCompletion
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000

private lemma GP0091B1b_one_numerator {n : ℕ} (E : Experiment n)
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

private lemma GP0091B1b_two_numerator {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (f : Assignment n → ℝ) :
    mean E.design (fun z => if z i = a ∧ z j = b then f z else 0) =
      (marginal E i a*marginal E j b) *
        mean E.design (fun z => f (Function.update (Function.update z i a) j b)) := by
  have he : (fun z : Assignment n => if z i = a ∧ z j = b then f z else 0) =
      fun z => if z i = a then (if z j = b then f z else 0) else 0 := by
    funext z; split_ifs <;> simp_all
  rw [he, GP0091B1b_one_numerator E hb i a]
  simp only [Function.update_of_ne (Ne.symm hij)]
  rw [GP0091B1b_one_numerator E hb j b]
  have hu (z : Assignment n) : Function.update (Function.update z j b) i a =
      Function.update (Function.update z i a) j b := by
    funext l
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
      simp_all [Function.update]
  simp_rw [hu]
  ring

private lemma GP0091B1b_two_prob {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool) :
    prob E.design (fun z => z i = a ∧ z j = b) = marginal E i a*marginal E j b := by
  have h := GP0091B1b_two_numerator E hb i j hij a b (fun _ => 1)
  simp only [mean_const, mul_one] at h
  rw [← h]
  unfold prob
  congr 1
  funext z
  split_ifs <;> rfl

private lemma GP0091B1b_two_cmean {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (f : Assignment n → ℝ) :
    cmean E.design (fun z => z i = a ∧ z j = b) f =
      mean E.design (fun z => f (Function.update (Function.update z i a) j b)) := by
  rw [cmean, GP0091B1b_two_prob E hb i j hij]
  calc
    _ = (mean E.design (fun z => if z i = a ∧ z j = b then f z else 0)) /
        (marginal E i a*marginal E j b) := by
      congr 1
      congr 1
      funext z
      split_ifs <;> rfl
    _ = _ := by
      rw [GP0091B1b_two_numerator E hb i j hij]
      exact mul_div_cancel_left₀ _ (mul_ne_zero
        (marginal_pos E hb i a).ne' (marginal_pos E hb j b).ne')

private theorem GP0091B1b_ccov_update {n : ℕ} (E : Experiment n)
    (hBER : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (f g : Assignment n → ℝ) :
    ccov E.design (fun z => z i = a ∧ z j = b) f g =
      cov E.design (fun z => f (Function.update (Function.update z i a) j b))
        (fun z => g (Function.update (Function.update z i a) j b)) := by
  unfold ccov
  rw [GP0091B1b_two_cmean E hBER i j hij,
    GP0091B1b_two_cmean E hBER i j hij,
    GP0091B1b_two_cmean E hBER i j hij]
  rfl

private theorem GP0091B1b_source_ccov {n : ℕ} (hn : 0 < n) (h : ℕ)
    (c : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) (a b : Bool) :
    let E := fairExperiment n (oneSourceOutcome h c)
    ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j) =
      if (0 < i.val ∧ i.val < h) ∧ (0 < j.val ∧ j.val < h)
      then bit a * bit b else 0 := by
  dsimp only
  rw [GP0091B1b_ccov_update _ (SparseCompletion.fair_BER _ _) i j hij]
  let o : Fin n := ⟨0, hn⟩
  by_cases hi : 0 < i.val ∧ i.val < h
  · have hio : i ≠ o := by intro he; have := congrArg Fin.val he; dsimp [o] at this; omega
    by_cases hj : 0 < j.val ∧ j.val < h
    · have hjo : j ≠ o := by intro he; have := congrArg Fin.val he; dsimp [o] at this; omega
      have hf : (fun z : Assignment n =>
          (fairExperiment n (oneSourceOutcome h c)).outcome i
            (Function.update (Function.update z i a) j b)) =
          fun z => 2*bit (z o)*bit a+c i := by
        funext z
        simp [fairExperiment, oneSourceOutcome, hi, o,
          Function.update_of_ne hij, Function.update_of_ne hio.symm,
          Function.update_of_ne hjo.symm]
      have hg : (fun z : Assignment n =>
          (fairExperiment n (oneSourceOutcome h c)).outcome j
            (Function.update (Function.update z i a) j b)) =
          fun z => 2*bit (z o)*bit b+c j := by
        funext z
        simp [fairExperiment, oneSourceOutcome, hj, o,
          Function.update_of_ne hio.symm, Function.update_of_ne hjo.symm]
      rw [hf, hg]
      change cov (fairLaw n) _ _ = _
      rw [covariance_product_formula]
      rw [SparseCompletion.fair_coordinate n o (fun v =>
        (2*bit v*bit a+c i)*(2*bit v*bit b+c j)),
        SparseCompletion.fair_coordinate n o (fun v => 2*bit v*bit a+c i),
        SparseCompletion.fair_coordinate n o (fun v => 2*bit v*bit b+c j)]
      cases a <;> cases b <;> norm_num [bit, hi, hj] <;> ring
    · have hg : (fun z : Assignment n =>
          (fairExperiment n (oneSourceOutcome h c)).outcome j
            (Function.update (Function.update z i a) j b)) = fun _ => bit b+c j := by
        funext z
        simp [fairExperiment, oneSourceOutcome, hj]
      rw [hg]
      simp [cov, mean_const, hi, hj]
  · have hf : (fun z : Assignment n =>
        (fairExperiment n (oneSourceOutcome h c)).outcome i
          (Function.update (Function.update z i a) j b)) = fun _ => bit a+c i := by
      funext z
      simp [fairExperiment, oneSourceOutcome, hi, Function.update_of_ne hij]
    rw [hf]
    simp [cov, mean_const, hi]

private theorem GP0091B1b_source_B2 {n : ℕ} (hn : 0 < n) (b : ℕ)
    (hb : 1 ≤ b ∧ b ≤ n) (c : Fin n → ℝ) :
    B2 (fairExperiment n (oneSourceOutcome b c)) =
      ((b:ℝ)-1)*((b:ℝ)-2)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) := by
  let A : Fin n → Prop := fun i => 0 < i.val ∧ i.val < b
  have hpair (i j : Fin n) : (if j = i then (0 : ℝ) else
      ∑ a : Bool, ∑ d : Bool, (1-2*bit a)*(1-2*bit d)*
        ccov (fairLaw n) (fun z => z i = a ∧ z j = d)
          (oneSourceOutcome b c i) (oneSourceOutcome b c j)) =
      (if A i then 1 else 0)*(if A j then 1 else 0) -
        (if j = i then (if A i then 1 else 0) else 0) := by
    by_cases hji : j = i
    · subst j; simp only [ite_true]; split_ifs <;> norm_num
    · simp only [hji, ite_false]
      have hc := GP0091B1b_source_ccov hn b c i j (Ne.symm hji)
      simp only [fairExperiment] at hc
      simp_rw [hc]
      by_cases hi : A i <;> by_cases hj : A j <;>
        simp only [A] at hi hj ⊢ <;>
        norm_num [hi, hj, bit, Fintype.sum_bool]
  unfold B2
  dsimp only [fairExperiment]
  simp_rw [hpair, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul]
  change (((∑ i : Fin n, if 0 < i.val ∧ i.val < b then (1:ℝ) else 0) *
    (∑ i : Fin n, if 0 < i.val ∧ i.val < b then (1:ℝ) else 0) -
    (∑ i : Fin n, if 0 < i.val ∧ i.val < b then (1:ℝ) else 0)) / _) = _
  rw [OneSourceCompletion.source_count_affected hn b hb]
  change ((b-1:ℝ)*(b-1)-(b-1)) /
    ((n:ℝ)*dAvg (fairExperiment n (oneSourceOutcome b c))) = _
  rw [OneSourceCompletion.source_davg hn b hb c]
  congr 1
  ring

private theorem GP0091B1b_source_msq {n : ℕ} (hn : 0 < n) (b : ℕ)
    (c : Fin n → ℝ) : msq (fairExperiment n (oneSourceOutcome b c)) = 1 := by
  have hm (i : Fin n) :
      mean (fairLaw n) (effect (fairExperiment n (oneSourceOutcome b c)) i) = 1 := by
    by_cases hi : 0 < i.val ∧ i.val < b
    · let o : Fin n := ⟨0, hn⟩
      have hio : o ≠ i := by intro he; have := congrArg Fin.val he; dsimp [o] at this; omega
      have he : effect (fairExperiment n (oneSourceOutcome b c)) i =
          fun z => 2*bit (z o) := by
        funext z
        simp [effect, potential, fairExperiment, oneSourceOutcome, hi,
          Function.update_of_ne hio, bit, o]
      rw [he, SparseCompletion.fair_coordinate n o (fun v => 2*bit v)]
      norm_num [bit]
    · have he : effect (fairExperiment n (oneSourceOutcome b c)) i = fun _ => 1 := by
        funext z
        simp [effect, potential, fairExperiment, oneSourceOutcome, hi, bit]
      rw [he, mean_const]
  unfold msq
  change (∑ i : Fin n, mean (fairLaw n)
    (effect (fairExperiment n (oneSourceOutcome b c)) i)^2)/(n:ℝ) = 1
  simp only [hm, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (by exact_mod_cast hn.ne' : (n:ℝ) ≠ 0)

private theorem GP0091B1b_source_center {n : ℕ} (hn : 0 < n) (b : ℕ)
    (hb : 1 ≤ b ∧ b ≤ n) (c : Fin n → ℝ) (hc : c ⟨0,hn⟩ = -1/4) :
    let E := fairExperiment n (oneSourceOutcome b c)
    msq E/dAvg E-B1 E-B2 E =
      ((n:ℝ)-((b:ℝ)-1)^2)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) := by
  dsimp only
  rw [GP0091B1b_source_msq hn, GP0091B1b_source_B2 hn b hb c,
    (OneSourceCompletion.corrected_one_source_spillover_completed hn b hb c).2.2, hc]
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd := OneSourceCompletion.source_davg hn b hb c
  have hd0 : dAvg (fairExperiment n (oneSourceOutcome b c)) ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (average_degree_at_least_one _ hn)).ne'
  have he : (n:ℝ)+(b:ℝ)*((b:ℝ)-1) ≠ 0 := by rw [← hd]; exact mul_ne_zero hn0 hd0
  field_simp [he, hd0]
  nlinarith [hd]

private theorem GP0091B1b_row_identification (S : Study) (b : ℕ → ℕ)
    (c : (t : ℕ) → Fin (S.N t) → ℝ)
    (hLaw : ∀ t, (S.experiment t).design = fairLaw (S.N t))
    (hOutcome : ∀ t, (S.experiment t).outcome = oneSourceOutcome (b t) (c t))
    (t : ℕ) :
    S.experiment t = fairExperiment (S.N t) (oneSourceOutcome (b t) (c t)) := by
  cases he : S.experiment t with
  | mk P y =>
      have hp : P = fairLaw (S.N t) := by simpa only [he] using hLaw t
      have hy : y = oneSourceOutcome (b t) (c t) := by simpa only [he] using hOutcome t
      cases hp
      cases hy
      rfl

theorem corrected_one_source_limit_proof (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hQ : 4 ≤ q)
    (b : ℕ → ℕ) (hb : ∀ t, 1 ≤ b t ∧ b t ≤ S.N t)
    (c : (t : ℕ) → Fin (S.N t) → ℝ)
    (hSource : ∀ t, c t ⟨0,S.positive t⟩ = -1/4)
    (hLaw : ∀ t, (S.experiment t).design = fairLaw (S.N t))
    (hOutcome : ∀ t, (S.experiment t).outcome = oneSourceOutcome (b t) (c t)) :
    InProbability S (fun t z => size S t/dAvg (S.experiment t)*
      (vBER (S.experiment t) z-var (S.experiment t).design (ht (S.experiment t))) -
        (size S t-((b t:ℝ)-1)^2)/(size S t+(b t:ℝ)*((b t:ℝ)-1))) := by
  have hrow := GP0091B1b_row_identification S b c hLaw hOutcome
  have hBER (t : ℕ) : Bernoulli (S.experiment t) := by
    rw [hrow t]
    exact SparseCompletion.fair_BER _ _
  have hc (t : ℕ) : msq (S.experiment t)/dAvg (S.experiment t)-
      B1 (S.experiment t)-B2 (S.experiment t) =
      (size S t-((b t:ℝ)-1)^2)/(size S t+(b t:ℝ)*((b t:ℝ)-1)) := by
    rw [hrow t]
    exact GP0091B1b_source_center (S.positive t) (b t) (hb t) (c t) (hSource t)
  simpa only [hc] using (variance_bias_limit_proof S k q s hReg hQ hBER).1

private theorem GP0091B1b_mean_mono {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (f g : Ω → ℝ) (h : ∀ z, f z ≤ g z) : mean P f ≤ mean P g :=
  Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (h z) (P.nonneg z))

private theorem GP0091B1b_observed_square {n : ℕ} (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (i : Fin n) :
    mean E.design (fun z => E.outcome i z^2) ≤ k^2 := by
  have hm := finite_moment_interpolation E.design (E.outcome i) 2 (by norm_num) q hr.2.1
  have hn : 0 ≤ mean E.design (fun z => Real.rpow |E.outcome i z| q) :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (E.design.nonneg z) (Real.rpow_nonneg (abs_nonneg _) _))
  have hq : 0 < q := lt_of_lt_of_le (by norm_num) hr.2.1
  have hb := Real.rpow_le_rpow hn (hr.2.2.2.2.1 i) (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hq.le)
  have he : (k^q)^(2/q) = k^2 := by
    rw [← Real.rpow_mul hr.1.le, mul_div_cancel₀ _ hq.ne', Real.rpow_two]
  simp only [Real.rpow_eq_pow] at hb hm
  rw [he] at hb
  simpa only [sq_abs] using hm.trans hb

private theorem GP0091B1b_one_square {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (hBER : Bernoulli E)
    (l i : Fin n) (a : Bool) :
    mean E.design (fun z => E.outcome l (Function.update z i a)^2) ≤ k^4 := by
  have hp := regular_marginal_bounds E k q s hr i a
  have hid := GP0091B1b_one_numerator E hBER i a (fun z => E.outcome l z^2)
  have hle : mean E.design (fun z => if z i = a then E.outcome l z^2 else 0) ≤ k^2 :=
    (GP0091B1b_mean_mono _ _ _ (fun z => by split_ifs <;> first | exact le_rfl | positivity)).trans
      (GP0091B1b_observed_square E k q s hr l)
  have he : mean E.design (fun z => E.outcome l (Function.update z i a)^2) =
      mean E.design (fun z => if z i = a then E.outcome l z^2 else 0) / marginal E i a := by
    apply (eq_div_iff hp.2.2.1.ne').mpr
    rw [mul_comm]
    exact hid.symm
  rw [he]
  calc
    _ ≤ k^2 / marginal E i a := div_le_div_of_nonneg_right hle hp.2.2.1.le
    _ ≤ k^2*k := by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hp.2.2.2 (sq_nonneg k)
    _ ≤ k^4 := by
      have hk := regular_k_ge_two hn E k q s hr
      nlinarith [sq_nonneg (k-1), mul_nonneg (sq_nonneg k) (show 0 ≤ k^2-k by nlinarith)]

private theorem GP0091B1b_two_square {n : ℕ} (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (hBER : Bernoulli E)
    (l i j : Fin n) (hij : i ≠ j) (a b : Bool) :
    mean E.design (fun z => E.outcome l (Function.update (Function.update z i a) j b)^2) ≤ k^4 := by
  have hp := regular_marginal_bounds E k q s hr i a
  have hq := regular_marginal_bounds E k q s hr j b
  have hid := GP0091B1b_two_numerator E hBER i j hij a b (fun z => E.outcome l z^2)
  have hle : mean E.design (fun z => if z i = a ∧ z j = b then E.outcome l z^2 else 0) ≤ k^2 :=
    (GP0091B1b_mean_mono _ _ _ (fun z => by split_ifs <;> first | exact le_rfl | positivity)).trans
      (GP0091B1b_observed_square E k q s hr l)
  have he : mean E.design (fun z => E.outcome l (Function.update (Function.update z i a) j b)^2) =
      mean E.design (fun z => if z i = a ∧ z j = b then E.outcome l z^2 else 0) /
        (marginal E i a*marginal E j b) := by
    apply (eq_div_iff (mul_ne_zero hp.2.2.1.ne' hq.2.2.1.ne')).mpr
    rw [mul_comm]
    exact hid.symm
  rw [he]
  calc
    _ ≤ k^2 / (marginal E i a*marginal E j b) :=
      div_le_div_of_nonneg_right hle (mul_nonneg hp.2.2.1.le hq.2.2.1.le)
    _ ≤ k^2*(k*k) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg k)
      exact mul_le_mul hq.2.2.2 hp.2.2.2 (inv_nonneg.mpr hp.2.2.1.le) hr.1.le
    _ = _ := by ring

private theorem GP0091B1b_mean_bound {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (f : Ω → ℝ) (k : ℝ) (hm : mean P (fun z => f z^2) ≤ k^4) :
    |mean P f| ≤ k^2 := by
  have hv := variance_nonnegative P f
  rw [variance_second_moment] at hv
  apply (sq_le_sq₀ (abs_nonneg _) (sq_nonneg k)).mp
  rw [sq_abs]
  nlinarith

private theorem GP0091B1b_cov_bound {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (f g : Ω → ℝ) (k : ℝ)
    (hf : mean P (fun z => f z^2) ≤ k^4) (hg : mean P (fun z => g z^2) ≤ k^4) :
    |cov P f g| ≤ k^4 := by
  have hvf : var P f ≤ k^4 := by rw [variance_second_moment]; nlinarith [sq_nonneg (mean P f)]
  have hvg : var P g ≤ k^4 := by rw [variance_second_moment]; nlinarith [sq_nonneg (mean P g)]
  have hc := covariance_cauchy_schwarz P f g
  have hs : Real.sqrt (var P f*var P g) ≤ k^4 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    have hm := mul_le_mul hvf hvg (variance_nonnegative P g) (by positivity : 0 ≤ k^4)
    nlinarith
  exact hc.trans hs

private theorem GP0091B1b_xi_bound {n : ℕ} (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (hBER : Bernoulli E)
    (i j : Fin n) (hij : i ≠ j) (a : Bool) : |xi E i j a| ≤ 2*k^2 := by
  unfold xi
  rw [mean_sub]
  exact (abs_sub _ _).trans (by
    have ht := GP0091B1b_mean_bound _ _ k (GP0091B1b_two_square E k q s hr hBER i i j hij a true)
    have hf := GP0091B1b_mean_bound _ _ k (GP0091B1b_two_square E k q s hr hBER i i j hij a false)
    linarith)

private theorem GP0091B1b_xi_zero {n : ℕ} (E : Experiment n)
    (i j : Fin n) (h : ¬ Interferes E j i) (a : Bool) : xi E i j a = 0 := by
  unfold xi
  simp only [outcome_update_of_not_interferes E i j h, sub_self, mean_const]

private theorem GP0091B1b_ybreve_bound {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (hBER : Bernoulli E) (i : Fin n) :
    |yBreve E i| ≤ k^2 := by
  have hm (a : Bool) : |cmean E.design (fun z => z i = a) (E.outcome i)| ≤ k^2 := by
    rw [conditional_observed_eq_potential_mean E hBER]
    exact GP0091B1b_mean_bound _ _ k (GP0091B1b_one_square hn E k q s hr hBER i i a)
  have hp := regular_marginal_bounds E k q s hr i true
  unfold yBreve
  calc
    _ ≤ |(1-marginal E i true)*cmean E.design (fun z => z i = true) (E.outcome i)| +
        |marginal E i true*cmean E.design (fun z => z i = false) (E.outcome i)| := abs_add_le _ _
    _ = (1-marginal E i true)*|cmean E.design (fun z => z i = true) (E.outcome i)| +
        marginal E i true*|cmean E.design (fun z => z i = false) (E.outcome i)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp.2.2.1.le,
        abs_of_nonneg (by linarith [inv_pos.mpr hr.1] : 0 ≤ 1-marginal E i true)]
    _ ≤ (1-marginal E i true)*k^2 + marginal E i true*k^2 := by
      gcongr <;> first | exact hm _ | linarith [inv_pos.mpr hr.1]
    _ = _ := by ring

private theorem GP0091B1b_xibreve_bound {n : ℕ} (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (hBER : Bernoulli E)
    (i j : Fin n) (hij : i ≠ j) : |xiBreve E i j| ≤ 2*k^2 := by
  have hp := regular_marginal_bounds E k q s hr i true
  unfold xiBreve
  calc
    _ ≤ |(1-marginal E i true)*xi E i j true| +
        |marginal E i true*xi E i j false| := abs_add_le _ _
    _ = (1-marginal E i true)*|xi E i j true| +
        marginal E i true*|xi E i j false| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp.2.2.1.le,
        abs_of_nonneg (by linarith [inv_pos.mpr hr.1] : 0 ≤ 1-marginal E i true)]
    _ ≤ (1-marginal E i true)*(2*k^2)+marginal E i true*(2*k^2) := by
      gcongr <;> first | exact GP0091B1b_xi_bound E k q s hr hBER i j hij _ | linarith [inv_pos.mpr hr.1]
    _ = _ := by ring

private theorem GP0091B1b_ccov_nonedge {n : ℕ} (E : Experiment n)
    (hBER : Bernoulli E) (i j : Fin n) (hij : i ≠ j)
    (hdep : ¬ Dependent E i j) (a b : Bool) :
    ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j) = 0 := by
  have hf (l : Fin n) : DependsOn
      (fun z => E.outcome l (Function.update (Function.update z i a) j b))
      {v | Interferes E v l} := by
    intro z z' hz
    apply outcome_dependsOn E l
    intro v hv
    by_cases hvi : v = i <;> by_cases hvj : v = j <;>
      simp_all [Function.update]
  have hg : DependsOn
      (fun z => E.outcome j (Function.update (Function.update z i a) j b))
      {v | Interferes E v i}ᶜ := by
    apply DependsOn.mono _ (hf j)
    intro v hv hi
    exact hdep ⟨v, hi, hv⟩
  rw [GP0091B1b_ccov_update E hBER i j hij, covariance_product_formula,
    mean_product_of_dependsOn E hBER _ _ _ (hf i) hg, sub_self]

private theorem GP0091B1b_magnitude_bounds {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (hBER : Bernoulli E) :
    |B1 E| ≤ 12*k^4*C1 E/dAvg E ∧ |B2 E| ≤ 4*k^4 ∧
      0 ≤ msq E ∧ msq E ≤ 4*k^4 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hd : 0 < dAvg E := lt_of_lt_of_le zero_lt_one (average_degree_at_least_one E hn)
  have hmsq : msq E ≤ 4*k^4 := by
    have hterm (i : Fin n) : mean E.design (effect E i)^2 ≤ 4*k^4 := by
      have hm (a : Bool) : |mean E.design (potential E i a)| ≤ k^2 :=
        GP0091B1b_mean_bound _ _ k (GP0091B1b_one_square hn E k q s hr hBER i i a)
      have he : |mean E.design (effect E i)| ≤ 2*k^2 := by
        rw [show effect E i = fun z => potential E i true z-potential E i false z from rfl, mean_sub]
        exact (abs_sub _ _).trans (by linarith [hm true, hm false])
      have hh := (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ 2*k^2 by positivity)).mpr he
      rw [sq_abs] at hh
      nlinarith
    unfold msq
    apply (div_le_iff₀ hnR).mpr
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_comm] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hb1 (i j : Fin n) : |if j = i then (0:ℝ) else
      xiBreve E i j*xiBreve E j i+2*yBreve E j*(xi E i j true-xi E i j false)| ≤
      12*k^4*I E j i := by
    by_cases hji : j = i
    · simp only [hji, ite_true, abs_zero]
      simp [I, Interferes, show (0:ℝ) ≤ 12*k^4 by positivity]
    · by_cases hi : Interferes E j i
      · rw [if_neg hji, I, if_pos hi]
        have hx := GP0091B1b_xibreve_bound E k q s hr hBER i j (Ne.symm hji)
        have hy := GP0091B1b_xibreve_bound E k q s hr hBER j i hji
        have hyb := GP0091B1b_ybreve_bound hn E k q s hr hBER j
        have hxt := GP0091B1b_xi_bound E k q s hr hBER i j (Ne.symm hji) true
        have hxf := GP0091B1b_xi_bound E k q s hr hBER i j (Ne.symm hji) false
        have hdiff : |xi E i j true-xi E i j false| ≤ 4*k^2 :=
          (abs_sub _ _).trans (by linarith)
        calc
          _ ≤ |xiBreve E i j*xiBreve E j i|+|2*yBreve E j*(xi E i j true-xi E i j false)| := abs_add_le _ _
          _ ≤ (2*k^2)*(2*k^2)+2*(k^2)*(4*k^2) := by
            simp only [abs_mul]; norm_num only [Nat.abs_ofNat]
            gcongr
          _ = _ := by ring
      · simp [hji, I, hi, xiBreve, GP0091B1b_xi_zero E i j hi]
  have hb2 (i j : Fin n) : |if j = i then (0:ℝ) else
      ∑ a : Bool, ∑ b : Bool, (1-2*bit a)*(1-2*bit b)*
        ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j)| ≤
      4*k^4*d E i j := by
    by_cases hji : j = i
    · simp only [hji, ite_true, abs_zero]
      unfold d
      split_ifs <;> positivity
    · by_cases hdep : Dependent E i j
      · rw [if_neg hji, d, if_pos hdep, mul_one]
        have hc (a b : Bool) : |(1-2*bit a)*(1-2*bit b)*
            ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j)| ≤ k^4 := by
          have hh : |ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j)| ≤ k^4 := by
            rw [GP0091B1b_ccov_update E hBER i j (Ne.symm hji)]
            exact GP0091B1b_cov_bound _ _ _ k
              (GP0091B1b_two_square E k q s hr hBER i i j (Ne.symm hji) a b)
              (GP0091B1b_two_square E k q s hr hBER j i j (Ne.symm hji) a b)
          cases a <;> cases b <;> norm_num [bit] at hh ⊢ <;> exact hh
        calc
          _ ≤ ∑ a : Bool, ∑ b : Bool, |(1-2*bit a)*(1-2*bit b)*
              ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j)| :=
            (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _))
          _ ≤ ∑ _a : Bool, ∑ _b : Bool, k^4 :=
            Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hc a b))
          _ = _ := by simp [Fintype.sum_bool]; ring
      · simp [hji, d, hdep, GP0091B1b_ccov_nonedge E hBER i j (Ne.symm hji) hdep]
  refine ⟨?_, ?_, ?_, hmsq⟩
  · unfold B1
    rw [abs_div, abs_of_pos (mul_pos hnR hd)]
    calc
      _ ≤ (∑ i, ∑ j, 12*k^4*I E j i)/((n:ℝ)*dAvg E) :=
        div_le_div_of_nonneg_right
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => hb1 i j)))))
          (mul_nonneg hnR.le hd.le)
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, C1, outgoing]
        ring
  · unfold B2
    rw [abs_div, abs_of_pos (mul_pos hnR hd)]
    calc
      _ ≤ (∑ i, ∑ j, 4*k^4*d E i j)/((n:ℝ)*dAvg E) :=
        div_le_div_of_nonneg_right
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => hb2 i j)))))
          (mul_nonneg hnR.le hd.le)
      _ = _ := by
        simp only [← Finset.mul_sum]
        have he : (∑ i, ∑ j, d E i j) = (n:ℝ)*dAvg E := by
          simp only [dAvg, degree]
          field_simp
        rw [he]
        field_simp
  · unfold msq
    positivity

/-- Self interference supplies the lower bound on C1, independently of design. -/
private theorem GP0091B1b_C1_ge_one {n : ℕ} (hn : 0 < n) (E : Experiment n) :
    1 ≤ C1 E := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hout (i : Fin n) : 1 ≤ outgoing E i := by
    have hI (j : Fin n) : 0 ≤ I E i j := by
      unfold I
      split_ifs <;> norm_num
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hI j)
      (Finset.mem_univ i)
    have hii : I E i i = 1 := by simp [I, Interferes]
    simpa only [hii, outgoing] using hs
  unfold C1
  apply (le_div_iff₀ hnR).mpr
  calc
    1 * (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ ∑ i, outgoing E i := Finset.sum_le_sum (fun i _ => hout i)

/-- An eventual absolute bound by a sequence tending to zero suffices. -/
private theorem GP0091B1b_abs_squeeze (f g : ℕ → ℝ)
    (hg : Tendsto g atTop (nhds 0))
    (hfg : ∀ᶠ t in atTop, |f t| ≤ g t) :
    Tendsto f atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hfg, hg.eventually_lt_const hε] with t ht hsmall
  simpa only [Real.dist_eq, sub_zero] using ht.trans_lt hsmall

private theorem GP0091B1b_inverse_graph_ratio (S : Study)
    (hRatio : Tendsto (fun t => dAvg (S.experiment t)/C1 (S.experiment t))
      atTop atTop) :
    Tendsto (fun t => C1 (S.experiment t)/dAvg (S.experiment t)) atTop (nhds 0) := by
  simpa only [Function.comp_def, inv_div] using (tendsto_inv_atTop_zero.comp hRatio)

-- P009-T12.
theorem corrected_bias_term_comparison_proof (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hQ : 4 ≤ q)
    (hBER : ∀ t, Bernoulli (S.experiment t))
    (hRatio : Tendsto (fun t => dAvg (S.experiment t)/C1 (S.experiment t)) atTop atTop) :
    Tendsto (fun t => msq (S.experiment t)/dAvg (S.experiment t)) atTop (nhds 0) ∧
    Tendsto (fun t => B1 (S.experiment t)) atTop (nhds 0) ∧
    BigO (fun t => B2 (S.experiment t)) (fun _ => 1) ∧
    (Tendsto (fun t => C1 (S.experiment t)/
      (dAvg (S.experiment t)*|B2 (S.experiment t)|)) atTop (nhds 0) →
      (∀ᶠ t in atTop, B2 (S.experiment t) ≠ 0) →
      LittleO (fun t => msq (S.experiment t)/dAvg (S.experiment t))
        (fun t => |B2 (S.experiment t)|) ∧
      LittleO (fun t => B1 (S.experiment t)) (fun t => |B2 (S.experiment t)|)) := by
  have hC (t : ℕ) : 1 ≤ C1 (S.experiment t) := GP0091B1b_C1_ge_one (S.positive t) _
  have hD (t : ℕ) : 0 < dAvg (S.experiment t) :=
    lt_of_lt_of_le (by norm_num) (average_degree_at_least_one _ (S.positive t))
  have hb (t : ℕ) := GP0091B1b_magnitude_bounds (S.positive t)
    (S.experiment t) k q s (hReg t) (hBER t)
  have hR := GP0091B1b_inverse_graph_ratio S hRatio
  have hA (t : ℕ) : msq (S.experiment t) ≤ 4*k^4*C1 (S.experiment t) := by
    exact (hb t).2.2.2.trans
      (by nlinarith [mul_le_mul_of_nonneg_left (hC t) (show 0 ≤ 4*k^4 by positivity)])
  have hU (t : ℕ) : |B1 (S.experiment t)| ≤
      12*k^4*(C1 (S.experiment t)/dAvg (S.experiment t)) := by
    calc
      _ ≤ 12*k^4*C1 (S.experiment t)/dAvg (S.experiment t) := (hb t).1
      _ = _ := by ring
  have hA0 : Tendsto (fun t => msq (S.experiment t)/dAvg (S.experiment t))
      atTop (nhds 0) := by
    apply GP0091B1b_abs_squeeze _ _ (by simpa using hR.const_mul (4*k^4))
    exact Eventually.of_forall (fun t => by
      rw [abs_of_nonneg (div_nonneg (hb t).2.2.1 (hD t).le)]
      simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (hA t) (hD t).le)
  have hU0 : Tendsto (fun t => B1 (S.experiment t)) atTop (nhds 0) :=
    GP0091B1b_abs_squeeze _ _ (by simpa using hR.const_mul (12*k^4))
      (Eventually.of_forall hU)
  have hV : BigO (fun t => B2 (S.experiment t)) (fun _ => 1) := by
    refine ⟨4*k^4+1, by positivity, Eventually.of_forall (fun t => ?_)⟩
    have hv := (hb t).2.1
    simpa only [abs_one, mul_one] using (show |B2 (S.experiment t)| ≤ 4*k^4+1 by linarith)
  refine ⟨hA0, hU0, hV, ?_⟩
  intro hRel hNZ
  have hQA : Tendsto (fun t => 4*k^4*(C1 (S.experiment t)/
      (dAvg (S.experiment t)*|B2 (S.experiment t)|))) atTop (nhds 0) := by
    simpa using hRel.const_mul (4*k^4)
  have hQU : Tendsto (fun t => 12*k^4*(C1 (S.experiment t)/
      (dAvg (S.experiment t)*|B2 (S.experiment t)|))) atTop (nhds 0) := by
    simpa using hRel.const_mul (12*k^4)
  constructor
  · unfold LittleO
    apply GP0091B1b_abs_squeeze _ _ hQA
    filter_upwards [hNZ] with t ht
    have hv : 0 < |B2 (S.experiment t)| := abs_pos.mpr ht
    rw [abs_of_nonneg (div_nonneg
      (div_nonneg (hb t).2.2.1 (hD t).le) hv.le), div_div]
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right (hA t) (mul_nonneg (hD t).le hv.le)
  · unfold LittleO
    apply GP0091B1b_abs_squeeze _ _ hQU
    filter_upwards [hNZ] with t ht
    have hv : 0 < |B2 (S.experiment t)| := abs_pos.mpr ht
    rw [abs_div, abs_of_pos hv]
    calc
      _ ≤ (12*k^4*(C1 (S.experiment t)/dAvg (S.experiment t)))/
          |B2 (S.experiment t)| := div_le_div_of_nonneg_right (hU t) hv.le
      _ = _ := by ring

open CompleteConditional CompleteMixing
set_option backward.isDefEq.respectTransparency false

private def GP0091B1b_uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : Law Ω where
  mass _ := 1/(Fintype.card Ω:ℝ)
  nonneg _ := by positivity
  total := by simp [Finset.sum_const, Fintype.card_ne_zero]

private theorem GP0091B1b_uniform_reindex {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (e : Ω ≃ Ω) (f : Ω → ℝ) :
    mean (GP0091B1b_uniform Ω) (fun z => f (e z)) = mean (GP0091B1b_uniform Ω) f := by
  unfold mean GP0091B1b_uniform
  exact e.sum_comp (fun z => (1/(Fintype.card Ω:ℝ))*f z)

private theorem GP0091B1b_perm_orbit {n : ℕ} (z z' : Assignment n)
    (hc : (Finset.univ.filter (fun i => z i = true)).card =
      (Finset.univ.filter (fun i => z' i = true)).card) :
    ∃ σ : Equiv.Perm (Fin n), relabel σ z = z' := by
  have ht : Fintype.card {i : Fin n // z i = true} =
      Fintype.card {i : Fin n // z' i = true} := by simpa only [Fintype.card_subtype] using hc
  have hf : Fintype.card {i : Fin n // ¬ z i = true} =
      Fintype.card {i : Fin n // ¬ z' i = true} := by
    simp only [Fintype.card_subtype_compl, ht]
  let et := Fintype.equivOfCardEq ht.symm
  let ef := Fintype.equivOfCardEq hf.symm
  let e : Equiv.Perm (Fin n) := (Equiv.sumCompl (fun i => z' i = true)).symm |>.trans
    ((Equiv.sumCongr et ef).trans (Equiv.sumCompl (fun i => z i = true)))
  refine ⟨e, ?_⟩
  funext i
  by_cases hi : z' i = true
  · change z (e i) = z' i
    have he : z (e i) = true := by
      have hei : e i = (et ⟨i,hi⟩).val := by
        dsimp only [e, Equiv.trans_apply]
        rw [Equiv.sumCompl_symm_apply_of_pos (p := fun l : Fin n => z' l = true) (a := i) hi]
        rfl
      rw [hei]
      exact (et ⟨i,hi⟩).property
    rw [he, hi]
  · change z (e i) = z' i
    have he : ¬ z (e i) = true := by
      have hei : e i = (ef ⟨i,hi⟩).val := by
        dsimp only [e, Equiv.trans_apply]
        rw [Equiv.sumCompl_symm_apply_of_neg (p := fun l : Fin n => z' l = true) (a := i) hi]
        rfl
      rw [hei]
      exact (ef ⟨i,hi⟩).property
    cases hz : z (e i) <;> cases hz' : z' i <;> simp_all

private theorem GP0091B1b_perm_average_invariant {n : ℕ} (g : Assignment n → ℝ)
    (z : Assignment n) (τ : Equiv.Perm (Fin n)) :
    mean (GP0091B1b_uniform (Equiv.Perm (Fin n))) (fun σ => g (relabel σ (relabel τ z))) =
      mean (GP0091B1b_uniform (Equiv.Perm (Fin n))) (fun σ => g (relabel σ z)) := by
  let e : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) := {
    toFun := fun σ => Equiv.trans σ τ
    invFun := fun σ => Equiv.trans σ τ.symm
    left_inv := fun σ => by ext i; simp
    right_inv := fun σ => by ext i; simp }
  exact GP0091B1b_uniform_reindex e (fun σ => g (relabel σ z))

private theorem GP0091B1b_perm_average {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (g : Assignment n → ℝ) (z : Assignment n)
    (hz : 0 < E.design.mass z) :
    mean (GP0091B1b_uniform (Equiv.Perm (Fin n))) (fun σ => g (relabel σ z)) =
      mean E.design g := by
  let G := fun z : Assignment n =>
    mean (GP0091B1b_uniform (Equiv.Perm (Fin n))) (fun σ => g (relabel σ z))
  have he : mean E.design G = mean E.design g := by
    rw [CompleteMixing.mean_comm]
    simp_rw [complete_mean_relabel E m hCR]
    exact mean_const _ _
  have hg : mean E.design G = G z := by
    rw [← mean_const E.design (G z)]
    apply mean_support_congr
    intro w hw
    have hc : (Finset.univ.filter (fun i => z i = true)).card =
        (Finset.univ.filter (fun i => w i = true)).card := by
      have hc1 := supported_treated_count E m hCR z hz
      have hc2 := supported_treated_count E m hCR w hw
      have ht (v : Assignment n) : ((Finset.univ.filter (fun i => v i = true)).card:ℝ) =
          ∑ i, bit (v i) := by
        simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
          Nat.cast_one, Nat.cast_zero, bit]

      have hh : ((Finset.univ.filter (fun i => z i = true)).card:ℝ) =
          ((Finset.univ.filter (fun i => w i = true)).card:ℝ) := by rw [ht,ht,hc1,hc2]
      exact_mod_cast hh
    obtain ⟨τ,hτ⟩ := GP0091B1b_perm_orbit z w hc
    dsimp [G]
    rw [← hτ]
    exact GP0091B1b_perm_average_invariant g z τ
  exact hg.symm.trans he

private theorem GP0091B1b_mean_product_bound {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (f g : Ω → ℝ) (K : ℝ) (hf : mean P (fun z => f z^2) ≤ K)
    (hg : mean P (fun z => g z^2) ≤ K) : |mean P (fun z => f z*g z)| ≤ K := by
  have hpos (u : Ω → ℝ) : 0 ≤ mean P (fun z => u z^2) :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (P.nonneg z) (sq_nonneg _))
  have h1 := hpos (fun z => f z+g z)
  have h2 := hpos (fun z => f z-g z)
  have he1 : mean P (fun z => (f z+g z)^2) =
      mean P (fun z => f z^2)+mean P (fun z => g z^2)+2*mean P (fun z => f z*g z) := by
    rw [← mean_add, ← mean_const_mul, ← mean_add]
    congr 1; funext z; ring
  have he2 : mean P (fun z => (f z-g z)^2) =
      mean P (fun z => f z^2)+mean P (fun z => g z^2)-2*mean P (fun z => f z*g z) := by
    rw [← mean_add, ← mean_const_mul, ← mean_sub]
    congr 1; funext z; ring
  rw [he1] at h1
  rw [he2] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem GP0091B1b_perm_extend_avoiding {n : ℕ} (H K : Finset (Fin n))
    (hdis : Disjoint H K) (σ : Equiv.Perm (Fin n))
    (ha : ∀ j ∈ K, σ j ∉ H) :
    ∃ τ : Equiv.Perm (Fin n), (∀ j ∈ K, τ j = σ j) ∧ (∀ i ∈ H, τ i = i) := by
  let f : K → {i : Fin n // i ∉ H} := fun j => ⟨j.val, by
    intro hj; exact Finset.disjoint_left.mp hdis hj j.property⟩
  let g : K → {i : Fin n // i ∉ H} := fun j => ⟨σ j.val, ha j.val j.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun v : {i : Fin n // i ∉ H} => v.val) hab
  have hg : Function.Injective g := by
    intro a b hab; exact Subtype.ext (σ.injective (congrArg Subtype.val hab))
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  let τ := e.extendDomain (Equiv.refl {i : Fin n // i ∉ H})
  refine ⟨τ, ?_, ?_⟩
  · intro j hj
    have hh := congrArg Subtype.val (he ⟨j,hj⟩)
    have hjH : j ∉ H := by intro hh; exact Finset.disjoint_left.mp hdis hh hj
    change e.extendDomain (Equiv.refl {i : Fin n // i ∉ H}) j = σ j
    rw [Equiv.Perm.extendDomain_apply_subtype (p := fun l : Fin n => l ∉ H) (b := j) e (Equiv.refl _) hjH]
    exact hh
  · intro i hi
    exact Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simpa using hi)

private theorem GP0091B1b_nohit_product {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (H K : Finset (Fin n)) (hdis : Disjoint H K)
    (f g : Assignment n → ℝ) (hf : DependsOn f (H : Set (Fin n)))
    (hg : DependsOn g (K : Set (Fin n))) (σ : Equiv.Perm (Fin n))
    (ha : ∀ j ∈ K, σ j ∉ H) :
    mean E.design (fun z => f z*g (relabel σ z)) = mean E.design (fun z => f z*g z) := by
  obtain ⟨τ, htK, htH⟩ := GP0091B1b_perm_extend_avoiding H K hdis σ ha
  have he (z : Assignment n) : g (relabel σ z) = g (relabel τ z) := by
    apply hg; intro j hj; dsimp [relabel]; rw [htK j hj]
  have hfe (z : Assignment n) : f (relabel τ z) = f z := by
    apply hf; intro i hi; dsimp [relabel]; rw [htH i hi]
  have hp : (fun z => f z*g (relabel σ z)) =
      fun z => f (relabel τ z)*g (relabel τ z) := by
    funext z
    rw [he, hfe]
  rw [hp]
  exact complete_mean_relabel E m hCR τ (fun z => f z*g z)

private theorem GP0091B1b_perm_point {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    mean (GP0091B1b_uniform (Equiv.Perm (Fin n)))
      (fun σ => if σ j = i then (1:ℝ) else 0) = 1/(n:ℝ) := by
  let P := GP0091B1b_uniform (Equiv.Perm (Fin n))
  let p := fun i : Fin n => mean P (fun σ => if σ j = i then (1:ℝ) else 0)
  have heq (l : Fin n) : p l = p i := by
    let e : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) := {
      toFun := fun σ => Equiv.trans σ (Equiv.swap i l)
      invFun := fun σ => Equiv.trans σ (Equiv.swap i l)
      left_inv := fun σ => by ext a; simp
      right_inv := fun σ => by ext a; simp }
    have he : (fun σ : Equiv.Perm (Fin n) => if (e σ) j = i then (1:ℝ) else 0) =
        fun σ => if σ j = l then 1 else 0 := by
      funext σ
      have hh : (e σ) j = i ↔ σ j = l := by
        change Equiv.swap i l (σ j) = i ↔ σ j = l
        rw [Equiv.swap_apply_eq_iff]
        simp
      simp only [hh]
    have h := GP0091B1b_uniform_reindex e (fun σ => if σ j = i then (1:ℝ) else 0)
    rw [he] at h
    exact h
  have hs : ∑ l, p l = 1 := by
    rw [← mean_sum]
    have he : (fun σ : Equiv.Perm (Fin n) => ∑ l : Fin n, if σ j = l then (1:ℝ) else 0) = fun _ => 1 := by
      funext σ; simp
    rw [he, mean_const]
  simp_rw [heq] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  exact (eq_div_iff (by exact_mod_cast hn.ne' : (n:ℝ) ≠ 0)).mpr (by linarith)

private theorem GP0091B1b_mean_finset {Ω ι : Type*} [Fintype Ω] (P : Law Ω)
    (A : Finset ι) (X : ι → Ω → ℝ) :
    mean P (fun z => ∑ i ∈ A, X i z) = ∑ i ∈ A, mean P (X i) := by
  unfold mean
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- Average over uniform coordinate permutations. Relabeling the second block
has constant average on the complete-design support. If its image avoids the
first block, extend that relabeling while fixing the first block, so the product
mean is unchanged. Only intersecting images contribute; their expected number
of intersections is |H||K|/n. Each product-mean difference is bounded by 2B. -/
private theorem GP0091B1b_complete_disjoint_cov {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (H K : Finset (Fin n)) (hdis : Disjoint H K)
    (f g : Assignment n → ℝ) (hf : DependsOn f (H : Set (Fin n)))
    (hg : DependsOn g (K : Set (Fin n))) (B : ℝ) (hB : 0 ≤ B)
    (hf2 : mean E.design (fun z => f z^2) ≤ B)
    (hg2 : mean E.design (fun z => g z^2) ≤ B) :
    |cov E.design f g| ≤ 2*B*(H.card:ℝ)*(K.card:ℝ)/(n:ℝ) := by
  let P := GP0091B1b_uniform (Equiv.Perm (Fin n))
  let T := fun σ : Equiv.Perm (Fin n) =>
    mean E.design (fun z => f z*g z)-mean E.design (fun z => f z*g (relabel σ z))
  let R := fun σ : Equiv.Perm (Fin n) =>
    ∑ j ∈ K, ∑ i ∈ H, if σ j = i then (1:ℝ) else 0
  have hcov : cov E.design f g = mean P T := by
    rw [covariance_product_formula]
    dsimp [T]
    rw [mean_sub, mean_const, ← CompleteMixing.mean_comm]
    have he : mean E.design (fun z => mean P (fun σ => f z*g (relabel σ z))) =
        mean E.design f*mean E.design g := by
      calc
        _ = mean E.design (fun z => f z*mean P (fun σ => g (relabel σ z))) := by
          simp_rw [mean_const_mul]
        _ = mean E.design (fun z => f z*mean E.design g) := by
          apply mean_support_congr
          intro z hz
          rw [GP0091B1b_perm_average E m hCR g z hz]
        _ = _ := by
          simp only [mul_comm _ (mean E.design g)]
          rw [mean_const_mul]
    rw [he]
  have ht (σ : Equiv.Perm (Fin n)) : |T σ| ≤ 2*B*R σ := by
    by_cases ha : ∀ j ∈ K, σ j ∉ H
    · have he := GP0091B1b_nohit_product E m hCR H K hdis f g hf hg σ ha
      dsimp [T]
      rw [he, sub_self, abs_zero]
      dsimp [R]
      positivity
    · push_neg at ha
      obtain ⟨j,hj,hji⟩ := ha
      have hR : 1 ≤ R σ := by
        have he1 : (1:ℝ) ≤ ∑ i ∈ H, if σ j = i then (1:ℝ) else 0 := by
          simpa using Finset.single_le_sum (f := fun i => if σ j = i then (1:ℝ) else 0)
            (fun i _ => by positivity) hji
        exact he1.trans (Finset.single_le_sum
          (f := fun l => ∑ i ∈ H, if σ l = i then (1:ℝ) else 0)
          (fun l _ => by positivity) hj)
      have h1 := GP0091B1b_mean_product_bound E.design f g B hf2 hg2
      have h2 := GP0091B1b_mean_product_bound E.design f (fun z => g (relabel σ z)) B hf2
        (by rw [complete_mean_relabel E m hCR σ (fun z => g z^2)]; exact hg2)
      calc
        _ ≤ |mean E.design (fun z => f z*g z)|+
            |mean E.design (fun z => f z*g (relabel σ z))| := abs_sub _ _
        _ ≤ 2*B := by linarith
        _ ≤ _ := by nlinarith
  rw [hcov]
  calc
    _ ≤ mean P (fun σ => |T σ|) := mean_abs_le P T
    _ ≤ mean P (fun σ => 2*B*R σ) := CompleteConditional.mean_mono P _ _ ht
    _ = 2*B*(H.card:ℝ)*(K.card:ℝ)/(n:ℝ) := by
      rw [mean_const_mul]
      dsimp [R, P]
      rw [GP0091B1b_mean_finset]
      simp_rw [GP0091B1b_mean_finset, GP0091B1b_perm_point hn]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

private theorem GP0091B1b_complete_arm_variance {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (k q s : ℝ) (hr : Regular E k q s) (b : Bool) :
    var E.design (muHat E b) ≤ k^4*dAvg E/(n:ℝ)+2*k^4*C1 E^2/(n:ℝ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  let H := fun i => Finset.univ.filter (fun l => Interferes E l i)
  have hm (i : Fin n) : mean E.design (fun z => armVariable E b 1 i z^2) ≤ k^2 := by
    apply le_trans (GP0091B1b_mean_mono _ _ (fun z => E.outcome i z^2) _)
      (GP0091B1b_observed_square E k q s hr i)
    intro z
    by_cases hz : z i = b <;> simp [armVariable, hz, sq_nonneg]
  have hc (i j : Fin n) : |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤
      d E i j*k^2+2*k^2*(incoming E i:ℝ)*(incoming E j:ℝ)/(n:ℝ) := by
    by_cases hdep : Dependent E i j
    · have hh := (corrected_moment_covariance E k q hr.1 hr.2.1 hr.2.2.2.2.1
        1 (by simpa using hr.2.1) i j b).2.2.2.2.2.2
      simp only [show 2*1=2 by norm_num] at hh
      rw [d, if_pos hdep, one_mul]
      exact hh.trans (le_add_of_nonneg_right (by positivity))
    · have hdis : Disjoint (H i) (H j) := by
        apply Finset.disjoint_left.mpr
        intro l hl hl'
        exact hdep ⟨l, (Finset.mem_filter.mp hl).2, (Finset.mem_filter.mp hl').2⟩
      have hh := GP0091B1b_complete_disjoint_cov hn E m hCR (H i) (H j) hdis
        (armVariable E b 1 i) (armVariable E b 1 j)
        (by intro z z' hz; apply arm_dependsOn E i b 1
            intro l hl; exact hz l (by simp [H, hl]))
        (by intro z z' hz; apply arm_dependsOn E j b 1
            intro l hl; exact hz l (by simp [H, hl]))
        (k^2) (sq_nonneg k) (hm i) (hm j)
      simpa only [d, hdep, ite_false, zero_mul, zero_add, H, incoming] using hh
  have he : muHat E b = fun z => (∑ i, (marginal E i b)⁻¹*armVariable E b 1 i z)/(n:ℝ) := by
    funext z
    simp only [muHat, armVariable, pow_one, div_eq_mul_inv]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, variance_div]
  have hw := weighted_variance_absolute E.design (armVariable E b 1)
    (fun i => (marginal E i b)⁻¹) k (fun i =>
      ⟨inv_pos.mpr (regular_marginal_bounds E k q s hr i b).2.2.1,
        (regular_marginal_bounds E k q s hr i b).2.2.2⟩)
  have hsumD : (∑ i, ∑ j, d E i j*k^2) = (n:ℝ)*dAvg E*k^2 := by
    simp only [← Finset.sum_mul, dAvg, degree]
    field_simp
  have hsumC : (∑ i, ∑ j, 2*k^2*(incoming E i:ℝ)*(incoming E j:ℝ)/(n:ℝ)) =
      (2*k^2/(n:ℝ))*((n:ℝ)*C1 E)^2 := by
    simp only [← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul,
      MixingBasics.sum_incoming hn E]
    ring
  calc
    _ ≤ (k^2*(∑ i, ∑ j, |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)|))/(n:ℝ)^2 :=
      div_le_div_of_nonneg_right hw.2 (sq_nonneg _)
    _ ≤ (k^2*(∑ i, ∑ j, (d E i j*k^2+2*k^2*(incoming E i:ℝ)*(incoming E j:ℝ)/(n:ℝ))))/(n:ℝ)^2 := by
      gcongr with i j
      exact hc i j
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [hsumD, hsumC]
      field_simp
      <;> ring

private theorem GP0091B1b_complete_bias {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (k q s : ℝ) (hr : Regular E k q s) :
    |adse E-eate E| ≤ 4*k^2*C1 E/(n:ℝ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hb (i : Fin n) (b : Bool) :
      |cmean E.design (fun z => z i = b) (potential E i b)-mean E.design (potential E i b)| ≤
        2*k^2*(incoming E i:ℝ)/(n:ℝ) := by
    let H := (Finset.univ.filter (fun l => Interferes E l i)).erase i
    have hF : DependsOn (potential E i b) (H : Set (Fin n)) := by
      intro z z' hz
      apply outcome_dependsOn E i
      intro l hl
      by_cases hli : l = i
      · subst l; simp
      · simp only [potential, Function.update_of_ne hli]
        exact hz l (by simp [H, hli, hl])
    have hi : i ∉ H := by simp [H]
    have hp := regular_marginal_bounds E k q s hr i b
    have hpot : mean E.design (fun z => |potential E i b z|) ≤ k :=
      mean_abs_of_moment E.design _ k s hr.1 hr.2.2.1 (hr.2.2.2.2.2 i b)
    have hk0 : 0 ≤ k := hr.1.le
    have hpinv0 : 0 ≤ (marginal E i b)⁻¹ := inv_nonneg.mpr hp.2.2.1.le
    have hpot0 : 0 ≤ mean E.design (fun z => |potential E i b z|) :=
      Finset.sum_nonneg (fun z _ => mul_nonneg (E.design.nonneg z) (abs_nonneg _))
    have hcard : (H.card:ℝ) ≤ incoming E i := by
      exact_mod_cast (Finset.card_erase_le (s := Finset.univ.filter (fun l => Interferes E l i)) (a := i))
    calc
      _ ≤ (2*(H.card:ℝ)/(n:ℝ))*(marginal E i b)⁻¹*
          mean E.design (fun z => |potential E i b z|) :=
        CompleteConditional.complete_conditional_mean_bound E m hCR H i hi _ hF b hp.2.2.1
      _ ≤ (2*(incoming E i:ℝ)/(n:ℝ))*k*k := by
        gcongr <;> first | exact hp.2.2.2 | positivity
      _ = _ := by ring
  have hE : eate E = (∑ i, (mean E.design (potential E i true)-
      mean E.design (potential E i false)))/(n:ℝ) := by
    change mean E.design (fun z => (∑ i, effect E i z)/(n:ℝ)) = _
    rw [mean_div, mean_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact mean_sub E.design (potential E i true) (potential E i false)
  have he : adse E-eate E = (∑ i,
      ((cmean E.design (fun z => z i = true) (potential E i true)-mean E.design (potential E i true))-
      (cmean E.design (fun z => z i = false) (potential E i false)-mean E.design (potential E i false))))/(n:ℝ) := by
    simp only [adse, hE, conditional_potential_eq_observed,
      Finset.sum_sub_distrib, sub_div]
    ring
  rw [he, abs_div, abs_of_pos hnR]
  calc
    _ ≤ (∑ i, (|cmean E.design (fun z => z i = true) (potential E i true)-mean E.design (potential E i true)|+
        |cmean E.design (fun z => z i = false) (potential E i false)-mean E.design (potential E i false)|))/(n:ℝ) :=
      div_le_div_of_nonneg_right ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ => abs_sub _ _))) hnR.le
    _ ≤ (∑ i, (2*k^2*(incoming E i:ℝ)/(n:ℝ)+2*k^2*(incoming E i:ℝ)/(n:ℝ)))/(n:ℝ) := by
      gcongr with i
      · exact hb i true
      · exact hb i false
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum,
        MixingBasics.sum_incoming hn E]
      field_simp
      <;> ring

private theorem GP0091B1b_complete_ht_hajek {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (z : Assignment n) (hz : 0 < E.design.mass z) : ht E z = hajek E z := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hCR.1.ne'
  have hnmR : (n:ℝ)-(m:ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt (by exact_mod_cast hCR.2.1 : (m:ℝ) < n))
  have htreated := CompleteConditional.supported_treated_count E m hCR z hz
  have htrue : nHat E true z = n := by
    simp only [nHat, CompleteConditional.complete_marginal_true E m hCR,
      ← Finset.sum_div]
    have he : (∑ i, if z i = true then (1:ℝ) else 0) = m := by
      calc
        _ = ∑ i, bit (z i) := by
          apply Finset.sum_congr rfl
          intro i _
          cases z i <;> norm_num [bit]
        _ = _ := htreated
    rw [he]
    field_simp
  have hfalse : nHat E false z = n := by
    simp only [nHat, CompleteConditional.complete_marginal_false E m hCR,
      ← Finset.sum_div]
    have he : (∑ i, if z i = false then (1:ℝ) else 0) = (n:ℝ)-m := by
      have he (i : Fin n) : (if z i = false then (1:ℝ) else 0) = 1-bit (z i) := by
        cases z i <;> norm_num [bit]
      simp only [he, Finset.sum_sub_distrib, htreated, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [he]
    field_simp
    <;> ring
  have ha : ArmsNonempty E z := by simp only [ArmsNonempty, htrue, hfalse]; exact ⟨hnR, hnR⟩
  simp only [hajek, ha, ite_true, htrue, hfalse]
  unfold ht
  field_simp

/-- Finite bias/variance decomposition, valid without any design restriction. -/
private theorem GP0091B1b_mse_identity {Ω : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → ℝ) (a : ℝ) :
    mean P (fun z => (X z-a)^2) = var P X+(mean P X-a)^2 := by
  have he : (fun z => (X z-a)^2) = fun z => X z^2-(2*a)*X z+a^2 := by
    funext z
    ring
  rw [he, mean_add, mean_sub, mean_const_mul, mean_const, variance_second_moment]
  ring

private theorem GP0091B1b_rate_square (S : Study) (t : ℕ) :
    dAvg (S.experiment t)/size S t ≤
      (bernoulliRate S t+C1 (S.experiment t)/Real.sqrt (size S t))^2 ∧
    C1 (S.experiment t)^2/size S t ≤
      (bernoulliRate S t+C1 (S.experiment t)/Real.sqrt (size S t))^2 := by
  have hn : 0 < size S t := by dsimp [size]; exact_mod_cast S.positive t
  have hC : 0 ≤ C1 (S.experiment t) :=
    le_trans (by norm_num) (GP0091B1b_C1_ge_one (S.positive t) _)
  have hr := BernoulliCompletion.bernoulli_rate_pos S t
  have hs := BernoulliCompletion.bernoulli_rate_square S t
  have hc : (C1 (S.experiment t)/Real.sqrt (size S t))^2 =
      C1 (S.experiment t)^2/size S t := by
    rw [div_pow, Real.sq_sqrt hn.le]
  have hcr : 0 ≤ C1 (S.experiment t)/Real.sqrt (size S t) := by positivity
  constructor <;> nlinarith [mul_nonneg hr.le hcr]

private theorem GP0091B1b_HT_mse_bound (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hCR : CompleteSequence S) (t : ℕ) :
    mean (S.experiment t).design (fun z =>
      (ht (S.experiment t) z-eate (S.experiment t))^2) ≤
      (28*k^4+1)*
        (bernoulliRate S t+C1 (S.experiment t)/Real.sqrt (size S t))^2 := by
  obtain ⟨p, hp, hp1, hcomplete⟩ := hCR
  let E := S.experiment t
  let n := size S t
  let C := C1 E
  let D := dAvg E
  let a := bernoulliRate S t+C/Real.sqrt n
  have hn : 0 < n := by dsimp [n, size]; exact_mod_cast S.positive t
  have hn1 : 1 ≤ n := by
    dsimp [n, size]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (S.positive t).ne')
  have hC : 0 ≤ C := le_trans (by norm_num) (GP0091B1b_C1_ge_one (S.positive t) E)
  have hk : 0 < k := (hReg t).1
  have hbias : |adse E-eate E| ≤ 4*k^2*C/n :=
    GP0091B1b_complete_bias (S.positive t) E ⌊p*size S t⌋₊ (hcomplete t) k q s (hReg t)
  have hv1 : var E.design (muHat E true) ≤ k^4*D/n+2*k^4*C^2/n :=
    GP0091B1b_complete_arm_variance (S.positive t) E ⌊p*size S t⌋₊ (hcomplete t) k q s (hReg t) true
  have hv0 : var E.design (muHat E false) ≤ k^4*D/n+2*k^4*C^2/n :=
    GP0091B1b_complete_arm_variance (S.positive t) E ⌊p*size S t⌋₊ (hcomplete t) k q s (hReg t) false
  have hv : var E.design (ht E) ≤ 4*k^4*D/n+8*k^4*C^2/n := by
    have hh := BernoulliCompletion.variance_sub_le E.design (muHat E true) (muHat E false)
    calc
      _ ≤ 2*(var E.design (muHat E true)+var E.design (muHat E false)) := hh
      _ ≤ 2*((k^4*D/n+2*k^4*C^2/n)+(k^4*D/n+2*k^4*C^2/n)) := by gcongr
      _ = _ := by ring
  have hm : mean E.design (ht E) = adse E := by
    apply ht_unbiased_ADSE E
    intro i
    exact ⟨(BernoulliCompletion.regular_marginal_bounds E k q s (hReg t) i true).2.2.1,
      (BernoulliCompletion.regular_marginal_bounds E k q s (hReg t) i false).2.2.1⟩
  have hbias2 : (adse E-eate E)^2 ≤ 16*k^4*C^2/n := by
    have hh : (adse E-eate E)^2 ≤ (4*k^2*C/n)^2 := by
      have h := (sq_le_sq₀ (abs_nonneg (adse E-eate E))
        (show 0 ≤ 4*k^2*C/n by positivity)).mpr hbias
      simpa only [sq_abs] using h
    calc
      _ ≤ (4*k^2*C/n)^2 := hh
      _ = 16*k^4*C^2/n^2 := by ring
      _ ≤ 16*k^4*C^2/n := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hn) hn).mpr
        have hN : 0 ≤ 16*k^4*C^2 := by positivity
        exact mul_le_mul_of_nonneg_left (by nlinarith : n ≤ n^2) hN
  have hparts := GP0091B1b_rate_square S t
  have hDsq : D/n ≤ a^2 := hparts.1
  have hCsq : C^2/n ≤ a^2 := hparts.2
  have hDmul := mul_le_mul_of_nonneg_left hDsq (show 0 ≤ 4*k^4 by positivity)
  have hCmul := mul_le_mul_of_nonneg_left hCsq (show 0 ≤ 8*k^4+16*k^4 by positivity)
  rw [GP0091B1b_mse_identity, hm]
  change var E.design (ht E)+(adse E-eate E)^2 ≤ (28*k^4+1)*a^2
  calc
    _ ≤ (4*k^4*D/n+8*k^4*C^2/n)+16*k^4*C^2/n := add_le_add hv hbias2
    _ = 4*k^4*(D/n)+(8*k^4+16*k^4)*(C^2/n) := by ring
    _ ≤ 4*k^4*a^2+(8*k^4+16*k^4)*a^2 := add_le_add hDmul hCmul
    _ ≤ _ := by nlinarith [sq_nonneg a]

-- P009-T42.
theorem complete_consistency_proof (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hCR : CompleteSequence S)
    (hRestricted : Restricted S)
    (hC1 : LittleO (fun t => C1 (S.experiment t)) (fun t => Real.sqrt (size S t))) :
    EstimatorClaims S (fun t => eate (S.experiment t))
      (fun t => bernoulliRate S t + C1 (S.experiment t)/Real.sqrt (size S t)) := by
  let a := fun t => bernoulliRate S t+C1 (S.experiment t)/Real.sqrt (size S t)
  let C0 := 28*k^4+1
  have hk : 0 < k := (hReg 0).1
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have ha (t : ℕ) : 0 < a t := by
    have hC : 0 ≤ C1 (S.experiment t) :=
      le_trans (by norm_num) (GP0091B1b_C1_ge_one (S.positive t) _)
    have hc : 0 ≤ C1 (S.experiment t)/Real.sqrt (size S t) := by positivity
    exact add_pos_of_pos_of_nonneg (BernoulliCompletion.bernoulli_rate_pos S t) hc
  have hM (t : ℕ) : mean (S.experiment t).design (fun z =>
      (ht (S.experiment t) z-eate (S.experiment t))^2) ≤ C0*(a t)^2 :=
    GP0091B1b_HT_mse_bound S k q s hReg hCR t
  have hHT : Op S (fun t z => ht (S.experiment t) z-eate (S.experiment t)) a :=
    BernoulliCompletion.op_of_second_moment S _ a C0 hC0 ha hM
  have hHJmom (t : ℕ) : mean (S.experiment t).design (fun z =>
      (hajek (S.experiment t) z-eate (S.experiment t))^2) =
      mean (S.experiment t).design (fun z =>
        (ht (S.experiment t) z-eate (S.experiment t))^2) := by
    obtain ⟨p, hp, hp1, hcomplete⟩ := hCR
    apply CompleteConditional.mean_support_congr
    intro z hz
    rw [GP0091B1b_complete_ht_hajek (S.positive t) (S.experiment t)
      ⌊p*size S t⌋₊ (hcomplete t) z hz]
  have hHJ : Op S (fun t z => hajek (S.experiment t) z-eate (S.experiment t)) a := by
    apply BernoulliCompletion.op_of_second_moment S _ a C0 hC0 ha
    intro t
    rw [hHJmom t]
    exact hM t
  have hazero : Tendsto a atTop (nhds 0) := by
    have hr := BernoulliCompletion.bernoulli_rate_zero S hRestricted
    have hc : Tendsto (fun t => C1 (S.experiment t)/Real.sqrt (size S t))
        atTop (nhds 0) := hC1
    simpa only [add_zero] using hr.add hc
  exact ⟨BernoulliCompletion.probability_of_op_zero S _ a hazero hHT,
    BernoulliCompletion.probability_of_op_zero S _ a hazero hHJ, hHT, hHJ⟩

end
end AronowAudit.P009.Wave1
