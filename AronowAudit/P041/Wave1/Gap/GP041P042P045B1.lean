import AronowAudit.P041.P041_OrderCountCompletion
import AronowAudit.P041.P041_Wald
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-! Gaussian probability bounds, balanced scrutiny, and significance tiers.
The Gaussian bounds use finite Taylor polynomials and rational arithmetic;
the scrutiny calculation averages over the actual balanced-subset law. -/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace AronowAudit.P041.Wave1

/-! Gaussian p-value approximations. -/

def normal_expPoly (n : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), (-u)^j / (j.factorial:ℝ)

def normal_intPoly (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), (-1/2:ℝ)^j * x^(2*j+1) / ((j.factorial:ℝ)*(2*j+1))

lemma normal_iter_exp (n : ℕ) : iteratedDeriv n Real.exp = Real.exp := by
  simpa using iteratedDeriv_exp_const_mul n 1

lemma normal_exp_taylor (n : ℕ) (u : ℝ) (hu : u ≠ 0) :
    taylorWithinEval Real.exp n (uIcc 0 (-u)) 0 (-u) = normal_expPoly n u := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by simpa using hu))
    (Real.contDiff_exp (n := j)).contDiffAt (left_mem_uIcc), normal_iter_exp]
  simp [Real.exp_zero, div_eq_mul_inv, mul_comm]

lemma normal_exp_bracket (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    normal_expPoly (2*n+1) u ≤ Real.exp (-u) ∧ Real.exp (-u) ≤ normal_expPoly (2*n) u := by
  by_cases hzero : u = 0
  · subst u
    have hz (k : ℕ) : normal_expPoly k 0 = 1 := by
      unfold normal_expPoly
      calc
        _ = (-(0:ℝ))^0 / (Nat.factorial 0:ℝ) :=
          Finset.sum_eq_single 0 (by intro b hb hb0; simp [hb0]) (by simp)
        _ = 1 := by norm_num
    simp [hz]
  have hx : (0:ℝ) ≠ -u := by intro h; apply hzero; linarith
  have rem (k : ℕ) := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.exp) (n := k) hx Real.contDiff_exp.contDiffOn
  obtain ⟨a,ha,he⟩ := rem (2*n+1)
  obtain ⟨b,hb,hf⟩ := rem (2*n)
  rw [normal_exp_taylor _ _ hzero, normal_iter_exp] at he hf
  simp only [sub_zero] at he hf
  constructor
  · have hp : 0 ≤ Real.exp a * (-u)^(2*n+1+1) / ((2*n+1+1).factorial:ℝ) := by
      apply div_nonneg
      · apply mul_nonneg (Real.exp_pos _).le
        convert sq_nonneg ((-u)^(n+1)) using 1 <;> ring
      · positivity
    linarith
  · have hp : Real.exp b * (-u)^(2*n+1) / ((2*n+1).factorial:ℝ) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        rw [pow_succ, pow_mul]
        exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (sq_nonneg _) _) (neg_nonpos.mpr hu)
      · positivity
    linarith

lemma normal_poly_integral (n : ℕ) (x : ℝ) :
    (∫ t in 0..x, normal_expPoly n (t^2/2)) = normal_intPoly n x := by
  have he (t : ℝ) (j : ℕ) : (-(t^2/2))^j / (j.factorial:ℝ) =
      ((-1/2:ℝ)^j / (j.factorial:ℝ)) * t^(2*j) := by
    rw [show -(t^2/2) = (-1/2:ℝ)*t^2 by ring, mul_pow, ← pow_mul]
    ring
  simp only [normal_expPoly, he]
  rw [intervalIntegral.integral_finsetSum (fun j _ => (by fun_prop :
    Continuous (fun t : ℝ => ((-1/2:ℝ)^j / (j.factorial:ℝ)) * t^(2*j))).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul, integral_pow, zero_pow (by omega : 2*_+1 ≠ 0), sub_zero]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma normal_integral_bracket (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    normal_intPoly (2*n+1) x ≤ (∫ t in 0..x, Real.exp (-(t^2/2))) ∧
    (∫ t in 0..x, Real.exp (-(t^2/2))) ≤ normal_intPoly (2*n) x := by
  have hp (k : ℕ) : Continuous (fun t : ℝ => normal_expPoly k (t^2/2)) := by
    unfold normal_expPoly
    fun_prop
  have hf : Continuous (fun t : ℝ => Real.exp (-(t^2/2))) := by fun_prop
  rw [← normal_poly_integral, ← normal_poly_integral]
  constructor
  · exact intervalIntegral.integral_mono_on hx ((hp _).intervalIntegrable _ _)
      (hf.intervalIntegrable _ _) (fun t _ => (normal_exp_bracket n (t^2/2) (by positivity)).1)
  · exact intervalIntegral.integral_mono_on hx (hf.intervalIntegrable _ _)
      ((hp _).intervalIntegrable _ _) (fun t _ => (normal_exp_bracket n (t^2/2) (by positivity)).2)

lemma normal_cdf_integral (x : ℝ) (hx : 0 ≤ x) :
    2*cdf (gaussianReal 0 1) (-x) =
      1 - 2*(1/Real.sqrt (2*Real.pi))*(∫ t in 0..x, Real.exp (-(t^2/2))) := by
  have hm : gaussianReal 0 1 (Ioc 0 x) =
      ENNReal.ofReal (cdf (gaussianReal 0 1) x - cdf (gaussianReal 0 1) 0) := by
    conv_lhs => rw [← measure_cdf (gaussianReal 0 1), StieltjesFunction.measure_Ioc]
  rw [gaussianReal_apply_eq_integral 0 (by norm_num : (1:NNReal) ≠ 0)] at hm
  have hn : 0 ≤ cdf (gaussianReal 0 1) x - cdf (gaussianReal 0 1) 0 :=
    sub_nonneg.mpr (monotone_cdf _ hx)
  have hint : 0 ≤ ∫ t in Ioc 0 x, gaussianPDFReal 0 1 t :=
    integral_nonneg (fun t => gaussianPDFReal_nonneg 0 1 t)
  have he := (ENNReal.ofReal_eq_ofReal_iff hint hn).mp hm
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero] at he
  rw [← intervalIntegral.integral_of_le hx, intervalIntegral.integral_const_mul] at he
  simp only [neg_div] at he
  rw [P053.NormalCompletion.normal_cdf_zero] at he
  rw [P053.NormalCompletion.normal_cdf_neg]
  simp only [one_div]
  nlinarith only [he]


lemma normal_density_bounds :
    (0.39894:ℝ) ≤ 1/Real.sqrt (2*Real.pi) ∧
    1/Real.sqrt (2*Real.pi) ≤ 0.39895 := by
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  constructor
  · apply (le_div_iff₀ hs).mpr
    nlinarith [Real.pi_lt_d4, sq_nonneg (0.39894*Real.sqrt (2*Real.pi)-1)]
  · apply (div_le_iff₀ hs).mpr
    nlinarith [Real.pi_gt_d4, sq_nonneg (0.39895*Real.sqrt (2*Real.pi)-1)]

lemma normal_tail_bound (n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hp : 0 ≤ normal_intPoly (2*n+1) x) :
    1 - 2*0.39895*normal_intPoly (2*n) x ≤ 2*cdf (gaussianReal 0 1) (-x) ∧
    2*cdf (gaussianReal 0 1) (-x) ≤ 1 - 2*0.39894*normal_intPoly (2*n+1) x := by
  obtain ⟨hl,hu⟩ := normal_integral_bracket n x hx
  obtain ⟨hc0,hc1⟩ := normal_density_bounds
  have hi : 0 ≤ ∫ t in 0..x, Real.exp (-(t^2/2)) :=
    intervalIntegral.integral_nonneg hx (fun t _ => (Real.exp_pos _).le)
  have hcoef : 0 ≤ 1/Real.sqrt (2*Real.pi) := by positivity
  rw [normal_cdf_integral x hx]
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hu hcoef
    have h2 := mul_le_mul_of_nonneg_right hc1 (le_trans hi hu)
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hl hcoef
    have h2 := mul_le_mul_of_nonneg_right hc0 hp
    nlinarith

lemma normal_tail_antitone {a b : ℝ} (h : a ≤ b) :
    2*cdf (gaussianReal 0 1) (-b) ≤ 2*cdf (gaussianReal 0 1) (-a) := by
  have := monotone_cdf (gaussianReal 0 1) (neg_le_neg h)
  linarith


set_option maxRecDepth 10000 in
lemma normal_small_endpoints :
    (0.415:ℝ) ≤ 2*cdf (gaussianReal 0 1) (-0.81) ∧
    2*cdf (gaussianReal 0 1) (-0.8) ≤ 0.425 ∧
    (0.8445:ℝ) ≤ 2*cdf (gaussianReal 0 1) (-0.19488) ∧
    2*cdf (gaussianReal 0 1) (-0.19487) ≤ 0.8455 := by
  have ha := normal_tail_bound 3 0.81 (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  have hb := normal_tail_bound 3 0.8 (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  have hc := normal_tail_bound 3 0.19488 (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  have hd := normal_tail_bound 3 0.19487 (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial] at ha hb hc hd
  exact ⟨by linarith [ha.1], by linarith [hb.2], by linarith [hc.1], by linarith [hd.2]⟩

lemma normal_between_stat :
    (0.19487:ℝ) ≤ betweenHazardWald 0.691 0.318 0.629 0.091 ∧
    betweenHazardWald 0.691 0.318 0.629 0.091 ≤ 0.19488 := by
  have hF := neg_log_certificate 0.691 (by norm_num) (by norm_num) 10
  have hA := neg_log_certificate 0.629 (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hF hA
  let Q : ℝ := ((0.318:ℝ)/0.691)^2 + ((0.091:ℝ)/0.629)^2
  have hpos : 0 < Real.sqrt Q := Real.sqrt_pos.mpr (by norm_num [Q])
  have hs : (0.482407:ℝ) ≤ Real.sqrt Q ∧ Real.sqrt Q ≤ 0.482408 := by
    constructor
    · apply Real.le_sqrt_of_sq_le
      norm_num [Q]
    · apply Real.sqrt_le_iff.mpr
      constructor <;> norm_num [Q]
  change 0.19487 ≤ (Real.log 0.691 - Real.log 0.629)/Real.sqrt Q ∧
    (Real.log 0.691 - Real.log 0.629)/Real.sqrt Q ≤ 0.19488
  constructor
  · apply (le_div_iff₀ hpos).mpr
    nlinarith only [hF.2, hA.1, hs.2]
  · apply (div_le_iff₀ hpos).mpr
    nlinarith only [hF.1, hA.2, hs.1]

 theorem corrected_normal_p_approximations_proof :
    |normalTwoSided (hazardWald 0.691 0.318) - 0.42| ≤ 0.005 ∧
    |normalTwoSided (betweenHazardWald 0.691 0.318 0.629 0.091) - 0.845| ≤ 0.0005 := by
  obtain ⟨hlo,hhi⟩ := wald_former_rounding 0.691 0.318
    (by norm_num [printedInterval]) (by norm_num [printedInterval])
  obtain ⟨ha,hb,hc,hd⟩ := normal_small_endpoints
  obtain ⟨hz0,hz1⟩ := normal_between_stat
  constructor
  · unfold normalTwoSided
    apply abs_le.mpr
    have h1 := normal_tail_antitone hhi.le
    have h2 := normal_tail_antitone hlo.le
    constructor <;> linarith
  · unfold normalTwoSided
    rw [abs_of_nonneg (by linarith : 0 ≤ betweenHazardWald 0.691 0.318 0.629 0.091)]
    apply abs_le.mpr
    have h1 := normal_tail_antitone hz1
    have h2 := normal_tail_antitone hz0
    constructor <;> linarith

/-! Balanced scrutiny and its specializations. -/
open OrderCompletion

lemma scrutiny_card {m : ℕ} {z : Finset (Fin (2*m))}
    (hz : z ∈ balancedSequences m) : z.card = m :=
  (Finset.mem_powersetCard.mp hz).2

lemma scrutiny_leading_bound {m : ℕ} {z : Finset (Fin (2*m))}
    (hz : z ∈ balancedSequences m) : leadingCited z ≤ m := by
  apply le_trans (b := z.card) _ (scrutiny_card hz).le
  apply Finset.card_le_card
  intro r hr
  exact (Finset.mem_filter.mp hr).2 r le_rfl

lemma scrutiny_tail_count (m r : ℕ) (hm : 1 ≤ m) (hr : r ≤ m) :
    ((balancedSequences m).filter (fun z => r ≤ leadingCited z)).card =
      (2*m-r).choose m := by
  classical
  have he : (balancedSequences m).filter (fun z => r ≤ leadingCited z) =
      (Finset.univ.powersetCard m).filter
        (fun z : Finset (Fin (2*m)) => initialSegment (2*m) r ⊆ z) := by
    ext z
    simp only [balancedSequences, Finset.mem_filter]
    apply and_congr_right
    intro hz
    exact leading_run_ge_iff z (balanced_proper hm z (Finset.mem_powersetCard.mp hz).2)
  rw [he, Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _)]
  · rw [initialSegment_card (by omega : r < 2*m), Finset.card_univ, Fintype.card_fin]
    rw [← Nat.choose_symm (by omega : m-r ≤ 2*m-r)]
    congr 1
    omega
  · rw [initialSegment_card (by omega : r < 2*m)]
    exact hr

lemma scrutiny_leading_sum (m : ℕ) (hm : 1 ≤ m) :
    (∑ z ∈ balancedSequences m, leadingCited z) = (2*m).choose (m+1) := by
  classical
  have tail (z : Finset (Fin (2*m))) (hz : z ∈ balancedSequences m) :
      leadingCited z = ∑ r ∈ Finset.range m, if r+1 ≤ leadingCited z then 1 else 0 := by
    have he : (Finset.range m).filter (fun r => r+1 ≤ leadingCited z) =
        Finset.range (leadingCited z) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range]
      have := scrutiny_leading_bound hz
      omega
    rw [← Finset.sum_filter, he]
    simp
  calc
    _ = ∑ z ∈ balancedSequences m, ∑ r ∈ Finset.range m,
        if r+1 ≤ leadingCited z then 1 else 0 := Finset.sum_congr rfl tail
    _ = ∑ r ∈ Finset.range m, ((balancedSequences m).filter
        (fun z => r+1 ≤ leadingCited z)).card := by
      rw [Finset.sum_comm]
      simp
    _ = ∑ r ∈ Finset.range m, (2*m-(r+1)).choose m := by
      apply Finset.sum_congr rfl
      intro r hr
      exact scrutiny_tail_count m (r+1) hm (by simpa using hr)
    _ = ∑ r ∈ Finset.range m, (r+m).choose m := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      have := Finset.mem_range.mp hr
      omega
    _ = (2*m).choose (m+1) := by
      have h := Nat.sum_range_add_choose (m-1) m
      have he : m-1+1 = m := by omega
      have he' : m-1+m+1 = 2*m := by omega
      simpa only [he, he'] using h

lemma scrutiny_leading_mean (m : ℕ) (hm : 1 ≤ m) :
    balancedExpectation m (fun z => (leadingCited z : ℝ)) = (m:ℝ)/(m+1) := by
  have hs : (∑ z ∈ balancedSequences m, (leadingCited z : ℝ)) =
      ((2*m).choose (m+1) : ℝ) := by exact_mod_cast scrutiny_leading_sum m hm
  have hc : ((balancedSequences m).card : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (balanced_sequence_card m).2
  have hi := Nat.choose_succ_right_eq (2*m) m
  have hi' : ((2*m).choose (m+1) : ℝ) * (m+1) = ((2*m).choose m : ℝ) * m := by
    have hn : 2*m-m = m := by omega
    rw [hn] at hi
    exact_mod_cast hi
  unfold balancedExpectation
  rw [hs]
  rw [(balanced_sequence_card m).1] at hc ⊢
  apply (div_eq_div_iff hc (by positivity : (m:ℝ)+1 ≠ 0)).mpr
  nlinarith [hi']

lemma scrutiny_removal_counts (m : ℕ) (hm : 1 ≤ m)
    (z : Finset (Fin (2*m))) (hz : z ∈ balancedSequences m) :
    (∑ r ∈ z, scrutinyOutcome z r) = (m:ℝ) - leadingCited z ∧
    (∑ r ∈ Finset.univ \ z, scrutinyOutcome z r) = (m:ℝ)-1 := by
  classical
  have hcard := scrutiny_card hz
  obtain ⟨q,hq,hmin,hK⟩ := first_missing_exists z (balanced_proper hm z hcard)
  have hK' : leadingCited z = q.val := hK
  have hY (r : Fin (2*m)) : scrutinyOutcome z r = if q < r then 1 else 0 := by
    unfold scrutinyOutcome
    congr 1
    apply propext
    constructor
    · rintro ⟨s,hs,hn⟩
      exact lt_of_le_of_lt (hmin s hn) hs
    · intro hr
      exact ⟨q,hr,hq⟩
  have hprefix : Finset.Iio q ⊆ z := by
    intro r hr
    by_contra hn
    exact (not_lt_of_ge (hmin r hn)) (Finset.mem_Iio.mp hr)
  have hC : z.filter (fun r => q < r) = z \ Finset.Iio q := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Iio]
    constructor
    · rintro ⟨hz,hr⟩; exact ⟨hz,not_lt_of_ge hr.le⟩
    · rintro ⟨hz,hr⟩
      exact ⟨hz,lt_of_le_of_ne (le_of_not_gt hr) (by intro he; exact hq (he ▸ hz))⟩
  have hU : (Finset.univ \ z).filter (fun r => q < r) = (Finset.univ \ z).erase q := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · rintro ⟨hr,ht⟩; exact ⟨ne_of_gt ht,hr⟩
    · rintro ⟨hr,hn⟩; exact ⟨hn,lt_of_le_of_ne (hmin r hn) (Ne.symm hr)⟩
  simp_rw [hY]
  rw [← Finset.sum_filter, ← Finset.sum_filter, hC, hU]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.card_sdiff_of_subset hprefix, Fin.card_Iio, hcard,
    Finset.card_erase_of_mem (by simp [hq]), Finset.card_sdiff_of_subset (Finset.subset_univ z),
    Finset.card_univ, Fintype.card_fin, hcard]
  have hb := scrutiny_leading_bound hz
  rw [← hK', Nat.cast_sub hb, Nat.cast_sub (by omega : 1 ≤ 2*m-m)]
  rw [show 2*m-m = m by omega]
  push_cast
  constructor <;> ring

lemma scrutiny_expect_affine (m : ℕ) (f : Finset (Fin (2*m)) → ℝ) (a b : ℝ) :
    balancedExpectation m (fun z => a + b * f z) = a + b * balancedExpectation m f := by
  have hc : ((balancedSequences m).card : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (balanced_sequence_card m).2
  simp only [balancedExpectation, Finset.sum_add_distrib, Finset.sum_const,
    ← Finset.mul_sum, nsmul_eq_mul]
  field_simp [hc]
  <;> ring

 theorem balanced_scrutiny_general_proof (m : ℕ) (hm : 1 ≤ m) :
    (∀ k ≤ m, leadingCitedProbability m k =
      (((2*m-k-1).choose (m-1) : ℝ) / ((2*m).choose m : ℝ))) ∧
    balancedExpectation m (fun z => (leadingCited z : ℝ)) = (m:ℝ)/(m+1) ∧
    (∀ z ∈ balancedSequences m,
      (∑ r ∈ z, scrutinyOutcome z r) = (m:ℝ) - leadingCited z ∧
      (∑ r ∈ Finset.univ \ z, scrutinyOutcome z r) = (m:ℝ)-1) ∧
    balancedExpectation m (fun z => (∑ r ∈ z, scrutinyOutcome z r) / m) =
      (m:ℝ)/(m+1) ∧
    balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z)) =
      1/((m:ℝ)*(m+1)) ∧
    0 < balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z)) := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hmean := scrutiny_leading_mean m hm
  have hrem := scrutiny_removal_counts m hm
  have hcongr (f g : Finset (Fin (2*m)) → ℝ)
      (h : ∀ z ∈ balancedSequences m, f z = g z) :
      balancedExpectation m f = balancedExpectation m g := by
    unfold balancedExpectation
    rw [Finset.sum_congr rfl h]
  have hcited : balancedExpectation m (fun z => (∑ r ∈ z, scrutinyOutcome z r) / m) =
      (m:ℝ)/(m+1) := by
    calc
      _ = balancedExpectation m (fun z => 1 + (-(m:ℝ)⁻¹) * (leadingCited z : ℝ)) := by
        apply hcongr
        intro z hz
        rw [(hrem z hz).1]
        field_simp
        <;> ring
      _ = _ := by rw [scrutiny_expect_affine, hmean]; field_simp [hm0] <;> ring
  have hcontrast : balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z)) =
      1/((m:ℝ)*(m+1)) := by
    calc
      _ = balancedExpectation m (fun z => (m:ℝ)⁻¹ + (-(m:ℝ)⁻¹) * (leadingCited z : ℝ)) := by
        apply hcongr
        intro z hz
        unfold citationContrast
        rw [(hrem z hz).1, (hrem z hz).2]
        field_simp
        <;> ring
      _ = _ := by rw [scrutiny_expect_affine, hmean]; field_simp [hm0] <;> ring
  refine ⟨fun k hk => leading_cited_probability_exact hm hk, hmean, hrem,
    hcited, hcontrast, ?_⟩
  rw [hcontrast]
  have : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  positivity

 theorem study_one_size_scrutiny_proof :
    balancedExpectation 50 (fun z => (leadingCited z : ℝ)) = 50/51 ∧
    balancedExpectation 50 (fun z => (∑ r ∈ z, scrutinyOutcome z r) / 50) = 50/51 ∧
    (∀ z ∈ balancedSequences 50,
      (∑ r ∈ Finset.univ \ z, scrutinyOutcome z r) / 50 = 49/50) ∧
    balancedExpectation 50 (fun z => citationContrast 50 z (scrutinyOutcome z)) = 1/2550 ∧
    balancedExpectation 50 (fun z => citationContrast 50 z (scrutinyOutcome z)) ≠ 0 := by
  obtain ⟨_,hk,hs,hc,hd,hpos⟩ := balanced_scrutiny_general_proof 50 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ne_of_gt hpos⟩
  · norm_num at hk ⊢; exact hk
  · norm_num at hc ⊢; exact hc
  · intro z hz
    rw [(hs z hz).2]
    norm_num
  · norm_num at hd ⊢; exact hd

 theorem adaptive_protocol_estimands_general_proof (m : ℕ) (hm : 1 ≤ m) :
    (∀ z z' : Finset (Fin (2*m)), ∀ r : Fin (2*m),
      (∀ s, s ≠ r → (s ∈ z ↔ s ∈ z')) → scrutinyOutcome z r - scrutinyOutcome z' r = 0) ∧
    balancedExpectation m (fun z => citationContrast m z (fun _ => 0)) = 0 ∧
    balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z)) = 1/((m:ℝ)*(m+1)) ∧
    0 < balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z)) := by
  obtain ⟨_,_,_,_,he,hp⟩ := balanced_scrutiny_general_proof m hm
  refine ⟨?_,slow_expectation_zero m,he,hp⟩
  intro z z' r h
  rw [scrutiny_no_direct_effect z z' r (fun s hs => h s (ne_of_lt hs))]
  ring

/-! Strongest attained significance tiers. -/
set_option maxRecDepth 10000 in
lemma normal_star_endpoints :
    2*cdf (gaussianReal 0 1) (-2.80) < (0.01:ℝ) ∧
    2*cdf (gaussianReal 0 1) (-2.01) < (0.05:ℝ) ∧
    (0.01:ℝ) < 2*cdf (gaussianReal 0 1) (-2.46) := by
  have ha := normal_tail_bound 8 2.80 (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  have hb := normal_tail_bound 8 2.01 (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  have hc := normal_tail_bound 8 2.46 (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial] at ha hb hc
  exact ⟨by linarith [ha.2], by linarith [hb.2], by linarith [hc.1]⟩

lemma normal_two_star (z : ℝ) (hl : 2.01 < |z|) (hu : |z| < 2.46) :
    0.01 < normalTwoSided z ∧ normalTwoSided z < 0.05 ∧ significanceTier z = 2 := by
  obtain ⟨_,hb,hc⟩ := normal_star_endpoints
  have h1 := normal_tail_antitone hl.le
  have h2 := normal_tail_antitone hu.le
  have hlo : 0.01 < normalTwoSided z := by unfold normalTwoSided; linarith
  have hhi : normalTwoSided z < 0.05 := by unfold normalTwoSided; linarith
  exact ⟨hlo,hhi,by simp [significanceTier, not_lt.mpr hlo.le, hhi]⟩

 theorem corrected_normal_star_tiers_proof :
    (∀ h s : ℝ, printedInterval 0.670 h → printedInterval 0.095 s →
      normalTwoSided (hazardWald h s) < 0.01 ∧ significanceTier (hazardWald h s) = 3) ∧
    (∀ h s : ℝ, printedInterval 0.480 h → printedInterval 0.174 s →
      0.01 < normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.05 ∧
      significanceTier (hazardWald h s) = 2) ∧
    (∀ h s : ℝ, printedInterval 0.274 h → printedInterval 0.162 s →
      0.01 < normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.05 ∧
      significanceTier (hazardWald h s) = 2) ∧
    (∀ h s : ℝ, printedInterval 0.316 h → printedInterval 0.149 s →
      0.01 < normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.05 ∧
      significanceTier (hazardWald h s) = 2) := by
  obtain ⟨hA,hB,hC,hD⟩ := corrected_star_wald_bounds
  refine ⟨?_,?_,?_,?_⟩
  · intro h s hh hs
    have he := normal_tail_antitone (hA h s hh hs).le
    have hp : normalTwoSided (hazardWald h s) < 0.01 := by
      unfold normalTwoSided
      linarith [normal_star_endpoints.1]
    exact ⟨hp,by simp [significanceTier,hp]⟩
  · intro h s hh hs
    obtain ⟨hl,hu⟩ := hB h s hh hs
    exact normal_two_star _ hl (by linarith)
  · intro h s hh hs
    obtain ⟨hl,hu⟩ := hC h s hh hs
    exact normal_two_star _ (by linarith) (by linarith)
  · intro h s hh hs
    obtain ⟨hl,hu⟩ := hD h s hh hs
    exact normal_two_star _ (by linarith) hu

end AronowAudit.P041.Wave1
