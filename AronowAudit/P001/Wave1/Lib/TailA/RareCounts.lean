import AronowAudit.P001.Wave1.Lib.TailA.FiniteBootstrap
import AronowAudit.Literature.CondP001g14
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Finite rare-category counts and the law of small numbers. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

namespace AronowAudit.P001.TailA

local instance instDecidableRareCounts (p : Prop) : Decidable p := Classical.propDecidable p

/-- Counts of the first `k` categories; `Fin.last k` is the residual category. -/
def rareCounts {k N : ℕ} (a : Fin N → Fin (k + 1)) : Fin k → ℕ :=
  fun i => (Finset.univ.filter (fun j => a j = i.castSucc)).card

theorem rare_counts_full_fiber {k N : ℕ} (v : Fin k → ℕ)
    (hv : ∑ i, v i ≤ N) :
    (rareCounts (N := N)) ⁻¹' {v} = StatLean.ComputationalStatistics.categoricalCounts ⁻¹'
      {Fin.snoc v (N - ∑ i, v i)} := by
  ext a
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro ha
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · have hsum := StatLean.ComputationalStatistics.sum_categoricalCounts a
      rw [Fin.sum_univ_castSucc] at hsum
      have hfirst : ∀ i, StatLean.ComputationalStatistics.categoricalCounts a i.castSucc = v i :=
        fun i => congrFun ha i
      simp only [hfirst] at hsum
      simp only [Fin.snoc_last]
      omega
    · simpa only [Fin.snoc_castSucc, rareCounts, StatLean.ComputationalStatistics.categoricalCounts] using congrFun ha i
  · intro ha
    funext i
    simpa only [rareCounts, StatLean.ComputationalStatistics.categoricalCounts,
      Fin.snoc_castSucc] using congrFun ha i.castSucc

/-- The multinomial coefficient after eliminating the residual count. -/
theorem rare_counts_multinomial_coefficient {k N : ℕ} (v : Fin k → ℕ)
    (hv : ∑ i, v i ≤ N) :
    (Nat.multinomial Finset.univ (Fin.snoc v (N - ∑ i, v i)) : ℝ) =
      (N.descFactorial (∑ i, v i) : ℝ) / ∏ i, (v i).factorial := by
  have hsum : ∑ j, Fin.snoc v (N - ∑ i, v i) j = N := by
    simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    omega
  have hprod : ∏ j : Fin (k + 1), Nat.factorial ((Fin.snoc v (N - ∑ i, v i) : Fin (k + 1) → ℕ) j) =
      (∏ i, (v i).factorial) * (N - ∑ i, v i).factorial := by
    simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  have hs := Nat.multinomial_spec Finset.univ (Fin.snoc v (N - ∑ i, v i))
  rw [hsum, hprod] at hs
  have hc : (∏ i, (v i).factorial) *
      Nat.multinomial Finset.univ (Fin.snoc v (N - ∑ i, v i)) =
      N.descFactorial (∑ i, v i) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos (N - ∑ i, v i))
    calc
      _ = N.factorial := by simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hs
      _ = _ := (Nat.factorial_mul_descFactorial hv).symm
  have hnonzero : (∏ i, ((v i).factorial : ℝ)) ≠ 0 := by positivity
  simp only [Nat.cast_prod]
  apply (eq_div_iff hnonzero).mpr
  exact_mod_cast (by simpa [Nat.mul_comm] using hc)

/-- Exact finite singleton probability, obtained from the multinomial fiber law. -/
theorem rare_counts_singleton {k N : ℕ} (q : Fin (k + 1) → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (v : Fin k → ℕ) (hv : ∑ i, v i ≤ N) :
    ((Measure.pi fun _ : Fin N => StatLean.ComputationalStatistics.categorical q).map
      rareCounts) {v} =
      ENNReal.ofReal (((N.descFactorial (∑ i, v i) : ℝ) *
        ∏ i, q i.castSucc ^ v i) / (∏ i, (v i).factorial) *
        q (Fin.last k) ^ (N - ∑ i, v i)) := by
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton v),
    rare_counts_full_fiber v hv,
    ← Measure.map_apply StatLean.ComputationalStatistics.measurable_categoricalCounts
      (measurableSet_singleton _),
    StatLean.ComputationalStatistics.map_categoricalCounts_pi hq0 hq1,
    StatLean.Bayesian.multinomialKernel_apply_singleton,
    StatLean.Bayesian.multinomialWeight]
  have hsum : ∑ j, Fin.snoc v (N - ∑ i, v i) j = N := by
    simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    omega
  rw [if_pos ⟨hq0, hq1, hsum⟩, rare_counts_multinomial_coefficient v hv,
    Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  congr 1
  ring

/-- A varying sample size version of the elementary rare-probability limit. -/
theorem rare_counts_probability_zero (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (p : ℕ → ℝ) (r : ℝ)
    (hr : Tendsto (fun n => (m n : ℝ) * p n) atTop (𝓝 r)) :
    Tendsto p atTop (𝓝 0) := by
  have h := hr.mul (tendsto_one_div_atTop_nhds_zero_nat.comp hm)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [hm.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (m n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < m n))
  dsimp
  field_simp

/-- The residual-category probability raised to the number of remaining trials. -/
theorem rare_counts_residual_power (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (p : ℕ → ℝ) (r : ℝ)
    (hr : Tendsto (fun n => (m n : ℝ) * p n) atTop (𝓝 r)) (s : ℕ) :
    Tendsto (fun n => (1 - p n) ^ (m n - s)) atTop (𝓝 (Real.exp (-r))) := by
  have hp := rare_counts_probability_zero m hm p r hr
  have hd : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1) 0 := by
    convert (((hasDerivAt_const (0 : ℝ) 1).sub (hasDerivAt_id 0)).log (by norm_num)) using 1 <;>
      norm_num
  let L : ℝ → ℝ := Function.update (fun x => Real.log (1 - x) / x) 0 (-1)
  have hL : Tendsto (fun n => L (p n)) atTop (𝓝 (-1)) := by
    simpa [L, Function.comp_def] using
      hd.continuousAt_div.tendsto.comp hp
  have hlog : Tendsto (fun n => (m n : ℝ) * Real.log (1 - p n)) atTop (𝓝 (-r)) := by
    convert (hr.mul hL).congr' (Eventually.of_forall fun n => ?_) using 1
    · ring
    · by_cases hpn : p n = 0
      · simp [hpn, L]
      · simp only [L, Function.update_of_ne hpn]
        field_simp
  have hpow : Tendsto (fun n => (1 - p n) ^ m n) atTop (𝓝 (Real.exp (-r))) := by
    apply (Real.continuous_exp.tendsto (-r) |>.comp hlog).congr'
    filter_upwards [hp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
    simp only [Function.comp_apply, Real.exp_nat_mul, Real.exp_log (sub_pos.mpr hn)]
  have hsmall : Tendsto (fun n => (1 - p n) ^ s) atTop (𝓝 (1 : ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hp).pow s
  have hfinal := hpow.mul (hsmall.inv₀ one_ne_zero)
  simp only [inv_one, mul_one] at hfinal
  apply hfinal.congr'
  filter_upwards [hm.eventually (eventually_ge_atTop s),
    hp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hpn
  exact (pow_sub₀ (1 - p n) (ne_of_gt (sub_pos.mpr hpn)) hn).symm

/-- Falling-factorial times rare probabilities, including zero limiting rates. -/
theorem rare_counts_factorial_limit (k : ℕ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (q : ℕ → Fin k → ℝ) (r : Fin k → ℝ)
    (hr : ∀ i, Tendsto (fun n => (m n : ℝ) * q n i) atTop (𝓝 (r i)))
    (v : Fin k → ℕ) :
    Tendsto (fun n => ((m n).descFactorial (∑ i, v i) : ℝ) * ∏ i, q n i ^ v i)
      atTop (𝓝 (∏ i, r i ^ v i)) := by
  have he := (isEquivalent_descFactorial (∑ i, v i)).comp_tendsto hm
  have he' := he.mul (Asymptotics.IsEquivalent.refl
    (u := fun n => ∏ i, q n i ^ v i))
  apply he'.tendsto_nhds_iff.mpr
  have hprod := tendsto_finsetProd Finset.univ (fun i _ => (hr i).pow (v i))
  convert hprod using 1
  funext n
  simp only [Function.comp_apply, Pi.mul_apply, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]

/-- Scheffé's argument on a countable carrier: point masses plus total mass
give convergence in the sum of absolute differences. -/
theorem rare_counts_scheffe {E : Type*} (p : ℕ → E → ℝ) (g : E → ℝ)
    (hp0 : ∀ n x, 0 ≤ p n x) (hg0 : ∀ x, 0 ≤ g x)
    (hp1 : ∀ n, HasSum (p n) 1) (hg1 : HasSum g 1)
    (hlim : ∀ x, Tendsto (fun n => p n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∑' x, |p n x - g x|) atTop (𝓝 0) := by
  have hminsum (n : ℕ) : Summable (fun x => min (p n x) (g x)) :=
    hg1.summable.of_nonneg_of_le (fun x => le_min (hp0 n x) (hg0 x))
      (fun x => min_le_right _ _)
  have hmin : Tendsto (fun n => ∑' x, min (p n x) (g x)) atTop (𝓝 1) := by
    rw [← hg1.tsum_eq]
    apply tendsto_tsum_of_dominated_convergence hg1.summable
    · intro x
      simpa using (hlim x).min (tendsto_const_nhds (x := g x))
    · exact Eventually.of_forall fun n x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp0 n x) (hg0 x))]
        exact min_le_right _ _
  have heq (n : ℕ) : (∑' x, |p n x - g x|) = 2 - 2 * ∑' x, min (p n x) (g x) := by
    have hpoint (x : E) : |p n x - g x| = p n x + g x - 2 * min (p n x) (g x) := by
      rcases le_total (p n x) (g x) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
        ring
    simp_rw [hpoint]
    rw [((hp1 n).summable.add hg1.summable).tsum_sub ((hminsum n).mul_left 2),
      (hp1 n).summable.tsum_add hg1.summable, (hminsum n).tsum_mul_left,
      (hp1 n).tsum_eq, hg1.tsum_eq]
    ring
  simpa only [heq, show (2 : ℝ) - 2 * 1 = 0 by norm_num] using
    (tendsto_const_nhds (x := (2 : ℝ))).sub (hmin.const_mul 2)

/-- Singleton masses of a countable probability measure sum to one in `ℝ`. -/
theorem rare_counts_hasSum_singletons {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [Countable E] (μ : Measure E) [IsProbabilityMeasure μ] :
    HasSum (fun x => (μ {x}).toReal) 1 := by
  have hsum : (∑' x, μ {x}) = 1 := by
    simpa using μ.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
  have hs := ENNReal.hasSum_toReal (f := fun x => μ {x}) (by rw [hsum]; exact ENNReal.one_ne_top)
  convert hs using 1
  rw [← ENNReal.tsum_toReal_eq (fun x => measure_ne_top μ {x}), hsum,
    ENNReal.toReal_one]

/-- Countable singleton convergence implies convergence of every bounded test.
Continuity of the test is unnecessary on this discrete carrier. -/
theorem rare_counts_bounded_tests {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [Countable E]
    (μ : ℕ → Measure E) (ν : Measure E)
    (hμ : ∀ n, IsProbabilityMeasure (μ n)) [IsProbabilityMeasure ν]
    (hlim : ∀ x, Tendsto (fun n => ((μ n) {x}).toReal) atTop (𝓝 ((ν {x}).toReal)))
    (f : E → ℝ) (hf : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  haveI instProbabilityRareCountRows (n : ℕ) : IsProbabilityMeasure (μ n) := hμ n
  obtain ⟨C, hC⟩ := hf
  let D := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  have hbound (x : E) : |f x| ≤ D := (hC x).trans (le_max_left _ _)
  have hfi (ρ : Measure E) [IsProbabilityMeasure ρ] : Integrable f ρ :=
    Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable D
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  have hsumf (ρ : Measure E) [IsProbabilityMeasure ρ] :
      Summable (fun x => (ρ {x}).toReal * f x) := by
    apply ((rare_counts_hasSum_singletons ρ).summable.mul_right D).of_norm_bounded
    intro x
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbound x) ENNReal.toReal_nonneg
  have hL := rare_counts_scheffe (fun n x => ((μ n) {x}).toReal)
    (fun x => (ν {x}).toReal) (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ => ENNReal.toReal_nonneg) (fun n => rare_counts_hasSum_singletons (μ n))
    (rare_counts_hasSum_singletons ν) hlim
  rw [← tendsto_sub_nhds_zero_iff]
  have hLD : Tendsto (fun n => D * ∑' x, |((μ n) {x}).toReal - (ν {x}).toReal|)
      atTop (𝓝 0) := by simpa only [mul_zero] using hL.const_mul D
  apply squeeze_zero_norm (fun n => ?_) hLD
  rw [integral_countable (hfi (μ n)), integral_countable (hfi ν)]
  simp only [measureReal_def, smul_eq_mul]
  rw [← (hsumf (μ n)).tsum_sub (hsumf ν)]
  have habs : Summable (fun x => |((μ n) {x}).toReal - (ν {x}).toReal|) :=
    ((rare_counts_hasSum_singletons (μ n)).summable.sub
      (rare_counts_hasSum_singletons ν).summable).abs
  apply (norm_tsum_le_tsum_norm (((hsumf (μ n)).sub (hsumf ν)).norm)).trans
  rw [← habs.tsum_mul_left]
  apply Summable.tsum_le_tsum _ ((hsumf (μ n)).sub (hsumf ν)).norm (habs.mul_left D)
  intro x
  rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg _)).trans_eq (mul_comm _ _)

/-- Point masses of the finite rare-count law converge to the independent
Poisson point masses. This is the finite-probability part of the limit proof. -/
theorem rare_counts_singleton_limit
    (k : ℕ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (q : ℕ → Fin (k + 1) → ℝ) (hq0 : ∀ n i, 0 ≤ q n i)
    (hq1 : ∀ n, ∑ i, q n i = 1) («λ» : Fin k → ℝ≥0)
    (hRate : ∀ i, Tendsto (fun n => (m n : ℝ) * q n i.castSucc) atTop (𝓝 («λ» i : ℝ)))
    (v : Fin k → ℕ) :
    Tendsto (fun n => ((Measure.pi fun _ : Fin (m n) =>
      StatLean.ComputationalStatistics.categorical (q n)).map rareCounts) {v})
      atTop (𝓝 ((Measure.pi fun i => poissonMeasure («λ» i)) {v})) := by
  have hsum : Tendsto (fun n => (m n : ℝ) * ∑ i : Fin k, q n i.castSucc)
      atTop (𝓝 (∑ i, («λ» i : ℝ))) := by
    simpa only [Finset.mul_sum] using tendsto_finsetSum Finset.univ (fun i _ => hRate i)
  have hres (n : ℕ) : q n (Fin.last k) = 1 - ∑ i : Fin k, q n i.castSucc := by
    have h := hq1 n
    rw [Fin.sum_univ_castSucc] at h
    linarith
  have hfac := rare_counts_factorial_limit k m hm (fun n i => q n i.castSucc)
    (fun i => («λ» i : ℝ)) hRate v
  have hp := rare_counts_residual_power m hm (fun n => ∑ i : Fin k, q n i.castSucc)
    (∑ i, («λ» i : ℝ)) hsum (∑ i, v i)
  have ht := (hfac.div_const (∏ i, ((v i).factorial : ℝ))).mul hp
  have hpoint : ((Measure.pi fun i => poissonMeasure («λ» i)) {v}) =
      ENNReal.ofReal ((∏ i, («λ» i : ℝ) ^ v i) / (∏ i, ((v i).factorial : ℝ)) *
        Real.exp (-(∑ i, («λ» i : ℝ)))) := by
    rw [Measure.pi_singleton]
    simp only [poissonMeasure_singleton]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    congr 1
    simp only [Finset.prod_div_distrib, Finset.prod_mul_distrib,
      ← Real.exp_sum, ← Finset.sum_neg_distrib]
    ring
  rw [hpoint]
  apply (ENNReal.tendsto_ofReal ht).congr'
  filter_upwards [hm.eventually (eventually_ge_atTop (∑ i, v i))] with n hn
  rw [rare_counts_singleton (q n) (hq0 n) (hq1 n) v hn, hres]
  simp only [Nat.cast_prod]


/-- A measurable statistic on changing sample spaces is determined for weak
convergence by its countable singleton laws and their total mass. -/
theorem rare_counts_rowWeak_of_singletons
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [Countable E] [TopologicalSpace E]
    (P : (n : ℕ) → Measure (Ω n)) (Z : (n : ℕ) → Ω n → E)
    (hP : ∀ n, IsProbabilityMeasure (P n)) (hZ : ∀ n, Measurable (Z n))
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hlim : ∀ x, Tendsto (fun n => ((P n).map (Z n)) {x}) atTop (𝓝 (ν {x}))) :
    AronowAudit.Literature.RowWeak P Z ν := by
  haveI instProbabilityRareSource (n : ℕ) : IsProbabilityMeasure (P n) := hP n
  intro f _ hf
  have hmap (n : ℕ) : IsProbabilityMeasure ((P n).map (Z n)) :=
    inferInstance
  have htest := rare_counts_bounded_tests (fun n => (P n).map (Z n)) ν hmap
    (fun x => (ENNReal.tendsto_toReal (measure_ne_top ν {x})).comp (hlim x)) f hf
  convert htest using 1
  funext n
  exact (integral_map (hZ n).aemeasurable (measurable_of_countable f).aestronglyMeasurable).symm

theorem rare_counts_categorical_singleton {d : ℕ} (q : Fin d → ℝ) (i : Fin d) :
    StatLean.ComputationalStatistics.categorical q {i} = ENNReal.ofReal (q i) := by
  simp [StatLean.ComputationalStatistics.categorical, Pi.single_apply, mul_ite]


/-- The categorical probabilities of `k` distinct original labels. -/
def rareLabelProbabilities (k N : ℕ) : Fin (k + 1) → ℝ :=
  Fin.snoc (fun _ => (N : ℝ)⁻¹) (1 - (k : ℝ) / (N : ℝ))

theorem rare_label_probabilities_nonneg {k N : ℕ} (hk : k ≤ N) :
    ∀ i, 0 ≤ rareLabelProbabilities k N i := by
  apply Fin.lastCases
  · simp only [rareLabelProbabilities, Fin.snoc_last]
    by_cases hN : N = 0
    · simp [hN]
    · exact sub_nonneg.mpr ((div_le_one (by positivity : (0 : ℝ) < N)).mpr
        (by exact_mod_cast hk))
  · intro i
    simp only [rareLabelProbabilities, Fin.snoc_castSucc]
    positivity

theorem rare_label_probabilities_sum (k N : ℕ) :
    ∑ i, rareLabelProbabilities k N i = 1 := by
  simp only [rareLabelProbabilities, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring


/-- First-order probability mass in a shrinking interval from its density.
The interval endpoints may lie on either side of the fixed score. -/
theorem rare_counts_scaled_interval_integral
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (f : ℝ → ℝ) (hf : Continuous f) (p a b : ℝ) :
    Tendsto (fun n => (m n : ℝ) *
      ∫ x in (p + a / (m n : ℝ))..(p + b / (m n : ℝ)), f x)
      atTop (𝓝 ((b - a) * f p)) := by
  have hd : HasDerivAt (fun t => ∫ x in p..t, f x) (f p) p :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  let D := Function.update (fun t => (∫ x in p..t, f x) / (t - p)) p (f p)
  have hD : ContinuousAt D p := by
    simpa only [intervalIntegral.integral_same, sub_zero, D] using hd.continuousAt_div
  have hhalf (c : ℝ) : Tendsto (fun n => (m n : ℝ) *
      ∫ x in p..(p + c / (m n : ℝ)), f x) atTop (𝓝 (c * f p)) := by
    have hinv : Tendsto (fun n => (m n : ℝ)⁻¹) atTop (𝓝 0) := by
      have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hm
      change Tendsto (fun n => 1 / (m n : ℝ)) atTop (𝓝 0) at h
      simpa only [one_div] using h
    have harg : Tendsto (fun n => p + c / (m n : ℝ)) atTop (𝓝 p) := by
      simpa only [div_eq_mul_inv, mul_zero, add_zero] using
        (tendsto_const_nhds (x := p)).add (hinv.const_mul c)
    have h := (hD.tendsto.comp harg).const_mul c
    simp only [D, Function.update_self] at h
    apply h.congr'
    filter_upwards [hm.eventually (eventually_ge_atTop 1)] with n hn
    have hn0 : (m n : ℝ) ≠ 0 := by positivity
    by_cases hc : c = 0
    · simp [hc]
    · have harg0 : p + c / (m n : ℝ) ≠ p := by
        intro hzero
        have : c / (m n : ℝ) = 0 := by linarith
        exact hc ((div_eq_zero_iff).mp this |>.resolve_right hn0)
      simp only [Function.comp_apply]
      rw [Function.update_of_ne harg0]
      rw [show p + c / (m n : ℝ) - p = c / (m n : ℝ) by ring]
      generalize (∫ x in p..(p + c / (m n : ℝ)), f x) = I
      field_simp [hn0, hc] <;> ring
  convert (hhalf b).sub (hhalf a) using 1
  · funext n
    rw [← mul_sub, intervalIntegral.integral_interval_sub_left
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  · ring

/-- The corresponding statement for actual interval probabilities when the
interval masses are represented by a continuous density. -/
theorem rare_counts_scaled_interval_probability
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (μ : Measure ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (hdensity : ∀ u v : ℝ, u ≤ v →
      (μ (Set.Ioc u v)).toReal = ∫ x in u..v, f x)
    (p a b : ℝ) (hab : a ≤ b) :
    Tendsto (fun n => (m n : ℝ) *
      (μ (Set.Ioc (p + a / (m n : ℝ)) (p + b / (m n : ℝ)))).toReal)
      atTop (𝓝 ((b - a) * f p)) := by
  apply (rare_counts_scaled_interval_integral m hm f hf p a b).congr'
  filter_upwards [hm.eventually (eventually_ge_atTop 1)] with n hn
  rw [hdensity _ _ (add_le_add (le_refl p) (div_le_div_of_nonneg_right hab (by positivity)))]

/-- A finite measurable partition of a window, with the complement retained
as the residual category. -/
def rareEventCategory {E : Type*} {k : ℕ} (A : Fin k → Set E) (x : E) : Fin (k + 1) :=
  if h : ∃ i, x ∈ A i then (Classical.choose h).castSucc else Fin.last k

theorem rare_event_category_fiber {E : Type*} {k : ℕ} (A : Fin k → Set E)
    (hdis : ∀ i j, i ≠ j → Disjoint (A i) (A j)) (i : Fin k) :
    rareEventCategory A ⁻¹' {i.castSucc} = A i := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, rareEventCategory]
  split_ifs with h
  · rw [Fin.castSucc_inj]
    constructor
    · intro hi
      simpa only [hi] using Classical.choose_spec h
    · intro hx
      by_contra hi
      exact Set.disjoint_left.mp (hdis _ _ hi) (Classical.choose_spec h) hx
  · constructor
    · intro hf
      exact False.elim (Fin.castSucc_ne_last i hf.symm)
    · intro hx
      exact False.elim (h ⟨i, hx⟩)

theorem rare_event_category_residual {E : Type*} {k : ℕ} (A : Fin k → Set E) :
    rareEventCategory A ⁻¹' {Fin.last k} = (⋃ i, A i)ᶜ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff,
    Set.mem_iUnion, rareEventCategory]
  split_ifs with h
  · exact iff_of_false (Fin.castSucc_ne_last _) (not_not_intro h)
  · simp only [not_false_eq_true, h]

theorem measurable_rare_event_category {E : Type*} [MeasurableSpace E] {k : ℕ}
    (A : Fin k → Set E) (hA : ∀ i, MeasurableSet (A i))
    (hdis : ∀ i j, i ≠ j → Disjoint (A i) (A j)) :
    Measurable (rareEventCategory A) := by
  apply measurable_to_countable'
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [rare_event_category_residual]
    exact (MeasurableSet.iUnion hA).compl
  · rw [rare_event_category_fiber A hdis i]
    exact hA i

/-- Counts in finitely many disjoint measurable window categories. This
interface accommodates score intervals crossed with donor/recipient types. -/
theorem rare_partition_counts {E : Type*} [MeasurableSpace E]
    (k : ℕ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (P : ℕ → Measure E) (hP : ∀ n, IsProbabilityMeasure (P n))
    (A : ℕ → Fin k → Set E) (hA : ∀ n i, MeasurableSet (A n i))
    (hdis : ∀ n i j, i ≠ j → Disjoint (A n i) (A n j))
    («λ» : Fin k → ℝ≥0)
    (hRate : ∀ i, Tendsto (fun n => (m n : ℝ) * ((P n) (A n i)).toReal)
      atTop (𝓝 («λ» i : ℝ))) :
    AronowAudit.Literature.RowWeak
      (fun n => Measure.pi (fun _ : Fin (m n) => P n))
      (fun n a i => (Finset.univ.filter (fun j => a j ∈ A n i)).card)
      (Measure.pi (fun i => poissonMeasure («λ» i))) := by
  haveI instProbabilityRarePartition (n : ℕ) : IsProbabilityMeasure (P n) := hP n
  let c := fun n => rareEventCategory (A n)
  have hc (n : ℕ) : Measurable (c n) := measurable_rare_event_category (A n) (hA n) (hdis n)
  let Q := fun n => (P n).map (c n)
  haveI instProbabilityRarePartitionImage (n : ℕ) : IsProbabilityMeasure (Q n) :=
    inferInstance
  let q := fun n i => ((Q n) {i}).toReal
  have hq1 (n : ℕ) : ∑ i, q n i = 1 := by
    simpa only [tsum_fintype] using (rare_counts_hasSum_singletons (Q n)).tsum_eq
  have hcat (n : ℕ) : Q n = StatLean.ComputationalStatistics.categorical (q n) := by
    apply Measure.ext_of_singleton
    intro i
    rw [rare_counts_categorical_singleton]
    exact (ENNReal.ofReal_toReal (measure_ne_top (Q n) {i})).symm
  have hfirst (n : ℕ) (i : Fin k) : q n i.castSucc = ((P n) (A n i)).toReal := by
    dsimp [q, Q]
    rw [Measure.map_apply (hc n) (measurableSet_singleton _),
      rare_event_category_fiber (A n) (hdis n) i]
  have hcounts (n : ℕ) :
      (fun (a : Fin (m n) → E) i => (Finset.univ.filter (fun j => a j ∈ A n i)).card) =
      rareCounts ∘ (fun (a : Fin (m n) → E) j => c n (a j)) := by
    funext a i
    simp only [Function.comp_apply, rareCounts]
    congr 1
    ext j
    have h := Set.ext_iff.mp (rare_event_category_fiber (A n) (hdis n) i) (a j)
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_preimage, Set.mem_singleton_iff, c] using h.symm
  have hZ (n : ℕ) : Measurable
      (fun (a : Fin (m n) → E) i => (Finset.univ.filter (fun j => a j ∈ A n i)).card) := by
    rw [hcounts]
    exact Measurable.of_discrete.comp (Measurable.of_eval fun j =>
      (hc n).comp (measurable_pi_apply j))
  apply rare_counts_rowWeak_of_singletons _ _ (fun _ => inferInstance) hZ
  intro v
  have hl := rare_counts_singleton_limit k m hm q (fun _ _ => ENNReal.toReal_nonneg)
    hq1 «λ» (fun i => by simpa only [hfirst] using hRate i) v
  convert hl using 1
  funext n
  have ht : Measurable (fun (a : Fin (m n) → E) j => c n (a j)) :=
    Measurable.of_eval fun j => (hc n).comp (measurable_pi_apply j)
  rw [hcounts, ← Measure.map_map (g := rareCounts) Measurable.of_discrete ht,
    Measure.pi_map_pi (fun _ => (hc n).aemeasurable)]
  simp only [← hcat]
  rfl

/-- Finite-window interval-category approximation: the counts in disjoint
intervals with endpoints `p + a i / m n` and `p + b i / m n` converge to the
product Poisson law with rates `(b i - a i) * f p`. -/
theorem finite_window_interval_category_counts
    (k : ℕ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (f : ℝ → ℝ) (hf : Continuous f)
    (hdensity : ∀ u v : ℝ, u ≤ v →
      (P (Set.Ioc u v)).toReal = ∫ x in u..v, f x)
    (p : ℝ) (a b : Fin k → ℝ) (hab : ∀ i, a i ≤ b i)
    (hdis : ∀ n i j, i ≠ j → Disjoint
      (Set.Ioc (p + a i / (m n : ℝ)) (p + b i / (m n : ℝ)))
      (Set.Ioc (p + a j / (m n : ℝ)) (p + b j / (m n : ℝ))))
    (rates : Fin k → ℝ≥0) (hrates : ∀ i, (rates i : ℝ) = (b i - a i) * f p) :
    AronowAudit.Literature.RowWeak
      (fun n => Measure.pi (fun _ : Fin (m n) => P))
      (fun n x i => (Finset.univ.filter (fun j =>
        x j ∈ Set.Ioc (p + a i / (m n : ℝ)) (p + b i / (m n : ℝ)))).card)
      (Measure.pi (fun i => poissonMeasure (rates i))) := by
  have hlim := rare_partition_counts k m hm (fun _ => P) (fun _ => inferInstance)
    (fun n i => Set.Ioc (p + a i / (m n : ℝ)) (p + b i / (m n : ℝ)))
    (fun _ _ => measurableSet_Ioc) hdis rates (fun i => by
      rw [hrates i]
      exact rare_counts_scaled_interval_probability m hm P f hf hdensity p (a i) (b i) (hab i))
  convert hlim using 1
  funext n x i
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- A density representation is needed only near the pinned score, allowing
support boundaries elsewhere and a continuous extension of the local density. -/
theorem rare_counts_scaled_interval_probability_local
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (μ : Measure ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (p δ : ℝ) (hδ : 0 < δ)
    (hdensity : ∀ u v : ℝ, u ∈ Metric.ball p δ → v ∈ Metric.ball p δ → u ≤ v →
      (μ (Set.Ioc u v)).toReal = ∫ x in u..v, f x)
    (a b : ℝ) (hab : a ≤ b) :
    Tendsto (fun n => (m n : ℝ) *
      (μ (Set.Ioc (p + a / (m n : ℝ)) (p + b / (m n : ℝ)))).toReal)
      atTop (𝓝 ((b - a) * f p)) := by
  have hloc (c : ℝ) : Tendsto (fun n => p + c / (m n : ℝ)) atTop (𝓝 p) := by
    have hi := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hm
    change Tendsto (fun n => 1 / (m n : ℝ)) atTop (𝓝 0) at hi
    have hi' : Tendsto (fun n => c / (m n : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_one_div, mul_zero] using hi.const_mul c
    simpa only [add_zero] using (tendsto_const_nhds (x := p)).add hi'
  apply (rare_counts_scaled_interval_integral m hm f hf p a b).congr'
  filter_upwards [(hloc a).eventually (Metric.ball_mem_nhds p hδ),
    (hloc b).eventually (Metric.ball_mem_nhds p hδ),
    hm.eventually (eventually_ge_atTop 1)] with n ha hb hn
  rw [hdensity _ _ ha hb
    (add_le_add (le_refl p) (div_le_div_of_nonneg_right hab (by positivity)))]


end AronowAudit.P001.TailA
