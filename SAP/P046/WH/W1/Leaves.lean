import SAP.P046.WH.W1.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

namespace SAP.P046.WH.W1

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

/-- Export the count-statistic reductions on the design support. Copy the finite-sum
argument in PropositionThree.n5_proof before its cutoff step: split at W=3/5,
sum the low-treated indicators, and use the already proved population mean. -/
def T1_L1 : Prop := WholeT1Reductions

/-- Identify the strict failure probability with the logarithm-indexed sum. Given the
reductions and joint law, the feasible (K,S) fibres are a measurable finite disjoint
partition. Sum their masses; use count_exclusion to identify exactly the selected fibres.
The existing certified numerator need not be recomputed. -/
def T1_L2 : Prop := WholeT1Reductions → WholeT1CountLaw →
  strictNoncoverage IntervalExample.study 100 (1 / 10000000) =
    ∑ k ∈ range 101, ∑ s ∈ range (k + 1),
      if Real.log 20000000 < wholeCountThreshold k s then wholeCountMass k s else 0

/-- Lift the conditional factorization to each scaled sample summand and record the
iterated means. Use conditional_xy_factorization, htcentre_coordinate, condExp_smul,
coordinate measure preservation, ht_conditional_centre_proof and integral_condExp.
All variables are bounded by positivity; supply their integrability before pull-out. -/
def T3_L1 : Prop := WholeT3Centres

/-- Conditional independence of the heterogeneous summands given all covariates, their
ranges, positive denominator identity and strict positivity bound. Use the binary
conditional product table p3_product_conditional/p3_single_conditional and
iCondIndepFun_iff_condExp_inter_preimage_eq_mul. The factors depending on W pull out.
Lift positivity coordinatewise, then use sqrt_mean_inverse_sq_lt for the strict bound. -/
def T3_L2 : Prop := WholeT3Structure

/-- Conditional and unconditional concentration at the random, covariate-measurable
threshold. Adapt conditional_hoeffding_binary_expansion, replacing its constant threshold
by sqrt(xi)*c. Its coefficients remain measurable for the covariate sigma algebra.
Use p3_bernoulli_tail pointwise, then integrate. p3_random_tail already proves the
unconditional inequality. Do not substitute a random value into fixed-t AE statements. -/
def T3_L3 : Prop := WholeT3RandomTail

/-- Pointwise training loss decomposition and complete minimizer characterization.
Split each generated observation at W=1/2 and its two bits, use loss_increase,
and sum the treated upper indicators. The nonnegative quadratic coefficient gives
the minimizer and the equality characterization, including empty training sets. -/
def T4_L1 : Prop := WholeT4Training

/-- Population criterion for every parameter. Prove square integrability of the
two-valued prediction, apply population_weighted_criterion_proof, and integrate the
three independent uniforms using unitUniform_bernE and population_loss. The polynomial
3/8+theta^2/6 yields the equality characterization. -/
def T4_L2 : Prop := WholeT4Population

/-- Connect the scalar table to the actual continuous law, including the four disjoint
event masses, bounds, integrability, moments and variances. Use rectangular generator
preimages and unitUniform_Iic, or export an integral transfer to the eight Boolean cells.
Then atom_moments and atom_variances give the numbers; binary Y1 gives its variance.
RepairT4's private transfer proof is a source template, not a public dependency. -/
def T4_L3 : Prop := WholeT4Table

/-- Positivity makes weighted and ordinary L2 equivalent, including infinite norms.
Prove delta<=q<=1/delta, multiply by the nonnegative square and integrate with lintegrals.
Finite positive scaling preserves convergence to zero in ENNReal. -/
def T5_L1 : Prop := WholeT5Norms

/-- A measurable deterministic limit with extended risk no worse than zero has finite
risk and lies in L2. Use the lower q bound, g^2<=2*(Y1-g)^2+2*Y1^2 and bounded Y1.
Convert finite lintegrals to integrable squares, then identify the real risks.
There is no moment assumption on any realized fitted function. -/
def T5_L2 : Prop := ∀ (M : Study), ValidStudy M → ∀ g : ℝ → ℝ, Measurable g →
  wholeRisk M g ≤ wholeRisk M (fun _ => 0) →
    MemLp (fun o => g (W o)) 2 M.law ∧ wholeRisk M g < ⊤ ∧
      risk M g ≤ risk M (fun _ => 0)

/-- On square-integrable fits the extended convergence predicate implies the existing
real-integral predicate. MemLp.sub gives integrable squared errors almost everywhere;
integral_eq_lintegral_of_nonneg_ae identifies their values and ofReal preserves the
positive threshold comparison. No global integrability over training samples is needed. -/
def T5_L3 : Prop := ∀ (M : Study), ValidStudy M →
  ∀ (F : ∀ n, CrossFit n) (g : ℝ → ℝ), MemLp (fun o => g (W o)) 2 M.law →
    (∀ n j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => (F n).g j a (W o)) 2 M.law) →
    ∀ j, WholeL2InProbability M F j g → L2InProbability M F j g

/-- Localize arbitrary fits to the event that their extended squared error is <=1,
using g itself elsewhere. Parameterized lintegral measurability and opposite_fold
make this a CrossFit with exactly the same folds. The localized fits are L2 and
converge in the existing sense. The estimators agree unless one of the two errors
exceeds 1, so the probability of disagreement tends to zero. This is the only
truncation construction; neither rates nor uniform moment bounds are required. -/
def T5_L4 : Prop := ∀ (M : Study), ValidStudy M →
  ∀ (F : ∀ n, CrossFit n) (g : ℝ → ℝ), Measurable g →
    MemLp (fun o => g (W o)) 2 M.law →
    (∀ j, WholeL2InProbability M F j g) →
    ∃ G : ∀ n, CrossFit n,
      (∀ n, (G n).fold = (F n).fold) ∧
      (∀ n j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => (G n).g j a (W o)) 2 M.law) ∧
      (∀ j, L2InProbability M G j g) ∧
      Tendsto (fun n => (sampleLaw M n
        {a | adjusted M (F n) a ≠ adjusted M (G n) a}).toReal) atTop (nhds 0)

/-- Transfer the Gaussian limit between two measurable CrossFit estimator sequences
that disagree with probability tending to zero. Every scaled-distance tail is
contained in the disagreement event. Apply the metric Slutsky/convergence-together
theorem; multiplying by sqrt(n) requires no bound on the disagreement event. -/
def T5_L5 : Prop := ∀ (M : Study), ValidStudy M →
  ∀ (F G : ∀ n, CrossFit n) (v : ℝ),
    NormalLimit M (fun n => adjusted M (G n)) v →
    Tendsto (fun n => (sampleLaw M n
      {a | adjusted M (F n) a ≠ adjusted M (G n) a}).toReal) atTop (nhds 0) →
      NormalLimit M (fun n => adjusted M (F n)) v

theorem T1_assembly (h1 : T1_L1) (h2 : T1_L2) : T1WholeStatement := by
  classical
  have hb := Bridge.target1
  have hM := hb.1
  letI := hM.probability
  have ha : ∀ᵐ a ∂sampleLaw IntervalExample.study 100,
      ht IntervalExample.study a = (wholeS a : ℝ) / 65 ∧
      ht IntervalExample.study a - mu IntervalExample.study = ((wholeS a : ℝ) - 39) / 65 ∧
      xi IntervalExample.study a = IntervalExample.xiK (wholeK a) := by
    exact AronowAudit.P046.Wave1.PropositionThree.n6_proof.mono (fun a ha => h1 a ha)
  have hm := coverage_complement IntervalExample.study hM _ _
    (measurable_ht _ hM 100) (measurable_printed _ hM 100 (1 / 10000000))
  have heq : wholeCoverage IntervalExample.study (ht IntervalExample.study)
      (printedRadius IntervalExample.study (1 / 10000000) (n := 100)) =
      1 - (IntervalExample.certifiedNumerator : ℝ) / 100 ^ 100 := by
    rw [hm]
    exact congrArg (fun t : ℝ => 1 - t) hb.2.2.2.1
  have hbcopy := hb
  obtain ⟨_, _, _, _, _, h119, halpha, _⟩ := hbcopy
  have hlt : (1 / 10000000 : ℝ) < strictNoncoverage IntervalExample.study 100 (1 / 10000000) :=
    lt_trans halpha h119
  refine ⟨hb, h1, count_law, ⟨count_exclusion, h2 h1 count_law⟩,
    fun _ => counts_feasible _, ha, ?_, heq, ?_, ?_⟩
  · decide
  · rw [hm]
    linarith
  · apply lt_of_lt_of_le hlt
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun a h => show printedRadius IntervalExample.study (1 / 10000000) a ≤
      |ht IntervalExample.study a - mu IntervalExample.study| from h.le))

theorem T2_assembly : T2WholeStatement := by
  have hb := Bridge.target2
  have hM := hb.1
  have hm : mu ConditionalExample.study = 1 / 2 := hb.2.2.1
  have hc : condExp (sampleCovariateSigma 100) (sampleLaw ConditionalExample.study 100)
      (ht ConditionalExample.study) =ᵐ[sampleLaw ConditionalExample.study 100]
      muW ConditionalExample.study :=
    AronowAudit.P046.Wave1.ht_conditional_centre_proof (Bridge.toStudy _) (Bridge.valid_to hM)
      100 (by norm_num)
  have hz : ∀ a : Sample 100, a ∈ ConditionalExample.E → muW ConditionalExample.study a = 0 := by
    intro a ha
    have hi (i : Fin 100) : ConditionalExample.study.m (W (a i)) = 0 := by
      have hw := ha i
      change (if (1 / 2 : ℝ) ≤ W (a i) then (1 : ℝ) else 0) = 0
      split_ifs with h
      · exact False.elim (not_le.mpr hw h)
      · rfl
    simp [muW, hi]
  refine ⟨hb, ?_, hc, ?_, ?_⟩
  · intro w x hw
    have hnot (i : Fin 100) : ¬ (1 / 2 : ℝ) ≤ w i := not_le.mpr (hw i)
    have hy (i : Fin 100) : Y (wholeConditionalSample w x i) = 0 := by
      have hy0 : Y0 (wholeConditionalSample w x i) = 0 := rfl
      have hy1 : Y1 (wholeConditionalSample w x i) = 0 := by
        change bit (decide ((1 / 2 : ℝ) ≤ w i)) = 0
        rw [show decide ((1 / 2 : ℝ) ≤ w i) = false from decide_eq_false_iff_not.mpr (hnot i)]
        rfl
      rw [Y, hy0, hy1]
      ring
    have hh : ht ConditionalExample.study (wholeConditionalSample w x) = 0 := by
      simp [ht, htTerm, hy]
    have hz' : muW ConditionalExample.study (wholeConditionalSample w x) = 0 :=
      hz _ (by exact hw)
    exact ⟨hy, hh, hz', by rw [hh, hm]; norm_num⟩
  · have hE : MeasurableSet ConditionalExample.E := by
      unfold ConditionalExample.E
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun i : Fin 100 =>
        measurableSet_lt (measurable_fst.comp (measurable_pi_apply i)) measurable_const)
    filter_upwards [ae_restrict_of_ae hc, ae_restrict_mem hE] with a ha he
    exact ⟨hz a he, ha.trans (hz a he), by rw [hm]; norm_num⟩
  · intro a
    have hd : wholeDenom ConditionalExample.study a = 1 / 81 := by
      norm_num [wholeDenom, ConditionalExample.study]
    refine ⟨hd, ?_⟩
    rw [hd, hb.2.2.2.2.2.1 a]
    convert AronowAudit.P046.ConditionalExample.printed_rhs using 2; ring_nf

theorem T3_assembly (h1 : T3_L1) (h2 : T3_L2) (h3 : T3_L3) : T3WholeStatement := by
  exact ⟨Bridge.target3, h1, h2, t3_fixed h2, h3, t3_sampling, t3_union h3, t3_known⟩

theorem T4_assembly (h1 : T4_L1) (h2 : T4_L2) (h3 : T4_L3) : T4WholeStatement := by
  have hb := Bridge.target4
  have hM := hb.1
  have hbcopy := hb
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hw, hr0, hrg⟩ := hbcopy
  have hn (theta : ℝ) : RegressionExample.prediction theta ≠ (fun _ => 0) := by
    intro h
    have := congrFun h 0
    norm_num [RegressionExample.prediction, RegressionExample.predictionL] at this
  have hl (theta : ℝ) : (3 / 8 : ℝ) ≤
      weightedNormSq RegressionExample.study (RegressionExample.prediction theta) := by
    rw [hw]
    nlinarith [sq_nonneg theta]
  refine ⟨hb, h1, h2, h3, ?_, ?_, ?_, hn, hl, ?_, ?_, by norm_num⟩
  · intro n
    have mh : Measurable wholeH := measurable_htUnit _ hM
    have ma : Measurable wholeA := measurable_wholeA
    exact ⟨iid_sample _ hM n _ mh, iid_sample _ hM n _ ma⟩
  · intro n a
    exact ⟨rfl, rfl⟩
  · intro n j a
    exact ⟨rfl, by simp [RegressionExample.fits, l2Sq]⟩
  · rintro (hz | ⟨u, hu, ht⟩)
    · obtain ⟨theta, htheta⟩ := hz
      exact hn theta htheta
    · have hbnd : ∀ k, (3 / 8 : ℝ) ≤ weightedNormSq RegressionExample.study (u k) := by
        intro k
        obtain ⟨theta, htheta⟩ := hu k
        rw [← htheta]
        exact hl theta
      have hh : (3 / 8 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall hbnd)
      norm_num at hh
  · rw [hr0, hrg]
    norm_num

theorem T5_assembly (h1 : T5_L1) (h2 : T5_L2) (h3 : T5_L3)
    (h4 : T5_L4) (h5 : T5_L5) : T5WholeStatement := by
  refine ⟨h1, ?_, ?_, ?_⟩
  · intro M hM g hg
    exact (AronowAudit.P046.Wave1.fixed_adjusted_variance_proof
      (Bridge.toStudy M) (Bridge.valid_to hM) g hg).1
  · intro M hM d family F hbal hG hz hfit gstar hstar hmin hconv
    have hfits : ∀ n j, ∀ᵐ a ∂sampleLaw M n,
        MemLp (fun o => (F n).g j a (W o)) 2 M.law := by
      intro n j
      exact (hfit n j).mono (fun a ha => by
        obtain ⟨theta, heq, _⟩ := ha
        rw [heq]
        exact hG theta)
    have hg : MemLp (fun o => gstar (W o)) 2 M.law := by
      obtain ⟨theta, heq⟩ := hstar
      rw [← heq]
      exact hG theta
    exact Bridge.target5.1 M hM d family F hbal hG hz hfit gstar hstar hmin
      (fun j => h3 M hM F gstar hg hfits j (hconv j))
  · intro M hM F hbal g mg hconv hr
    obtain ⟨hg, hfin, hbetter⟩ := h2 M hM g mg hr
    obtain ⟨G, hfold, hfits, hc, he⟩ := h4 M hM F g mg hg hconv
    have hbalG : Balanced G := by
      intro j
      simpa only [hfold] using hbal j
    have hcG := Bridge.target5.2 M hM G hbalG g hg hc hfits hbetter
    exact ⟨hg, hfin, hbetter, h5 M hM F G _ hcG.1 he, hcG.2⟩

end
end SAP.P046.WH.W1
