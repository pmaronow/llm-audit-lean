import SAP.P001a.Defs.WholeW2
import AronowAudit.P001.Wave1.Gap.TailA.MatchingFinals
import AronowAudit.P001.Wave1.Gap.TailA.HotDeckL2
import AronowAudit.P001.Wave1.Gap.GP0012B1

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001.Wave1
open scoped BigOperators ENNReal NNReal Topology Classical Matrix

noncomputable section

namespace SAP.P001a.WH.W2

universe u v

/-- Identify the continuous unit law: uniform score and shifted covariate,
independent fair sign, response marginal, support and outcome moments.
Use matching_unit_factorization and matching_score_marginal; identify uniformLaw
with twice restricted Lebesgue measure, translate by -1/4, and integrate the
two-point sign law. Atomlessness follows from Lebesgue singleton mass zero. -/
def T13_L1 : Prop := W2MatchingMarginals

/-- Identify the propensity versions and the conditional independence statements.
Use the product factorization of the sign from (score,response). Integrate over
preimages of arbitrary measurable score sets to prove the two CEF identities.
The same product calculation gives the conditional indicator factorization in CI.
Shifting the score is a measurable equivalence and preserves its conditioning
sigma-algebra. Composing the independent sign gives MCAR and both outcome pairs. -/
def T13_L2 : Prop := W2MatchingConditional

/-- A measurable square-integrable unbiased sequence with a finite limit of
n times its variance is root-n tight. Use eventual boundedness of the convergent
real variance sequence and Chebyshev; choose M with C/M^2 below the requested
tail probability. Only positive sample sizes are used, and all second moments
exist explicitly. This shared probability lemma also serves T15. -/
def T13_L3 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ → Ω → ℝ) (θ V : ℝ),
    (∀ n, MemLp (T n) 2 μ) →
    (∀ n, 0 < n → mean μ (T n) = θ) →
    Tendsto (fun (n : ℕ) => (n : ℝ)*var μ (T n)) atTop (nhds V) →
    W2RootNTight μ T θ

/-- A measurable real sequence with uniformly bounded ordinary second moments
is uniformly integrable in L1. All squared integrals are genuine: each term is
in L2. Bound the L1 tail at cutoff K by C/K and apply uniformIntegrable_of, or
use Mathlib's uniform Lp bound criterion with exponents 1 and 2. -/
def T13_L4 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ), (∀ n, MemLp (V n) 2 μ) →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n, mean μ (fun ω => (V n ω)^2) ≤ C) →
    UniformIntegrable V 1 μ

/-- Certify the two displayed decimals. Use log_three_gt_d9, log_three_lt_d9,
exp_neg_one_gt_d9 and exp_neg_one_lt_d9, then rational interval arithmetic with
positive denominators s and 2-s. Occupancy inequalities and positivity already
exist; the exact gap is ring arithmetic. The tolerances mean rounding to four
decimal places. Shared with T15. -/
def T13_L5 : Prop :=
  |matchV - 3.0458| < 0.00005 ∧ |matchVB - 2.6471| < 0.00005

theorem matching_constants (h : T13_L5) : W2MatchingConstants := by
  obtain ⟨hs, hs1, hA, hB, hgap⟩ := AronowAudit.P001.hot_deck_bootstrap_constant_inequalities
  refine ⟨hs, hs1, hA, hB,
    AronowAudit.P001.TailA.matching_endpoint_constants_positive.2.2, hgap, ?_, h⟩
  unfold matchV matchVB
  ring

theorem matching_realization : W2MatchingRealization := by
  exact ⟨AronowAudit.P001.TailA.matchingCanonicalLaw, inferInstance,
    AronowAudit.P001.TailA.matching_endpoint_canonical_iid,
    AronowAudit.P001.TailA.matching_endpoint_canonical_law⟩

theorem hot_memLp {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : IID μ Z) (n : ℕ) :
    MemLp (fun ω => hotDeck (firstSample Z n ω)) 2 μ := by
  apply MemLp.of_bound
    ((AronowAudit.P001.TailA.matching_hotDeck_measurable n).comp
      (AronowAudit.P001.TailA.matching_endpoint_first_measurable hiid n)).aestronglyMeasurable 51
  exact Filter.Eventually.of_forall (fun ω => AronowAudit.P001.TailA.matching_hotDeck_bound _)

theorem causal_memLp {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : IID μ Z) (n : ℕ) :
    MemLp (fun ω => causalMatch (firstSample Z n ω)) 2 μ := by
  apply MemLp.of_bound
    ((AronowAudit.P001.TailA.matching_causalMatch_measurable n).comp
      (AronowAudit.P001.TailA.matching_endpoint_first_measurable hiid n)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun ω => AronowAudit.P001.TailA.matching_causalMatch_bound _)

theorem boot_memLp {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : IID μ Z) (n : ℕ) :
    MemLp (fun ω => bootVar hotDeck (firstSample Z n ω)) 2 μ := by
  apply MemLp.of_bound
    ((AronowAudit.P001.TailA.matching_bootVar_measurable
      (AronowAudit.P001.TailA.matching_hotDeck_measurable n)).comp
      (AronowAudit.P001.TailA.matching_endpoint_first_measurable hiid n)).aestronglyMeasurable
      ((2*(51 : ℝ))^2)
  exact Filter.Eventually.of_forall (fun ω =>
    AronowAudit.P001.TailA.matching_bootVar_bound _ 51
      (fun s => AronowAudit.P001.TailA.matching_hotDeck_bound s) _)

/-- The actual iid witness satisfies all antecedents of the auxiliary
bias-only calibration rule and violates its standard-error conclusion. -/
theorem hot_deck_bias_only_calibration_false (h3 : T13_L3.{u}) :
    ¬ W2HotDeckBiasOnlyCalibration.{u} := by
  intro hcal
  let μ := AronowAudit.P001.TailA.matchingCanonicalLiftedLaw.{u}
  let Z := fun (n : ℕ) (ω : ULift.{u} (ℕ → ℝ × Bool × Bool)) => ω.down n
  have hiid : IID μ Z := AronowAudit.P001.TailA.matching_endpoint_canonical_lifted_iid
  have hlaw : μ.map (Z 0)=matchingUnitLaw :=
    AronowAudit.P001.TailA.matching_endpoint_canonical_lifted_law 0
  have hf : MatchingFailure μ Z false :=
    AronowAudit.P001.Wave1.TailA.hot_deck_bootstrap_counterexample_final μ Z hiid hlaw
  have ht := h3 μ _ 50 matchV (hot_memLp μ Z hiid) hf.1 hf.2.1
  have hse := hcal μ Z hiid hlaw hf.1 ht hf.2.1
  apply hf.2.2.2.2.2
  exact (AronowAudit.P001.variance_se_consistency_equivalence μ _
    (fun n ω => AronowAudit.P001.TailA.matching_endpoint_bootVar_nonneg _ _)
    matchV (le_trans hf.2.2.2.1.le hf.2.2.2.2.1.le)).mpr hse

theorem T13_example_assembly (h1 : T13_L1) (h2 : T13_L2) (h3 : T13_L3.{u})
    (h4 : T13_L4.{u}) (h5 : T13_L5) : T13BootstrapFailureExampleStatement.{u} := by
  refine ⟨h1, h2, matching_constants h5, ?_, ?_, ?_, matching_realization,
    hot_deck_bias_only_calibration_false h3⟩
  · intro u
    constructor
    · intro h; simp [W2CensoredOutcome, h]
    · intro h; simp [W2CensoredOutcome, h]
  · filter_upwards [h1.2.2.2.2.2.2.1] with u hu
    constructor <;> linarith [hu.1, hu.2]
  · intro Ω _ μ _ Z hiid hlaw
    have hf : MatchingFailure μ Z false :=
      AronowAudit.P001.Wave1.TailA.hot_deck_bootstrap_counterexample_final μ Z hiid hlaw
    have hC : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
        mean μ (fun ω => ((n : ℝ)*bootVar hotDeck (firstSample Z n ω))^2) ≤ C :=
      AronowAudit.P001.Wave1.TailA.hot_deck_bootstrap_uniform_second_moment_final μ Z hiid hlaw
    refine ⟨hf, h3 μ _ 50 matchV (hot_memLp μ Z hiid) hf.1 hf.2.1, hC,
      h4 μ _ (fun n => (boot_memLp μ Z hiid n).const_mul (n : ℝ)) hC, ?_⟩
    intro hse
    apply hf.2.2.2.2.2
    exact (AronowAudit.P001.variance_se_consistency_equivalence μ _
      (fun n ω => AronowAudit.P001.TailA.matching_endpoint_bootVar_nonneg _ _)
      matchV (le_trans (matching_constants h5).2.2.2.2.1.le
        (matching_constants h5).2.2.2.2.2.1.le)).mpr hse

/-- The independent fitted-score example contradicts the auxiliary mathematical
calibration rule, with no claim about either printed qualitative assertion. -/
theorem estimated_match_bias_only_calibration_false (h3 : T13_L3.{u}) :
    ¬ W2EstimatedMatchBiasOnlyCalibration.{u} := by
  intro hcal
  let μ := AronowAudit.P001.TailA.matchingCanonicalLiftedLaw.{u}
  let Z := fun (n : ℕ) (ω : ULift.{u} (ℕ → ℝ × Bool × Bool)) => ω.down n
  have hiid : IID μ Z := AronowAudit.P001.TailA.matching_endpoint_canonical_lifted_iid
  have hlaw : μ.map (Z 0)=matchingUnitLaw :=
    AronowAudit.P001.TailA.matching_endpoint_canonical_lifted_law 0
  have heq {n : ℕ} (s : Fin n → ℝ × Bool × Bool) :
      causalMatchEstimated s=causalMatch s := AronowAudit.P001.estimated_matching_statistic_equal s
  have hknown : MatchingFailure μ Z true :=
    AronowAudit.P001.Wave1.TailA.matching_bootstrap_counterexample_supporting_final μ Z hiid hlaw
  have hf : W2EstimatedMatchingFailure μ Z := by
    simpa only [W2EstimatedMatchingFailure, MatchingFailure, ite_true, heq, bootVar, bootMean]
      using hknown
  have h2 (n : ℕ) : MemLp (fun ω => causalMatchEstimated (firstSample Z n ω)) 2 μ := by
    simpa only [heq] using causal_memLp μ Z hiid n
  have ht := h3 μ _ 0 matchV h2 hf.1 hf.2.1
  have ha : CP μ (fun n ω => estimatedMatchIntercept (firstSample Z n ω)) (1/4) :=
    AronowAudit.P001.Wave1.matching_score_intercept_consistent_proof μ Z hiid hlaw
  have hse := hcal μ Z hiid hlaw ha hf.1 ht hf.2.1
  apply hf.2.2.2.2.2
  exact (AronowAudit.P001.variance_se_consistency_equivalence μ _
    (fun n ω => AronowAudit.P001.TailA.matching_endpoint_bootVar_nonneg _ _)
    matchV (le_trans hf.2.2.2.1.le hf.2.2.2.2.1.le)).mpr hse

theorem T15_example_assembly (h1 : T13_L1) (h2 : T13_L2) (h3 : T13_L3.{u})
    (h5 : T13_L5) : T15BootstrapFailureExampleStatement.{u} := by
  have heq {n : ℕ} (s : Fin n → ℝ × Bool × Bool) :
      causalMatchEstimated s = causalMatch s :=
    AronowAudit.P001.estimated_matching_statistic_equal s
  have hboot {n : ℕ} (s : Fin n → ℝ × Bool × Bool) :
      bootVar causalMatchEstimated s = bootVar causalMatch s := by
    unfold bootVar bootMean
    simp only [heq]
  refine ⟨h1, h2, matching_constants h5, ?_, ?_, ?_, ?_, matching_realization,
    estimated_match_bias_only_calibration_false h3⟩
  · intro u
    refine ⟨by simp [W2Observed, W2Potential], ?_, by simp [W2Potential]⟩
    cases h : u.2.2 <;> norm_num [W2Potential, W2Noise, noise, h]
  · intro n s
    refine ⟨?_, ?_, heq s, fun a => heq _, hboot s⟩
    · intro x z; constructor <;> congr 1 <;> ring
    · exact AronowAudit.P001.estimated_score_matches_equal s
  · intro n hn p d e
    rw [heq]
    exact (AronowAudit.P001.Wave1.causal_matching_conditional_reuse_variance_proof hn p d).1 e
  · intro Ω _ μ _ Z hiid hlaw
    have ha : CP μ (fun n ω => estimatedMatchIntercept (firstSample Z n ω)) (1/4) :=
      AronowAudit.P001.Wave1.matching_score_intercept_consistent_proof μ Z hiid hlaw
    have hf : MatchingFailure μ Z true :=
      AronowAudit.P001.Wave1.TailA.matching_bootstrap_counterexample_supporting_final μ Z hiid hlaw
    have hehf : W2EstimatedMatchingFailure μ Z := by
      simpa only [W2EstimatedMatchingFailure, MatchingFailure, ite_true, heq, hboot] using hf
    refine ⟨ha, ?_, hehf, fun n ω => heq _, ?_, ?_⟩
    · intro ε hε
      have hs (n : ℕ) :
          {ω | ∃ x ∈ Set.Icc (0 : ℝ) (1/2), ε ≤
              |(estimatedMatchIntercept (firstSample Z n ω)+x)-(1/4+x)|} =
          {ω | ε ≤ dist (estimatedMatchIntercept (firstSample Z n ω)) (1/4 : ℝ)} := by
        ext ω
        have hid (x : ℝ) :
            (estimatedMatchIntercept (firstSample Z n ω)+x)-(1/4+x) =
              estimatedMatchIntercept (firstSample Z n ω)-1/4 := by ring
        simp only [Set.mem_ofPred_eq, hid, Real.dist_eq]
        constructor
        · rintro ⟨x, _, hx⟩; exact hx
        · intro hx; exact ⟨0, by norm_num, hx⟩
      simpa only [hs] using ha ε hε
    · simpa only [heq] using h3 μ _ 0 matchV (causal_memLp μ Z hiid) hf.1 hf.2.1
    · simp only [hboot]
      intro hse
      apply hf.2.2.2.2.2
      exact (AronowAudit.P001.variance_se_consistency_equivalence μ _
        (fun n ω => AronowAudit.P001.TailA.matching_endpoint_bootVar_nonneg _ _)
        matchV (le_trans (matching_constants h5).2.2.2.2.1.le
          (matching_constants h5).2.2.2.2.2.1.le)).mpr hse

end SAP.P001a.WH.W2
