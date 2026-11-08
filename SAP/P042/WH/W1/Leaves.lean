import SAP.P042.Defs.WholeW1
import SAP.P042.Bridge
import AronowAudit.P033.Wave1.Gap.GLP010P033P033B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042.WH.W1

noncomputable section
open SAP.P042 SAP.P042.Bridge Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory
open Classical

/-- T1: integer coverage thresholds hold uniformly on the certified multiplier range.
Prove `coversZero e r ↔ |e| ≤ r`, rewrite `sqrt(1/400)=1/20`, and bound
`sqrt(3/800)` between 6123/100000 and 6124/100000 with `sqrt_enclosure`.
The resulting scaled radii lie in [19,20) and [24,25). Cast the strict upper bounds
back to integers and use discreteness. Adapt `binomial_interval_thresholds`;
no enumeration or probability calculation is needed. Expected size: under 100 lines. -/
def T1_L1 : Prop :=
  ∀ z : ℝ, 19599 / 10000 ≤ z → z ≤ 49 / 25 → ∀ q : ℤ,
    (coversZero ((q : ℝ) / 200) (z * Real.sqrt (1 / 400)) ↔ |q| ≤ 19) ∧
    (coversZero ((q : ℝ) / 200) (z * Real.sqrt (3 / 800)) ↔ |q| ≤ 24)

/-- T3: the complete square-root-free endpoint comparison family.
Use `Real.sqrt_nonneg` and `Real.sq_sqrt` to show the radius is nonnegative and its
square is `z^2*V`. Apply `sq_lt_sq₀` and `sq_le_sq₀` to this radius and the positive
gaps `μ-L` and `U-μ`; linear arithmetic translates back to endpoint comparisons.
Reverse comparisons can also be obtained by negating the strict/non-strict forms.
All sign premises are in `EndpointSquareLaw`. Expected size: under 100 lines. -/
def T3_L1 : Prop := EndpointSquareLaw

/-- T6: sampled-subject independence, expressed by event factorization for every
fixed attribute and every Boolean assignment value. Exchange the subject sum and
assignment expectation. `complete_inclusion_probability` makes the expected assignment
indicator constant in the subject. The false case follows by subtracting from one.
Factor the attribute indicator out and reverse the sum exchange for the marginal.
This is independence of one sampled subject's assignment, with no assertion of
independence between different subjects' assignments. Expected size: under 150 lines. -/
def T6_L1 : Prop := SampledSubjectIndependence

/-- T6: changing an unobserved contacted potential outcome of a Never-taker.
Split on `i=k` and on the assignment/contact Boolean to prove identical observations.
For the mean effect, write the perturbed summand as the old summand plus the singleton
indicator times δ, then sum and divide. The Never-taker count is positive because it
contains k. If the old schedule is binary and δ=1-2*Y_k(true), the new entry is its
binary complement; prove preservation by the same split. Expected size: under 150 lines. -/
def T6_L2 : Prop :=
  ∀ (N : ℕ) (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) (k : Fin N) (δ : ℝ),
    c k = false →
    (∀ S, contactedOutcome S (perturbContact Y k δ) c = contactedOutcome S Y c) ∧
    perturbContact Y k δ k true - perturbContact Y k δ k false =
      Y k true - Y k false + δ ∧
    neverTakerEffect (perturbContact Y k δ) c =
      neverTakerEffect Y c + δ / (neverTakerCount c : ℝ) ∧
    (BinarySchedule Y → δ = 1 - 2 * Y k true → BinarySchedule (perturbContact Y k δ))

/-- Identify the local Mathlib-only quantile with the existing certified one. -/
theorem normal975_eq : normal975 = AronowAudit.P033.normalCritical := rfl

/-- Reuse the proved Gaussian inverse-CDF certificate; its defining set is inhabited
and bounded below, so the infimum has its ordinary quantile meaning. -/
theorem normal975_certificate : Normal975Certificate := by
  have hq : standardNormalCDF normal975 = 39 / 40 :=
    AronowAudit.P033.Wave1.native_power_correction_critical_cdf
  have hb := AronowAudit.P033.Wave1.binary_standardization.critical_bounds
  change (195996398454005 / 10 ^ 14 : ℝ) < normal975 ∧
    normal975 < (195996398454006 / 10 ^ 14 : ℝ) at hb
  refine ⟨⟨normal975, hq.ge⟩, ?_, hq, by linarith [hb.1], by linarith [hb.2]⟩
  refine ⟨(195996398454005 / 10 ^ 14 : ℝ), ?_⟩
  intro x hx
  have hlo := AronowAudit.P033.Wave1.binary_standardization.z_lo_cdf
  change (39 : ℝ) / 40 ≤ AronowAudit.P033.normalCDF x at hx
  by_contra hn
  have hxle : x ≤ (195996398454005 / 10 ^ 14 : ℝ) := le_of_lt (lt_of_not_ge hn)
  have hm := AronowAudit.P033.Wave1.binary_standardization.cdf_mono hxle
  linarith

/-- T1 assembly: reuse all existing exact moments and coverage certificates and
transport the event indicators using the one new integer-threshold lemma. -/
theorem T1_assembly (h1 : T1_L1) : T1WholeStatement := by
  have hexisting : T1Statement := by
    constructor
    · rcases AronowAudit.P042.six_design with ⟨hcard, hdesign⟩
      rcases AronowAudit.P042.six_moments with ⟨he1, he2, hv1, hv2, hc, hv, hs⟩
      rcases AronowAudit.P042.six_counterexample with ⟨hw1, hw2, hd, hW, hf, hlt⟩
      exact ⟨AronowAudit.P042.six_sharp_null, hcard, by decide, hdesign,
        he1, he2, hv1, hv2, hc, hw1, hw2, hd, hW, hv, hs, hf, hlt⟩
    · have hArm := AronowAudit.P042.binomial_arm_moments
      simp only [← binomialMass_eq, ← binomialArmExpectation_eq] at hArm
      have hMom := AronowAudit.P042.binomial_shared_control_moments
      simp only [← binomialTripleExpectation_eq, ← binomialTripleVariance_eq,
        ← binomialTripleCovariance_eq, ← binomialD1_eq, ← binomialD2_eq,
        ← binomialPooled_eq] at hMom
      rcases hMom with ⟨he1, he2, hv1, hv2, hc, hcv, hformula, he, hv, hlt⟩
      rcases AronowAudit.P042.binomial_diagonal with ⟨hw1, hw2, hd, hW, hfactor⟩
      have hCov := AronowAudit.P042.binomial_coverage_exact
      simp only [← binomialCoverage_eq] at hCov
      rcases hCov with ⟨hfrac, hlo, hhi, hnom, htrue⟩
      have hsq := (AronowAudit.P042.binomial_interval_thresholds 0 0 0).2.2
      exact ⟨hArm.1, hArm.2.1, he1, he2, hv1, hv2, hc, hcv,
        hw1, hw2, hd, hW, hformula, he, hv, hv.trans hfactor, hlt,
        AronowAudit.P042.binomial_diagonal_radius, binomial_thresholds,
        ⟨hsq.1, by norm_num, by norm_num⟩, binomial_nominal_coverage, binomial_true_coverage,
        hfrac, AronowAudit.P042.binomial_coverage_fraction_reduced, hlo, hhi, hnom, htrue⟩
  have hall : ∀ z : ℝ, 19599 / 10000 ≤ z → z ≤ 49 / 25 → BinomialMultiplierFacts z := by
    intro z hzlo hzhi
    have ht (x0 x1 x2 : Fin 101) := h1 z hzlo hzhi
      ((x1.val : ℤ) + (x2.val : ℤ) - 2 * (x0.val : ℤ))
    have hevents (x0 x1 x2 : Fin 101) :
        (coversZero (binomialPooled x0 x1 x2 : ℝ)
          (z * Real.sqrt (1 / 400)) ↔
          |(x1.val : ℤ) + (x2.val : ℤ) - 2 * (x0.val : ℤ)| ≤ 19) ∧
        (coversZero (binomialPooled x0 x1 x2 : ℝ)
          (z * Real.sqrt (3 / 800)) ↔
          |(x1.val : ℤ) + (x2.val : ℤ) - 2 * (x0.val : ℤ)| ≤ 24) := by
      simpa only [binomialPooled_cast] using ht x0 x1 x2
    refine ⟨hevents, ?_, ?_⟩
    · have he : (fun x0 x1 x2 : Fin 101 =>
          if coversZero (binomialPooled x0 x1 x2 : ℝ)
            (z * Real.sqrt (1 / 400)) then (1 : ℚ) else 0) = binomialCountEvent 19 := by
        funext x0 x1 x2
        rw [(hevents x0 x1 x2).1]
        unfold binomialCountEvent
        norm_num only [Nat.cast_ofNat]
        split_ifs <;> rfl
      rw [he, binomialTripleExpectation_eq, binomialCoverage_eq]
      exact AronowAudit.P042.Wave1.binomial_coverage_from_arms_proof 19
    · have he : (fun x0 x1 x2 : Fin 101 =>
          if coversZero (binomialPooled x0 x1 x2 : ℝ)
            (z * Real.sqrt (3 / 800)) then (1 : ℚ) else 0) = binomialCountEvent 24 := by
        funext x0 x1 x2
        rw [(hevents x0 x1 x2).2]
        unfold binomialCountEvent
        norm_num only [Nat.cast_ofNat]
        split_ifs <;> rfl
      rw [he, binomialTripleExpectation_eq, binomialCoverage_eq]
      exact AronowAudit.P042.Wave1.binomial_coverage_from_arms_proof 24
  exact ⟨hexisting, normal975_certificate, hall,
    hall normal975 normal975_certificate.2.2.2.1 normal975_certificate.2.2.2.2⟩

/-- T3 assembly: exact arithmetic and the quantile certificate are existing results;
monotonicity and the multiplier-endpoint principle are short order arguments. -/
theorem T3_assembly (h1 : T3_L1) : T3WholeStatement := by
  have hzlo := normal975_certificate.2.2.2.1
  have hzhi := normal975_certificate.2.2.2.2
  have hF := AronowAudit.P042.robo_fixed_endpoint_counterexample normal975 hzlo hzhi
  have hR := AronowAudit.P042.robo_random_interval normal975 hzlo hzhi
  refine ⟨⟨robo_fixed_exact, AronowAudit.P042.robo_fixed_counterexample,
      AronowAudit.P042.robo_fixed_endpoint_counterexample, robo_random_exact,
      robo_random_rounding⟩, normal975_certificate, ?_, ⟨hF.1, hF.2.2.1⟩, hR, h1, ?_⟩
  · rcases robo_random_exact with ⟨_, _, _, _, _, hτ, _, _, _, _⟩
    rw [hτ]
    norm_num
  · intro μ V hV
    have hl : Antitone (fun z : ℝ => μ - z * Real.sqrt V) := by
      intro a b hab
      have hm := mul_le_mul_of_nonneg_right hab (Real.sqrt_nonneg V)
      linarith
    have hu : Monotone (fun z : ℝ => μ + z * Real.sqrt V) := by
      intro a b hab
      have hm := mul_le_mul_of_nonneg_right hab (Real.sqrt_nonneg V)
      linarith
    have hs : MonotoneOn (fun z : ℝ => z ^ 2 * V) (Set.Ici 0) := by
      intro a ha b hb hab
      exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ ha hb).2 hab) hV
    refine ⟨hl, hu, hs, ?_⟩
    intro a b z ha haz hzb
    exact ⟨hl hzb, hl haz, hu haz, hu hzb,
      hs ha (ha.trans haz) haz, hs (ha.trans haz) (ha.trans (haz.trans hzb)) hzb⟩

/-- T5 partial result: both audit-formula negations have square-integrable six-voter
counterexamples with positive variances. This is not an assembly of a whole printed
claim; T5 retains its pre-existing restricted theorem. -/
theorem T5_variance_formula_refutation : T5VarianceFormulaRefutation := by
  exact ⟨AronowAudit.P042.Wave1.printed_pooling_variance_refuted,
    AronowAudit.P042.Wave1.printed_comparison_variance_refuted⟩

/-- T6 complete-randomization specialization: reuse the exact identities; the two
unchanged leaves supply sampled-subject independence and an unobserved-outcome
perturbation. The positive Never-taker denominator follows from the named member. -/
theorem T6_complete_randomization_assembly (h1 : T6_L1) (h2 : T6_L2) :
    T6CompleteRandomizationStatement := by
  have hexisting : T6Statement := by
    refine ⟨?_, AronowAudit.P042.michelson_cace_example⟩
    intro N m hN hm hmN Y
    have hb := AronowAudit.P042.complete_randomization_balance hN hm hmN Y
    refine ⟨hb.1, hb.2, ?_⟩
    intro c hc
    have hi := AronowAudit.P042.cace_randomization_identity hN hm hmN Y c hc
    refine ⟨AronowAudit.P042.itt_complier_identity (by omega) Y c hc,
      hi.1, hi.2.1, ?_, hi.2.2⟩
    rw [show finiteExpectation (completeAssignments N m)
        (fun s => assignedContactRate m s c) = complierShare c from hi.2.1]
    exact div_pos (by exact_mod_cast hc) (by exact_mod_cast (show 0 < N by omega))
  have hchanged (N : ℕ) (Y : Fin N → Bool → ℝ) (c : Fin N → Bool)
      (k : Fin N) (δ : ℝ) (hk : c k = false) (hδ : δ ≠ 0) :
      perturbContact Y k δ k true - perturbContact Y k δ k false ≠
        Y k true - Y k false ∧
      neverTakerEffect (perturbContact Y k δ) c ≠ neverTakerEffect Y c := by
    have hp := h2 N Y c k δ hk
    have hc : 0 < neverTakerCount c := by
      apply Finset.card_pos.mpr
      exact ⟨k, by simp [hk]⟩
    have hcne : (neverTakerCount c : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hc
    constructor
    · intro he
      exact hδ (by linarith [hp.2.1])
    · intro he
      exact (div_ne_zero hδ hcne) (by linarith [hp.2.2.1])
  refine ⟨hexisting, ?_, h1, ?_, ?_⟩
  · intro N Y Ω _ μ _ Z
    exact indepFun_const_right Z Y
  · intro N m hN hm hmN Y c S hS hrate
    exact ⟨rfl, div_mul_cancel₀ _ (ne_of_gt hrate)⟩
  · constructor
    · intro N Y c k δ hk hδ
      have hp := h2 N Y c k δ hk
      exact ⟨perturbContact Y k δ, hp.1, hp.2.1, hp.2.2.1,
        (hchanged N Y c k δ hk hδ).1, (hchanged N Y c k δ hk hδ).2⟩
    · intro N Y c k hb hk
      let δ := 1 - 2 * Y k true
      have hδ : δ ≠ 0 := by
        rcases hb k true with ht | ht <;> norm_num [δ, ht]
      have hp := h2 N Y c k δ hk
      exact ⟨perturbContact Y k δ, hp.2.2.2 hb rfl, hp.1,
        (hchanged N Y c k δ hk hδ).1, (hchanged N Y c k δ hk hδ).2⟩

/-- A complete arithmetic counterexample to the printed balance assertion under S1:
the finite law has two positive known masses summing to one and nonempty arms. -/
theorem biased_two_balance_counterexample : BiasedTwoBalanceCounterexample := by
  have hp : ∀ a, 0 < biasedTwoProbability a := by
    intro a
    fin_cases a <;> norm_num [biasedTwoProbability]
  have hy : BinarySchedule biasedTwoOutcome := by
    intro i t
    by_cases hi : i = 0 <;> simp [biasedTwoOutcome, hi]
  have hc : ∀ a, (biasedTwoAssignment a).card = 1 ∧
      (Finset.univ \ biasedTwoAssignment a).card = 1 := by
    intro a
    fin_cases a <;> decide
  refine ⟨hp, ?_, hy, hc, ?_, ?_, ?_⟩
  · norm_num [biasedTwoProbability, Fin.sum_univ_two]
  · intro t
    norm_num [biasedTwoExpectation, biasedTwoProbability, biasedTwoAssignment,
      biasedTwoOutcome, assignedTreatmentMean, assignedControlMean, populationMean,
      Fin.sum_univ_two]
  · norm_num [biasedTwoExpectation, biasedTwoProbability, biasedTwoAssignment,
      biasedTwoOutcome, assignedTreatmentMean, assignedControlMean, assignedOutcome,
      Fin.sum_univ_two]
  · norm_num [populationMean, biasedTwoOutcome, Fin.sum_univ_two]

/-- Specialize the printed balance assertion to the fully normalized finite law. -/
theorem known_probability_balance_refuted : ¬ KnownProbabilityBalanceAssertion := by
  intro h
  rcases biased_two_balance_counterexample with ⟨hp, hsum, hy, hc, hmeans, _, _⟩
  have heq := h 2 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    biasedTwoProbability (fun a => (hp a).le) hsum biasedTwoAssignment
    (fun a => (hc a).1) biasedTwoOutcome hy false
  exact (hmeans false).2.2.2 heq

/-- T6 assembly: refute the broader printed assertion by a finite known-probability
counterexample, and retain the correctly named complete-randomization specialization.
Both leaves keep exactly their original meanings and are used only for that specialization. -/
theorem T6_assembly (h1 : T6_L1) (h2 : T6_L2) : T6WholeStatement := by
  exact ⟨biased_two_balance_counterexample, known_probability_balance_refuted,
    T6_complete_randomization_assembly h1 h2⟩

end
end SAP.P042.WH.W1
