import SAP.P032.Defs
import SAP.P032.Bridge
import AronowAudit.P032.P032_Dyadic
import SAP.P032.WH.W1.Proofs.T9

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory Filter SAP.P032 SAP.P032.Bridge AronowAudit.P032

theorem SAP.P032.T1 {Ω : Type*} [MeasurableSpace Ω] : SAP.P032.T1Statement Ω := by
  refine ⟨pair_error_moments, bounded_pair_sampling_models, pair_eigenbasis_certificate,
    intercept_counterexample, slope_and_sign_control, four_block_moments,
    block_covariances_positive_definite, block_eigenbasis_certificates, four_block_counterexample,
    ?_, six_sign_error_moments, six_block_variances, six_errors_bounded, ?_,
    six_sign_measure_product, finite_law_iid_exists fourBlockLaw,
    finite_law_iid_exists sixSignLaw, fourReplication, sixReplication⟩
  · intro a
    exact interceptFit fourDyadData (by norm_num) (fourErrorValues a)
  · intro a
    exact interceptFit sixDyadData (by norm_num) (sixErrorValues a)

theorem SAP.P032.T2 {R M P Ω : Type*} [Fintype R] [Fintype M] [Fintype P]
    [DecidableEq R] [DecidableEq M] [DecidableEq P] [MeasurableSpace Ω] :
    SAP.P032.T2Statement R M P Ω := by
  refine ⟨?_, pair_error_moments, bounded_pair_sampling_models, intercept_counterexample,
    slope_and_sign_control, omitted_sign_not_determined⟩
  intro μ hμ d X hr β u hu hm
  dsimp only
  let da := fun r => toAuditDyad (d r)
  have hv : ∀ c, variance
      (fun ω => c ⬝ᵥ leastSquares X (X *ᵥ β + fun r => u r ω)) μ =
        quadForm (errorMoments μ u) (X *ᵥ (olsBread X *ᵥ c)) ∧
      quadForm (errorMoments μ u) (X *ᵥ (olsBread X *ᵥ c)) =
        quadForm (sandwichCovariance X (errorMoments μ u)) c :=
    fun c => ols_contrast_variance μ X hr β c u hu hm
  have hs : (errorCovariance μ u).transpose = errorCovariance μ u := by
    ext r s
    simp [errorCovariance, mul_comm]
  refine ⟨?_, ?_, omitted_sandwich_psd_iff da X hr (errorCovariance μ u)⟩
  · intro c
    refine ⟨fun ω => ols_contrast_error X hr β c (fun r => u r ω),
      (hv c).1, (hv c).2, variance_difference da (errorCovariance μ u) _, ?_⟩
    rw [(hv c).1]
    exact variance_sign_conditions da (errorCovariance μ u) _
  · have he := all_contrasts_lower_bound_iff da X hr (errorCovariance μ u) hs
    constructor
    · intro h
      apply he.mp
      intro c
      have hc := h c
      rwa [(hv c).1] at hc
    · intro h c
      rw [(hv c).1]
      exact he.mpr h c

theorem SAP.P032.T3 : SAP.P032.T3Statement := by
  exact survivalAssembly

theorem SAP.P032.T4 {R M P G : Type*} [Fintype R] [Fintype M] [Fintype P]
    [DecidableEq R] [DecidableEq M] [DecidableEq P] [DecidableEq G] :
    SAP.P032.T4Statement R M P G := by
  refine ⟨?_, ?_, ?_, ?_, survivalAssembly.2.2.2.2.1⟩
  · intro d z
    exact corrected_decomposition (fun r => toAuditDyad (d r)) z
  · intro d r s
    have hc : pairCoefficient d r s = dyadicMask d r s :=
      decomposition_coefficient (fun r => toAuditDyad (d r)) r s
    refine ⟨hc, ?_, ?_, ?_, ?_⟩
    · intro hrs
      subst s
      have hn : (d r).members.Nonempty := Finset.card_pos.mp (by rw [(d r).two]; decide)
      rw [hc]
      simp [dyadicMask, hn]
      ring
    · intro _ heq
      have hn : (d s).members.Nonempty := Finset.card_pos.mp (by rw [(d s).two]; decide)
      rw [hc]
      norm_num [dyadicMask, heq, hn]
    · intro _ hcard
      have hn : ((d r).members ∩ (d s).members).Nonempty :=
        Finset.card_pos.mp (by rw [hcard]; decide)
      rw [hc]
      norm_num [dyadicMask, hn]
    · intro hn
      rw [hc]
      simp [dyadicMask, hn]
  · intro a b
    exact dyad_intersection_cases (toAuditDyad a) (toAuditDyad b)
  · intro d z g
    dsimp only
    let da := fun r => toAuditDyad (d r)
    refine ⟨id_cross_products g z, ?_, id_substitution_cross_discrepancy da z g, ?_, ?_⟩
    · have he := id_substitution_discrepancy da z (scoreCovariance (subjectMask g) z) 1
      simp only [one_smul] at he
      exact he
    · intro hg
      have he : scoreCovariance (subjectMask g) z = scoreCovariance recordMask z :=
        singleton_id_covariance g hg z
      refine ⟨he, ?_⟩
      rw [he]
      exact corrected_decomposition da z
    · intro α
      exact id_substitution_discrepancy da z (scoreCovariance (subjectMask g) z) α

theorem SAP.P032.T5 : SAP.P032.T5Statement := by
  exact ⟨fun h => printed_population_claim_false.1 (populationReading_toAudit h),
    fun h => printed_population_claim_false.2 (strictReading_toAudit h),
    fun h => printed_expectation_claim_false (expectationReading_toAudit h),
    fun h => printed_ratio_limit_claim_false (limitReading_toAudit h)⟩

theorem SAP.P032.T6 : SAP.P032.T6Statement := by
  exact ⟨ten_ols_certificate, ten_variance_certificate, ten_meat_decomposition,
    ten_variance_hermitian, positive_diagonal_counterexample⟩

theorem SAP.P032.T7 {P : Type*} [Fintype P] [DecidableEq P] : SAP.P032.T7Statement P := by
  refine ⟨?_, ?_, psd_two_by_two_iff, positive_diagonal_counterexample.1,
    positive_diagonal_counterexample.2.2.2.1, ?_, positive_diagonal_counterexample.2.1, ?_⟩
  · intro Q eigs ho ho'
    have hp := spectral_clip_psd Q eigs
    refine ⟨?_, hp, spectral_clip_quadratic Q eigs, ?_, spectral_clip_fixed_iff Q eigs ho ho'⟩
    · change (spectralClip Q eigs).transpose = spectralClip Q eigs
      simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hp.1
    · intro c
      change 0 ≤ quadratic (spectralClip Q eigs) c
      simpa only [star_trivial, quadratic_eq_dot] using hp.dotProduct_mulVec_nonneg c
  · intro V hV
    exact ⟨positive_part_psd V hV, positive_part_fixed_iff V hV, gated_psd_iff V hV⟩
  · change AronowAudit.P032.tenVariance.trace = _
    norm_num [Matrix.trace, Fin.sum_univ_succ, ten_variance_certificate.2.2,
      Matrix.smul_apply, smul_eq_mul]
  · exact ⟨ten_variance_hermitian, ten_eigenvalues_identified ten_variance_hermitian,
      ten_positive_part_rank_one ten_variance_hermitian⟩

theorem SAP.P032.T8 : SAP.P032.T8Statement := by
  refine ⟨mi_completed_data_certificate, mi_between_certificate, mi_pooling_counterexample,
    mi_partition_counts, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · change miCodeTotal = 14/81+(49/52 : ℝ)*rubinBetween miFiveEstimates 0 0
    rw [mi_pooling_counterexample.2.1, mi_between_certificate.2.2]
    ring
  · change miCodeTotal-miCorrectTotal = ((49/52 : ℝ)-1)*rubinBetween miFiveEstimates 0 0
    rw [mi_pooling_counterexample.2.2.1, mi_between_certificate.2.2]
    ring
  · rcases mi_completed_data_certificate with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hA, hB⟩
    intro B
    cases B
    · have h : imputationDCR false = 2/9 := hA
      rw [h]
      norm_num
    · have h : imputationDCR true = 8/81 := hB
      rw [h]
      norm_num
  · exact max_eq_left (le_of_lt mi_pooling_counterexample.2.2.2.2.1)
  · exact max_eq_left (le_of_lt mi_pooling_counterexample.2.2.2.2.2.1)

theorem SAP.P032.T9 : SAP.P032.T9WholeStatement := SAP.P032.WH.W1.T9_whole

theorem SAP.P032.T10 : SAP.P032.T10Statement := by
  exact studyAssembly

theorem SAP.P032.T11 {R M P : Type*} [Fintype R] [Fintype M] [Fintype P]
    [DecidableEq R] [DecidableEq M] [DecidableEq P] : SAP.P032.T11Statement R M P := by
  intro d X hr hall Y
  exact headline_decomposition (fun r => toAuditDyad (d r)) X hr hall Y

theorem SAP.P032.T12 {Ω : Type*} [MeasurableSpace Ω] : SAP.P032.T12Statement Ω := by
  intro μ hμ
  refine ⟨?_, ?_⟩
  · intro Y₁ Y₂ h₁ h₂
    exact toy_variance_identity μ Y₁ Y₂ h₁ h₂
  · intro Z hZ hu a b c d
    exact ⟨toy_shared_country_covariance μ Z hZ hu a b c d, toy_sign_cases μ Z hZ hu a b c d⟩
