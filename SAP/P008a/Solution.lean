import SAP.P008a.Defs
import SAP.P008a.Bridge
import AronowAudit.P008.P008_Audit
import SAP.P008a.WH.W1.Proofs.T9
import SAP.P008a.WH.W1.Proofs.T10
import SAP.P008a.WH.W1.Proofs.T7

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P008a SAP.P008a.Bridge MeasureTheory
open scoped BigOperators Classical

noncomputable section

theorem SAP.P008a.T1 : SAP.P008a.T1Statement := by
  refine ⟨AronowAudit.P008.observed_count_does_not_identify_law, ?_, AronowAudit.P008.six_support,
    AronowAudit.P008.blocked_support, ?_, AronowAudit.P008.reference_laws_counterexample⟩
  · intro he
    have hp := AronowAudit.P008.observed_count_does_not_identify_law.2.2.2.2.2.2.2.2.2.1
    have hz := AronowAudit.P008.observed_count_does_not_identify_law.2.2.2.2.2.2.2.2.2.2.1
    have hv := congrFun he alternative121
    exact (ne_of_gt hp) (hv.trans hz)
  · intro k
    fin_cases k <;> norm_num [contrast4, sixAssignment, bit, Fin.sum_univ_succ]

theorem SAP.P008a.T2 : SAP.P008a.T2Statement := by
  refine ⟨?_, ?_, ?_, ?_, AronowAudit.P008.reference_laws_counterexample⟩
  · intro Ω _ Q T δ hδ hδ'
    exact AronowAudit.P008.design_tail_valid (toLaw Q) T δ hδ hδ'
  · intro Ω _ Q A hA T δ hδ hδ'
    exact AronowAudit.P008.conditional_tail_valid (toLaw Q) A hA T δ hδ hδ'
  · intro N Q p hp hp' hQ M hM
    exact AronowAudit.P008.bernoulli_given_count_uniform (toLaw Q) p hp hp' hQ M hM
  · intro N P Q A hA D hf hs hN hm hfin hi ha δ hδ hδ'
    have ht := AronowAudit.P008.sharp_null_cumulative_test_valid (toModel P) (toLaw Q) A hA D
      hf hs hN hm hfin hi ha δ hδ hδ'
    exact ⟨ht.1, fun z _ _ => ht.2 z⟩

theorem SAP.P008a.T3 : SAP.P008a.T3Statement := by
  refine ⟨AronowAudit.P008.six_support, AronowAudit.P008.spatial_percentile_counterexample, ?_, ?_⟩
  · intro Q hQ
    have h := AronowAudit.P008.bernoulli_given_count_uniform (toLaw Q) (1 / 2)
      (by norm_num) (by norm_num) hQ 2 (by norm_num)
    refine ⟨h.1, ?_⟩
    intro z hz
    have hv := h.2 z hz
    convert hv using 1 <;> norm_num [show Nat.choose 4 2 = 6 by decide] <;> rfl
  · intro j k
    have hs (r : Fin 5) (w : Fin 6) : validatorRectangleStatistic r w = percentileExample w :=
      AronowAudit.P008.spatial_percentile_counterexample.2.2.2.2.2.1 r w
    simp_rw [hs]
    fin_cases k <;> norm_num [percentileExample, outside, Fin.sum_univ_succ]

theorem SAP.P008a.T4 : SAP.P008a.T4Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, AronowAudit.P008.printed_toy_sums.1⟩
  · intro y k
    have hc := AronowAudit.P008.complement_contrast y k
    have hh := AronowAudit.P008.contrast_is_hajek y k
    exact ⟨hc.1, hc.2.1, hh.1, hh.2.1, hh.2.2⟩
  · intro J a m
    dsimp only
    have hs := AronowAudit.P008.linear_functional_complement a m
    refine ⟨hs, fun k => ⟨?_, ?_⟩⟩
    · exact AronowAudit.P008.six_tail_lower_bound (fun k => ∑ j, a j * contrast4 (m j) (sixAssignment k)) hs k
    · exact (AronowAudit.P008.six_no_five_percent_rejection (fun k => ∑ j, a j * contrast4 (m j) (sixAssignment k)) hs).1 k
  · intro R hR
    have he : (uniformLaw (Fin 6)).prob (fun k => k ∈ R) = R.card / 6 := by
      simp [FiniteLaw.prob, uniformLaw, div_eq_mul_inv]
    have hcard : (1 : ℝ) ≤ R.card := by exact_mod_cast hR.card_pos
    refine ⟨he, ?_, ?_⟩
    · rw [he]; linarith
    · exact (AronowAudit.P008.six_no_five_percent_rejection (fun _ => 0) (by simp)).2 R hR
  · intro Ω _ Q T δ hδ hδ'
    exact AronowAudit.P008.design_tail_valid (toLaw Q) T δ hδ hδ'
  · intro Ω _ Q B R hIID S δ hδ hδ'
    exact AronowAudit.P008.monte_carlo_rank_valid (toLaw Q) B (toLaw R) hIID S δ hδ hδ'

theorem SAP.P008a.T5 : SAP.P008a.T5Statement := by
  refine ⟨AronowAudit.P008.pair_support, AronowAudit.P008.pair_circle_calculation,
    AronowAudit.P008.effect_range_cutoff_counterexample, AronowAudit.P008.effect_range_covariance_omission,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := AronowAudit.P008.effect_range_cutoff_counterexample
    have hs (i : Fin 2) :
        (fun k => linearizationScore pairM (5 / 4) (1 / 4) i (pairAssignment k)) =
        (fun k => (1 / 2 : ℝ) * (2 * bit (pairAssignment k 0) - 1) *
          (2 * bit (pairAssignment k 1) - 1)) := funext (h.2.1 i)
    constructor
    · intro i
      constructor
      · rw [hs i]
        norm_num [FiniteLaw.expect, uniformLaw, pairAssignment, bit, Fin.sum_univ_succ]
      · have hv : (uniformLaw (Fin 4)).var
            (fun k => linearizationScore pairM (5 / 4) (1 / 4) 0 (pairAssignment k)) = 1 / 4 := h.2.2.1
        simpa only [hs] using hv
    · simp_rw [show ∀ i, (uniformLaw (Fin 4)).expect
          (fun k => pairM i (Function.update (pairAssignment k) i true)) = 5 / 4 from fun i => (h.1 i).1,
        show ∀ i, (uniformLaw (Fin 4)).expect
          (fun k => pairM i (Function.update (pairAssignment k) i false)) = 1 / 4 from fun i => (h.1 i).2]
      norm_num
  · exact AronowAudit.P008.replicated_spatial_counterexample
  · exact AronowAudit.P008.replicated_spatial_marginals
  · exact AronowAudit.P008.replicated_plane_circle
  · exact AronowAudit.P008.replicated_plane_separation
  · exact AronowAudit.P008.replicated_circle_depends_on_pair
  · exact AronowAudit.P008.replicated_plane_cutoff_omission

theorem SAP.P008a.T6 : SAP.P008a.T6Statement := by
  refine ⟨?_, ?_, AronowAudit.P008.additive_score_covariance, ?_, ?_⟩
  · intro N z M D c hc h₁ h₀
    have hr := AronowAudit.P008.matrix_hac_reduction z M D c h₁ h₀
    refine ⟨AronowAudit.P008.hajek_weighted_contrast z M, hr.1, hr.2.1, hr.2.2, ?_⟩
    intro hd hs
    have hh := AronowAudit.P008.hac_group_hc0 z M D c hc h₁ h₀ hd hs
    exact ⟨AronowAudit.P008.hac_equals_hc0 _ D c hc hd hs, hh.1, hh.2⟩
  · intro g
    have ht := AronowAudit.P008.toy_cutoff_is_hc0 g
    have he : hac g (fun i j => dist (toyNode i) (toyNode j)) (2 / 5) =
        hac g (fun i j => dist (toyNode i) (toyNode j)) 0 :=
      ht.2.trans (AronowAudit.P008.hac_equals_hc0 g
        (fun i j => dist (AronowAudit.P008.toyNode i) (AronowAudit.P008.toyNode j)) 0 le_rfl
        (fun i => dist_self (AronowAudit.P008.toyNode i))
        (fun i j hij => lt_trans (by norm_num) (ht.1 i j hij))).symm
    exact ⟨ht.1, ht.2, he, fun t critical => by rw [he]; exact ⟨rfl, rfl⟩⟩
  · intro N hN base a m₁ m₀
    dsimp only
    let Q := AronowAudit.P008.uniformLaw (AronowAudit.P008.Assignment N)
    let φ := fun i z => AronowAudit.P008.linearizationScore
      (fun i z => base i + ∑ k, a i k * AronowAudit.P008.bit (z k)) m₁ m₀ i z
    have hv := AronowAudit.P008.variance_mul_const Q (N : ℝ)⁻¹ (fun z => ∑ i, φ i z)
    have hs := AronowAudit.P008.variance_sum_covariances Q φ
    constructor
    · have hcov (i j : Fin N) : Q.cov (φ i) (φ j) =
          if i = j then Q.var (φ i) else a i j * a j i := by
        by_cases hij : i = j
        · subst j; simp [AronowAudit.P008.FiniteLaw.var]
        · rw [ite_eq_right hij]
          exact AronowAudit.P008.additive_score_covariance base a m₁ m₀ i j hij
      have hsum : (∑ i, ∑ j, Q.cov (φ i) (φ j)) =
          (∑ i, Q.var (φ i)) + ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), a i j * a j i := by
        have hdiag (i : Fin N) : Finset.univ.filter (fun j => i = j) = {i} := by
          ext j; simp [eq_comm]
        simp_rw [hcov]
        simp [Finset.sum_ite, Finset.sum_add_distrib, hdiag]
      exact hv.trans (congrArg ((N : ℝ)⁻¹^2 * ·) (hs.trans hsum))
    · intro D c hc hd hz
      have hzero (i j : Fin N) (hfar : c < D i j) : Q.cov (φ i) (φ j) = 0 := by
        have hij : i ≠ j := by intro he; subst j; rw [hd] at hfar; linarith
        exact (AronowAudit.P008.additive_score_covariance base a m₁ m₀ i j hij).trans (hz i j hfar)
      exact (congrArg ((N : ℝ)⁻¹^2 * ·)
        (AronowAudit.P008.dependence_cutoff_identity Q φ D c hzero)).trans hv.symm
  · intro N P d r c g hf hm hfin he hcut i k hfar
    exact AronowAudit.P008.integral_far_coefficient_zero (toModel P) i k d r (g i k)
      hf (hm i) (hfin i) (he i k) (hcut.trans_lt hfar)

theorem SAP.P008a.T7 : SAP.P008a.T7WholeStatement := SAP.P008a.WH.W1.T7_whole

theorem SAP.P008a.T8 : SAP.P008a.T8Statement := by
  refine ⟨?_, AronowAudit.P008.normalized_probability_effect, ?_, AronowAudit.P008.constant_radius_effect_for_sampling,
    AronowAudit.P008.common_rescaling_for_percentiles,
    ⟨AronowAudit.P008.reported_values_divided_by_four.1, AronowAudit.P008.reported_values_divided_by_four.2.1,
      AronowAudit.P008.reported_values_divided_by_four.2.2.1, AronowAudit.P008.reported_values_divided_by_four.2.2.2,
      by norm_num⟩, ?_⟩
  · intro N P Q d hN hf hm hfin hi hb
    exact AronowAudit.P008.spatial_risk_normalization (toModel P) (toLaw Q) d hN hf hm hfin hi hb
  · intro J hJ q₀ q₁
    have hj : (J : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hJ)
    constructor
    · rw [Finset.sum_sub_distrib, sub_div]
    · exact (mul_div_cancel₀ _ hj).symm
  · exact AronowAudit.P008.binary_companion_counterexample_bernoulli.2.2.2

theorem SAP.P008a.T9 : SAP.P008a.T9WholeStatement := SAP.P008a.WH.W1.T9_whole

theorem SAP.P008a.T10 : SAP.P008a.T10WholeStatement := SAP.P008a.WH.W1.T10_whole

theorem SAP.P008a.T11 : SAP.P008a.T11Statement := by
  exact ⟨AronowAudit.P008.printed_toy_sums, AronowAudit.P008.toy_sum_rounding, by norm_num⟩

theorem SAP.P008a.T12 : SAP.P008a.T12Statement := by
  refine ⟨AronowAudit.P008.printed_grid_counterexample, by norm_num, ?_⟩
  intro n M q hq hq'
  have hz := (AronowAudit.P008.printed_grid_empty_percentiles M).1
  refine ⟨hz, ?_⟩
  simp_rw [show ∀ z, (∑ j ∈ Finset.univ.filter (fun j => inUgandaRange (printedGrid j)), M z j) = 0 from hz]
  exact AronowAudit.P008.zero_sum_quantiles q

theorem SAP.P008a.T13 : SAP.P008a.T13Statement := by
  exact ⟨AronowAudit.P008.corrected_grid, by norm_num [correctedGrid]⟩

theorem SAP.P008a.T14 : SAP.P008a.T14Statement := by
  refine ⟨?_, AronowAudit.P008.amr_misprint, AronowAudit.P008.amr_misprint_witness⟩
  intro N hN μ₁ μ₀ τ hτ
  simp_rw [hτ]

end
