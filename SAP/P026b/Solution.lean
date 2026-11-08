import SAP.P026b.Defs
import SAP.P026b.Bridge
import AronowAudit.P026.P026_PaperScope
import AronowAudit.P026.P026_CompletePaper
import AronowAudit.P026.P026_LogitCompletion
import AronowAudit.P026.P026_Refutations
import AronowAudit.P026.Wave1.Gap.FidP026
import SAP.P026b.WH.W1.Proofs.T21

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026b
open Finset Bridge
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem T13 : T13Statement := by
  intro I _ _ _ E y1 y0 f
  constructor
  · intro a
    have h := AronowAudit.P026.PaperScope.generalized_total_bias_T13
      (toUnit E) a y1 y0 _ _ (encodePrediction f)
    rw [encoded_values] at h
    exact h
  · have h := AronowAudit.P026.PaperScope.generalized_bias_T13
      (toUnit E) y1 y0 _ _ (encodePrediction f)
    rw [encoded_values] at h
    exact h

theorem T14 : T14Statement := by
  have h : logitCoreFacts := AronowAudit.P026.logit_table_corrected
  exact ⟨h, AronowAudit.P026.LogitCompletion.logitCoefficients_maximizer,
    AronowAudit.P026.logit_no_separation, logit_column_glue h⟩

theorem T15 : T15Statement := by
  have h : packageFacts := AronowAudit.P026.package_counterexample
  rcases h with ⟨hD, hp, hm, _, _, hest, hcov, hmean, hate, hht, hne⟩
  refine ⟨hD, hp, hm, ?_, ?_, hest, hcov, hmean, hate, ?_, by norm_num, hht, hne⟩
  · intro w i
    fin_cases w <;> fin_cases i <;> norm_num [packageFit]
  · intro w
    have hs := AronowAudit.P026.Wave1.olsFitted_spec 2
      (designWithIntercept 1 (fun (i : Fin 3) (_ : Fin 1) => (i.val : ℝ)))
      (fun i => ((observed oneOfThree (fun _ => 1) (fun _ => 0) w i : ℚ) : ℝ))
    rw [olsFitted_eq, package_fit_eq_projection w] at hs
    exact hs
  · rw [hmean, hate]
    norm_num

theorem T16 : T16Statement := by
  refine ⟨?_, ?_, ?_, ?_, T15⟩
  · intro I _ _ _ E y1 y0 g
    exact ⟨observed_residual E y1 y0 (fun _ => g),
      AronowAudit.P026.PaperScope.fixed_prediction_unbiased_T16 (toUnit E) y1 y0 g⟩
  · intro I _ _ _ E K X y1 y0
    exact AronowAudit.P026.Wave1.all_unit_OLS_bias_T16_rank_unrestricted (toUnit E) K X y1 y0
  · intro I _ _ _ E y1 y0 f hf
    have h := AronowAudit.P026.PaperScope.generalized_unbiased_T16
      (toUnit E) y1 y0 _ _ (encodePrediction f)
    rw [encoded_values] at h
    exact (h hf).2.2
  · intro I _ _ _ E x G
    exact AronowAudit.P026.PaperScope.sharp_null_fit_unbiased_T16 (toUnit E) x G

theorem T17 : T17Statement := by
  refine ⟨?_, AronowAudit.P026.Refutations.printed_sharp_null_footnote_refuted⟩
  intro h
  apply AronowAudit.P026.Refutations.printed_cluster_claims_refuted
  intro D hD hp hd x z
  exact h (fromDesign D) hD hp hd x z

theorem T18 : T18Statement := by
  exact AronowAudit.P026.Refutations.printed_pairwise_fitting_refuted

theorem T19 : T19Statement := by
  have h : logitCoreFacts := AronowAudit.P026.logit_table_corrected
  exact ⟨fun w => (AronowAudit.P026.fe_normal_equations w).1, h.1, h.2.1,
    AronowAudit.P026.Refutations.printed_table_columns_refuted⟩

theorem T20 : T20Statement := by
  intro I _ _ _ E y1 y0
  refine ⟨?_, AronowAudit.P026.PaperScope.ht_unbiased_T20 (toUnit E) y1 y0⟩
  intro a w
  apply Finset.sum_congr rfl
  intro i _
  cases a
  · exact congrArg (fun v : ℝ => v/marginal E.design false i)
      (AronowAudit.P026.observed_mask (toDesign E.design) false y1 y0 w i).symm
  · exact congrArg (fun v : ℝ => v/marginal E.design true i)
      (AronowAudit.P026.observed_mask (toDesign E.design) true y1 y0 w i).symm

theorem T21 : SAP.P026b.T21WholeStatement := SAP.P026b.WH.W1.T21_whole

theorem T22 : T22Statement := by
  intro I _ _ _ E y1 y0 f
  refine ⟨?_, ?_, ?_⟩
  · have h := AronowAudit.P026.PaperScope.generalized_unbiased_T22
      (toUnit E) y1 y0 _ _ (encodePrediction f)
    rw [encoded_values] at h
    exact h
  · intro g
    have hp : AronowAudit.P026.probabilityDesign (toDesign E.design) :=
      ⟨E.nonnegative, E.normalized⟩
    have hz : ∀ i, covariance E.design (fun w => indicator E.design true w i) (fun _ => g i) = 0 :=
      fun i => AronowAudit.P026.covariance_const_right (toDesign E.design) hp _ (g i)
    have hg := AronowAudit.P026.generalized_unbiased (toDesign E.design) hp E.positive
      (Fintype.card I) Fintype.card_pos y1 y0 (fun _ => g) hz
    exact ⟨hz, hg.1, hg.2.1,
      AronowAudit.P026.PaperScope.fixed_prediction_unbiased_T22 (toUnit E) y1 y0 g⟩
  · intro w
    have h := AronowAudit.P026.PaperScope.generalized_adjustment_T22
      (toUnit E) y1 y0 _ _ (encodePrediction f) w
    rw [encoded_values] at h
    exact h

theorem T23 : T23Statement := by
  refine ⟨?_, ?_⟩
  · intro I _ _ _ E x z f b0 b1 w
    refine ⟨AronowAudit.P026.PaperScope.ht_affine_T23 (toUnit E) x z b0 b1 w,
      AronowAudit.P026.PaperScope.ht_affine_invariant_iff_T23 (toUnit E) x z b0 b1 w, ?_⟩
    have h := AronowAudit.P026.PaperScope.generalized_affine_T23
      (toUnit E) x z _ _ (encodePrediction f) b0 b1 w
    rw [encoded_values] at h
    exact h
  · rcases AronowAudit.P026.ht_location_counterexample with ⟨hD, hp, h1, h0, hne⟩
    exact ⟨hD, hp, by norm_num [singleAsymmetric, asymmetricTwo], h1, h0, hne⟩

theorem T24 : T24Statement := by
  constructor
  · intro I _ _ _ E x z f
    constructor
    · intro w
      have h := AronowAudit.P026.PaperScope.generalized_residual_T24
        (toUnit E) x z _ _ (encodePrediction f) w
      rw [encoded_values] at h
      exact ⟨h, observed_residual E x z f w⟩
    · intro r
      exact AronowAudit.P026.PaperScope.unit_generalized_fixed_variance_T24 (toUnit E) x z r
  · intro U C _ _ _ _ _ _ E hs x z
    refine ⟨?_, AronowAudit.P026.PaperScope.ht_covariance_full_T24
      (toCluster E) hs true false x z,
      AronowAudit.P026.PaperScope.ht_covariance_split_T24 (toCluster E) hs x z,
      AronowAudit.P026.PaperScope.ht_cluster_covariance_T24 (toCluster E) hs x z⟩
    intro a
    cases a
    · exact AronowAudit.P026.PaperScope.ht_arm_variance_T24 (toCluster E) hs false z
    · exact AronowAudit.P026.PaperScope.ht_arm_variance_T24 (toCluster E) hs true x

end
end SAP.P026b
