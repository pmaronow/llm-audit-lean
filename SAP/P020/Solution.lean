import SAP.P020.Defs
import SAP.P020.Bridge
import AronowAudit.P020.P020_Design
import AronowAudit.P020.P020_Logistic
import SAP.P020.WH.W1.Proofs.T5
import SAP.P020.WH.W1.Proofs.T14
import SAP.P020.WH.W1.Proofs.T17
import SAP.P020.WH.W2.Proofs.T3
import SAP.P020.WH.W3.Proofs.T13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P020
open scoped BigOperators
open Filter Bridge
noncomputable section

theorem T1 : T1Statement := by
  refine ⟨AronowAudit.P020.efficiency_individual_realization,
    AronowAudit.P020.efficiency_exact_values, ?_,
    AronowAudit.P020.efficiency_optimal_coefficient,
    AronowAudit.P020.efficiency_error_probability,
    ?_,
    AronowAudit.P020.efficiency_sample_size_grows,
    AronowAudit.P020.efficiency_inconsistent,
    fun h => AronowAudit.P020.efficiency_inconsistent
      ((withinReplication_consistency_iff efficiencyPopulation).mp h), ?_, ?_⟩
  · intro k
    have h := AronowAudit.P020.efficiency_raj_mse k
    refine ⟨h, ?_, AronowAudit.P020.efficiency_mse_counterexample k⟩
    change (3 : ℝ) / 686 ≤ AronowAudit.P020.meanSquaredError
      (AronowAudit.P020.clusterLaw AronowAudit.P020.efficiencyPopulation)
      (AronowAudit.P020.desRaj AronowAudit.P020.efficiencyPopulation k)
      (AronowAudit.P020.averageTreatmentEffect AronowAudit.P020.efficiencyPopulation)
    rw [h.2.2.2.2.2.1]
    nlinarith [sq_nonneg (k - 2 / 21)]
  · intro h hh k
    have hr := AronowAudit.P020.efficiency_all_replications_counterexample h hh k
    exact ⟨hr.1, hr.2.1, fun s _ => hr.2.2.1 s,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩
  · have hb : designBias (clusterLaw efficiencyPopulation) (differenceInMeans efficiencyPopulation)
        (averageTreatmentEffect efficiencyPopulation) = -(1 : ℝ) / 315 :=
      AronowAudit.P020.efficiency_exact_values.2.2.2.2.2.2.2.2.2.1
    rw [hb]
    norm_num
  · have hd : meanSquaredError (clusterLaw efficiencyPopulation) (differenceInMeans efficiencyPopulation)
        (averageTreatmentEffect efficiencyPopulation) = (131 : ℝ) / 33075 :=
      AronowAudit.P020.efficiency_exact_values.2.2.2.2.2.2.2.2.2.2.1
    have ht : meanSquaredError (clusterLaw efficiencyPopulation) (horvitzThompson efficiencyPopulation)
        (averageTreatmentEffect efficiencyPopulation) = (1 : ℝ) / 98 :=
      AronowAudit.P020.efficiency_exact_values.2.2.2.2.2.2.2.2.2.2.2.2
    rw [hd, ht]
    norm_num

theorem T2 : T2Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, AronowAudit.P020.efficiency_sample_size_grows⟩
  · intro Ω L T d
    exact ⟨AronowAudit.P020.mse_bias_variance (toLaw L) T d,
      AronowAudit.P020.squared_bias_le_mse (toLaw L) T d⟩
  · intro Ω L T U d b hb hBias hMSE
    exact AronowAudit.P020.eventual_mse_inferiority (fun h => toLaw (L h)) T U d b hb hBias hMSE
  · intro Ω L T d ε hε
    exact AronowAudit.P020.mse_markov_bound (toLaw L) T d ε hε
  · intro Ω L U d hMSE
    exact AronowAudit.P020.vanishing_mse_consistent (fun h => toLaw (L h)) U d hMSE
  · intro h hh
    have hr := AronowAudit.P020.efficiency_all_replications_counterexample h hh 0
    exact ⟨hr.2.2.2.1, hr.2.2.2.2.2⟩

theorem T3 : SAP.P020.T3WholeStatement_W2 :=
  SAP.P020.WH.W2.T3_whole

theorem T4 : T4Statement := by
  exact ⟨AronowAudit.P020.repaired_scale_equivalence, AronowAudit.P020.repaired_real_sign,
    AronowAudit.P020.repaired_integer_sign, AronowAudit.P020.repaired_probability_sign,
    AronowAudit.P020.repaired_average_sign⟩

theorem T5 : SAP.P020.T5WholeStatement :=
  SAP.P020.WH.W1.T5_whole

theorem T6 : T6Statement := by
  refine ⟨AronowAudit.P020.estimated_slope_counterexample, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [populationSize, slopePopulation, Fin.sum_univ_succ]
  · norm_num [clusterVariance, clusterMean, slopePopulation, Fin.sum_univ_succ]
  · norm_num [armMeanSize, armSize, armSum, slopePopulation]
  · norm_num [armMeanSize, armSize, armSum, controls, controlCount,
      slopePopulation, Fin.sum_univ_succ, AronowAudit.P020.univ_three]
  · have h := AronowAudit.P020.estimated_slope_counterexample
    have hb : designBias (clusterLaw slopePopulation)
        (fun s => desRaj slopePopulation (observedSlope slopePopulation s) s)
        (averageTreatmentEffect slopePopulation) = -3 / 8 := h.2.2.2.2.2.2.2.2.2.1
    have ht : designCovariance (clusterLaw slopePopulation) (observedSlope slopePopulation)
        (armMeanSize slopePopulation true) = 1 / 2 := h.2.2.2.2.2.2.2.2.2.2.1
    have hc : designCovariance (clusterLaw slopePopulation) (observedSlope slopePopulation)
        (armMeanSize slopePopulation false) = -1 / 4 := h.2.2.2.2.2.2.2.2.2.2.2
    rw [hb, ht, hc]
    norm_num [populationSize, slopePopulation, Fin.sum_univ_succ]

theorem T7 : T7Statement := by
  refine ⟨AronowAudit.P020.affine_cluster_total, ?_, ?_, ?_⟩
  · intro P a b0 b1 k j
    exact AronowAudit.P020.raj_potential_affine (toPopulation P) a b0 b1 k j
  · intro P b0 b1 k s hs
    exact AronowAudit.P020.des_raj_affine_invariant (toPopulation P) b0 b1 k s hs
  · intro P b0 b1 k s hs
    exact AronowAudit.P020.corrected_affine_chain (toPopulation P) b0 b1 k s hs

theorem T8 : T8Statement := by
  refine ⟨AronowAudit.P020.differenced_mean, AronowAudit.P020.differenced_variance, ?_⟩
  intro M hM v w size k
  dsimp only
  have hc : clusterCovariance (differenced v size k) (differenced w size k) =
      clusterMean (fun j => (v j - k * (size j - clusterMean size)) *
        (w j - k * (size j - clusterMean size))) - clusterMean v * clusterMean w ∧
      clusterCovariance (differenced v size k) (differenced w size k) =
        clusterCovariance v w - k * clusterCovariance v size -
          k * clusterCovariance w size + k^2 * clusterVariance size :=
    AronowAudit.P020.differenced_covariance hM v w size k
  have hz : clusterMean (fun j => size j - clusterMean size) = 0 :=
    AronowAudit.P020.centered_mean_zero hM size
  refine ⟨AronowAudit.P020.clusterCovariance_product hM _ _, hc.1, ?_, ?_, ?_, ?_, hc.2⟩
  · convert hc.1 using 2
    apply congrArg (@clusterMean M)
    funext j
    ring
  · have he (j : Fin M) :
        (v j - k * (size j - clusterMean size)) * (w j - k * (size j - clusterMean size)) =
        v j * w j - v j * k * (size j - clusterMean size) -
          w j * k * (size j - clusterMean size) + k^2 * (size j - clusterMean size)^2 := by ring
    have h := hc.1
    have hadd (f g : Fin M → ℝ) : clusterMean (fun j => f j + g j) = clusterMean f + clusterMean g :=
      AronowAudit.P020.clusterMean_add f g
    have hsub (f g : Fin M → ℝ) : clusterMean (fun j => f j - g j) = clusterMean f - clusterMean g :=
      AronowAudit.P020.clusterMean_sub f g
    simp_rw [he, hadd, hsub] at h
    linarith [h]
  · simpa only [hz, mul_zero, add_zero] using hc.2
  · simpa only [mul_zero, add_zero] using hc.2

theorem T9 : T9Statement := by
  refine ⟨AronowAudit.P020.control_subscript_counterexample,
    AronowAudit.P020.bracket_admissible_counterexample,
    AronowAudit.P020.expectation_bracket_counterexample, ?_⟩
  have h : desRaj (affinePopulation subscriptPopulation 0 1) 0 {0} = (2 : ℝ) / 3 :=
    AronowAudit.P020.control_subscript_counterexample.2.1
  have hi : desRaj (affinePopulation subscriptPopulation 0 1) (0 + 1 * (0 : ℝ)) {0} =
      1 * desRaj subscriptPopulation 0 {0} :=
    (AronowAudit.P020.des_raj_affine_invariant (toPopulation subscriptPopulation) 0 1 0
      ({0} : Finset (Fin 2)) AronowAudit.P020.control_subscript_counterexample.1).2
  simp only [mul_zero, zero_add, one_mul] at hi
  rw [hi] at h
  exact h

theorem T10 : T10Statement := by
  constructor
  · intro P I hnull s hs
    exact AronowAudit.P020.individual_sharp_null_facts (toPopulation P) (toIndividuals I) hnull s hs
  · intro P I hnull s hs
    exact AronowAudit.P020.sharp_null_exact_variance (toPopulation P) (toIndividuals I) hnull s hs

theorem T11 : T11Statement := by
  constructor
  · intro Ω L u v hv
    exact AronowAudit.P020.ratio_expectation_identity (toLaw L) u v hv
  · intro P
    exact AronowAudit.P020.difference_in_means_bias (toPopulation P)

theorem T12 : T12Statement := by
  refine ⟨AronowAudit.P020.affine_cluster_total, ?_, ?_, ?_, ?_⟩
  · intro P
    exact AronowAudit.P020.ht_unbiased (toPopulation P)
  · intro P b0 b1 s hs
    exact AronowAudit.P020.ht_affine_identity (toPopulation P) b0 b1 s hs
  · intro P b0 b1 s hs hb0 hsizes
    exact AronowAudit.P020.ht_not_location_invariant (toPopulation P) b0 b1 s hs hb0 hsizes
  · refine ⟨subscriptPopulation, 1, 1, {0}, ?_, ?_⟩
    · exact AronowAudit.P020.control_subscript_counterexample.1
    · have hsizes : armMeanSize subscriptPopulation true ({0} : Finset (Fin 2)) ≠
          armMeanSize subscriptPopulation false ({0} : Finset (Fin 2)) := by
        norm_num [armMeanSize, armSize, armSum, controls, controlCount,
          subscriptPopulation, Fin.sum_univ_succ, Finset.univ_fin2]
      exact AronowAudit.P020.ht_not_location_invariant (toPopulation subscriptPopulation) 1 1
        ({0} : Finset (Fin 2)) AronowAudit.P020.control_subscript_counterexample.1
        (by norm_num) hsizes

theorem T13 : SAP.P020.T13WholeStatement_W3 :=
  SAP.P020.WH.W3.T13_whole

theorem T14 : SAP.P020.T14WholeStatement :=
  SAP.P020.WH.W1.T14_whole

theorem T15 : T15Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P
    exact AronowAudit.P020.ht_variance_components (toPopulation P)
  · intro P
    exact AronowAudit.P020.ht_variance_identity_bound (toPopulation P)
  · intro P
    exact AronowAudit.P020.covariance_remainder_nonpos P.y0 P.y1
  · intro P ht hc
    exact AronowAudit.P020.combined_variance_conservative (toPopulation P) ht hc
  · intro P k ht hc
    exact AronowAudit.P020.raj_variance_conservative (toPopulation P) k ht hc
  · intro B hB P
    exact AronowAudit.P020.independent_blocks_unbiased_variance hB (fun b => toPopulation (P b))
  · intro B hB P Vhat hVhat
    exact AronowAudit.P020.independent_blocks_variance_estimator_conservative hB
      (fun b => toPopulation (P b)) Vhat hVhat

theorem T16 : T16Statement := by
  intro P hcondition
  exact AronowAudit.P020.sharp_null_variance_conservative (toPopulation P) hcondition

set_option maxHeartbeats 800000 in
theorem T17 : SAP.P020.T17WholeStatement :=
  SAP.P020.WH.W1.T17_whole

end
end SAP.P020
