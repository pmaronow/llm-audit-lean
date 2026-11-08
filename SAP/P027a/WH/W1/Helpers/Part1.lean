import SAP.P027a.Defs.WholeW1
import SAP.P027a.Bridge
import AronowAudit.P027.P027_Audit
import AronowAudit.P027.Wave1.Gap.GLP027P016P031B1
import AronowAudit.P027.Wave1.Gap.T2Conjunction
import AronowAudit.P027.Wave1.AePartition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a.WH.W1

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory SAP.P027a.Bridge
attribute [local instance] Classical.propDecidable

/-- Existing finite eight-unit certificate, with the data-only SAP definitions. -/
theorem periodic8_core : Periodic8Witness := by
  rcases AronowAudit.P027.periodic8_bias with ⟨hz, ha, hs⟩
  rcases AronowAudit.P027.periodic8_counterexample with ⟨he, hv, hh, hc, hb⟩
  exact ⟨valid_fromAudit AronowAudit.P027.periodic8, AronowAudit.P027.periodic8_positive,
    AronowAudit.P027.fourPhase_pi (1/12) (5/12) (by norm_num) (by norm_num) (by norm_num),
    AronowAudit.P027.fourPhase_joint (1/12) (5/12) (by norm_num) (by norm_num) (by norm_num),
    AronowAudit.P027.four_phase_zero_pair_count.1, AronowAudit.P027.periodic8_systematic,
    hz, ha, hs, AronowAudit.P027.periodic8_sample_values, he, hv, hh, hc, hb⟩

/-- Existing general continuous bridge. The incomplete raw bridge is not used. -/
theorem periodic_start_core : PeriodicStartLaw :=
  AronowAudit.P027.Wave1.periodic_correction_values_with_uniform_start.1

/-- Existing finite bias formulas; the last identity is elementary subtraction. -/
theorem periodic_bias_core : PeriodicBiasClaim := by
  intro r m hr hm z hz
  rcases AronowAudit.P027.periodic_finite_correction r m hr hm z hz with
    ⟨hY, hA, hS, hzero, hE, hV, hH, hUc, hGc, hsample,
      hdiff, hvG, hGU, hlo, hhi, hbounds⟩
  refine ⟨hY, hA, hS, hzero, hE, hV, hH,
    fun g => (hsample g).2.1, ?_, fun hv => ⟨(hbounds hv).1, (hbounds hv).2.1⟩⟩
  have hh : expect (phaseOriginal r m hr) (htVarianceEstimator (phaseOriginal r m hr) z) =
      variance (phaseOriginal r m hr) (htTotal (phaseOriginal r m hr) z) -
        ∑ g, groupTotal (fun _ : Fin r × Fin 2 => m) z g^2 := hH
  rw [hh]
  ring

/-- The outcome moment theorem already needs only the claimed error moments. -/
theorem periodic_outcome_core : PeriodicOutcomeWhole := by
  intro Ξ _ μ _ r m hr hm β σ2 hσ ε hε
  dsimp only
  rcases AronowAudit.P027.periodic_model_moments μ r m hr hm β σ2 hσ ε hε with
    ⟨hY, hA, hV, hH, hQ, hUc, hGc, hratios, hbias, hWR⟩
  exact ⟨fun g => ⟨(AronowAudit.P027.phase_centered_second_moment μ r m hr hm β σ2 ε hε g).1,
    hY g⟩, hA, hV, hH, hbias, fun hM => (hratios hM).1⟩

/-- Size moments and the printed PPS formula. Positivity follows from r,m>0. -/
theorem periodic_sizes : PeriodicSizesWhole := by
  intro r m hr hm
  dsimp only
  have hs := AronowAudit.P027.periodic_size_moments r m hr hm
  have hsum : (∑ k : (Σ _ : Fin r × Fin 2, Fin m), phaseSize k) =
      6*((m:ℝ)*(2*r)) := hs.1
  have hmR : (m:ℝ) ≠ 0 := by positivity
  have hrR : (r:ℝ) ≠ 0 := by positivity
  refine ⟨hsum, ?_, hs.2.1, hs.2.2, ?_⟩
  · rw [hsum]
    field_simp
  · intro k
    rw [(periodic_inclusions r m hr).2.2.1 k, hsum]
    dsimp [phaseProb, phaseSize]
    split_ifs
    all_goals field_simp
    all_goals ring

/-- Existing two finite aggregation witnesses, including their biases. -/
theorem cluster_core : T3Statement := by
  refine ⟨⟨AronowAudit.P027.aggregation_counterexample_positive,
    AronowAudit.P027.aggregation_counterexample_mixed⟩, ?_⟩
  have hpos : (Positive cluster3 ∧ Positive cluster2 ∧
      (∀ g, indicator cluster3 g 0 = indicator cluster3 g 1) ∧
      (∀ g, htTotal cluster3 allOnes3 g = htTotal cluster2 totalledOnes g) ∧
      variance cluster3 (htTotal cluster3 allOnes3) = 1 ∧
      biasA cluster3 allOnes3 = 4 ∧ quadraticA cluster3 allOnes3 = 4 ∧
      quadraticA cluster2 totalledOnes = 5 ∧
      expect cluster3 (c2Estimator cluster3 allOnes3) = 9 ∧
      expect cluster2 (c2Estimator cluster2 totalledOnes) = 10) :=
    AronowAudit.P027.aggregation_counterexample_positive
  rcases hpos with ⟨_, _, _, ht, hv, _, _, _, hu, hc⟩
  have hv2 : variance cluster2 (htTotal cluster2 totalledOnes) = 1 := by
    change variance cluster3 (htTotal cluster2 totalledOnes) = 1
    rw [← funext ht]
    exact hv
  have hm : variance cluster3 (htTotal cluster3 mixed3) = 81/16 ∧
      variance cluster2 (htTotal cluster2 totalledMixed) = 81/16 ∧
      biasA cluster3 mixed3 = -1 ∧ biasA cluster2 totalledMixed = -1 ∧
      quadraticA cluster3 mixed3 = 17/8 ∧ quadraticA cluster2 totalledMixed = 65/16 ∧
      expect cluster3 (c2Estimator cluster3 mixed3) = 99/16 ∧
      expect cluster2 (c2Estimator cluster2 totalledMixed) = 65/8 :=
    AronowAudit.P027.aggregation_counterexample_mixed
  rcases hm with ⟨hvm, hvcm, _, _, _, _, hum, hcm⟩
  dsimp only [ClusterBiasIncrease]
  rw [hv2, hv, hu, hc, hvm, hvcm, hum, hcm]
  norm_num

/-- Existing complete deterministic random-size witness. -/
theorem random8_core : Random8Witness := by
  exact ⟨valid_fromAudit AronowAudit.P027.random8, AronowAudit.P027.random8_positive,
    AronowAudit.P027.random8_counterexample, AronowAudit.P027.random8_mean_counterexample,
    AronowAudit.P027.random8_sample_values, AronowAudit.P027.random8_systematic,
    AronowAudit.P027.negative_bias_neighborhood⟩

/-- The normalized negative-binomial product gives the size vector positive mass. -/
theorem random_size_support : RandomSizeSupportWhole := by
  have hp : IsProbabilityMeasure nbProductLaw :=
    AronowAudit.P027.Wave1.all_pps_product_probability 8
  have he : (nbProductLaw {wholeRandomSizeAtom}).toReal =
      ∏ k, nbMass (wholeRandomSizeAtom k) :=
    AronowAudit.P027.Wave1.all_pps_product_singleton_real 8 wholeRandomSizeAtom
  refine ⟨hp, ?_, ?_, ?_⟩
  · intro k
    fin_cases k <;> norm_num [wholeRandomSizeAtom, randomSize8]
  · rw [he]
    norm_num [wholeRandomSizeAtom, Fin.prod_univ_succ]
    ring
  · rw [he]
    exact Finset.prod_pos (fun k _ => AronowAudit.P027.Wave1.all_pps_nbMass_pos _)

/-- Finite arithmetic supplement to the periodic witness. -/
theorem periodic8_details : Periodic8WholeDetails := by
  have hp (k : Fin 8) : pi periodic8 k = if k.val % 2 = 0 then 1/12 else 5/12 :=
    AronowAudit.P027.fourPhase_pi _ _ (by norm_num) (by norm_num) (by norm_num) k
  have hc := AronowAudit.P027.periodic8_counterexample
  have ha : biasA periodic8 alternating8 = -16 := AronowAudit.P027.periodic8_bias.2.1
  have hvscale : variance periodic8 (htMean periodic8 alternating8) =
      variance periodic8 (htTotal periodic8 alternating8)/64 := by
    have hs : variance periodic8 (fun ω => htTotal periodic8 alternating8 ω/8) =
        variance periodic8 (htTotal periodic8 alternating8)/8^2 :=
      AronowAudit.P027.variance_div_const AronowAudit.P027.periodic8
        (AronowAudit.P027.htTotal AronowAudit.P027.periodic8 AronowAudit.P027.alternating8) 8
    norm_num only [show (8:ℝ)^2 = 64 by norm_num] at hs
    exact hs
  have hv : variance periodic8 (htTotal periodic8 alternating8) = 576/5 := by
    have hc' : variance periodic8 (htMean periodic8 alternating8) = 9/5 := hc.2.1
    rw [hvscale] at hc'
    linarith
  have hhscale : expect periodic8 (fun g => htVarianceEstimator periodic8 alternating8 g/64) =
      expect periodic8 (htVarianceEstimator periodic8 alternating8)/64 :=
    AronowAudit.P027.expect_div_const AronowAudit.P027.periodic8 _ 64
  have hh : expect periodic8 (htVarianceEstimator periodic8 alternating8) = 496/5 := by
    have hc' : expect periodic8 (fun g => htVarianceEstimator periodic8 alternating8 g/64) = 31/20 :=
      hc.2.2.1
    rw [hhscale] at hc'
    linarith
  have hs : (∑ k, periodicSize8 k) = 48 := by
    norm_num [periodicSize8, Fin.sum_univ_succ]
  have htot (g : Fin 4) : htTotal periodic8 alternating8 g =
      if g.val % 2 = 0 then -24 else 24/5 := by
    have h : htMean periodic8 alternating8 g = if g.val % 2 = 0 then -3 else 3/5 :=
      (AronowAudit.P027.periodic8_sample_values g).1
    change htTotal periodic8 alternating8 g/8 = _ at h
    split_ifs at h ⊢ <;> linarith
  refine ⟨hs, ?_, ?_, ?_, ?_, ?_, hv, hh, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    fin_cases k <;> norm_num [cumulativeLeft, periodicSize8, Fin.sum_univ_succ]
  · intro k
    rw [hp, printedPPS, hs]
    fin_cases k <;> norm_num [periodicSize8]
  · intro k
    fin_cases k <;> norm_num [alternating8, periodicSize8, Fin.sum_univ_succ]
  · intro g
    fin_cases g <;> norm_num [periodic8, fourPhase, alternating8, Fin.sum_univ_succ]
  · rw [ha]
    norm_num [periodic8, fourPhase, alternating8, Fin.sum_univ_succ]
  · rw [hh, hv, ha]
    norm_num
  · have hb : expect periodic8 (fun g => htVarianceEstimator periodic8 alternating8 g/64) -
        variance periodic8 (htMean periodic8 alternating8) = -1/4 := hc.2.2.2.2
    rw [hb, ha]
    norm_num
  · have hb : expect periodic8 (fun g => htVarianceEstimator periodic8 alternating8 g/64) -
        variance periodic8 (htMean periodic8 alternating8) = -1/4 := hc.2.2.2.2
    have hvm : variance periodic8 (htMean periodic8 alternating8) = 9/5 := hc.2.1
    rw [hb, hvm]
    norm_num
  · have hvm : variance periodic8 (htMean periodic8 alternating8) = 9/5 := hc.2.1
    have hec : expect periodic8 (fun g => c2Estimator periodic8 alternating8 g/64) = 23/10 :=
      hc.2.2.2.1
    rw [hvm, hec]
    norm_num
  · intro g k hk
    rw [hp, htot]
    fin_cases g <;> fin_cases k <;>
      norm_num [periodic8, fourPhase] at hk <;> norm_num [alternating8]

/-- Probability tables and exact pair lists for the two-cluster examples. -/
theorem cluster_design_details : ClusterDesignWholeDetails := by
  have hz3 : (Finset.univ.filter (fun kl : Fin 3 × Fin 3 =>
      kl.1 ≠ kl.2 ∧ joint cluster3 kl.1 kl.2 = 0)) =
        {((0:Fin 3),2),(2,0),(1,2),(2,1)} := by
    ext ⟨k,l⟩
    fin_cases k <;> fin_cases l <;>
      norm_num [joint, expect, indicator, cluster3, Fin.sum_univ_succ]
  have hz2 : (Finset.univ.filter (fun kl : Fin 2 × Fin 2 =>
      kl.1 ≠ kl.2 ∧ joint cluster2 kl.1 kl.2 = 0)) = {((0:Fin 2),1),(1,0)} := by
    ext ⟨k,l⟩
    fin_cases k <;> fin_cases l <;>
      norm_num [joint, expect, indicator, cluster2, Fin.sum_univ_succ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hz3, hz2, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Valid, cluster3, Fin.sum_univ_succ]
  · norm_num [Valid, cluster2, Fin.sum_univ_succ]
  · intro k
    fin_cases k <;> norm_num [pi, expect, indicator, cluster3, Fin.sum_univ_succ]
  · intro k
    fin_cases k <;> norm_num [pi, expect, indicator, cluster2, Fin.sum_univ_succ]
  · intro k l
    fin_cases k <;> fin_cases l <;>
      norm_num [joint, expect, indicator, cluster3, Fin.sum_univ_succ]
  · intro k l
    fin_cases k <;> fin_cases l <;>
      norm_num [joint, expect, indicator, cluster2, Fin.sum_univ_succ]
  · intro g
    fin_cases g <;> norm_num [cluster3]
  · norm_num [expect, cluster3, Fin.sum_univ_succ]
  · rw [hz3]
    decide
  · rw [hz2]
    decide
  · intro g k
    fin_cases g <;> fin_cases k <;> norm_num [cluster3, cluster2]
  · intro k
    fin_cases k <;> norm_num [totalledOnes, allOnes3]
  · intro k
    fin_cases k <;> norm_num [totalledMixed, mixed3]

/-- All omitted entries of the positive cluster witness are finite arithmetic. -/
theorem cluster_value_details : ClusterValuesWholeDetails := by
  norm_num [ClusterValuesWholeDetails, pi, joint, expect, indicator, htTotal, biasA,
    c2Estimator, htVarianceEstimator, quadraticCorrection, inclusionCov,
    cluster3, cluster2, allOnes3, totalledOnes, Fin.sum_univ_succ, Fin.forall_fin_succ]

/-- Joint probabilities, feasibility and sign assertions for the random witness. -/
theorem random8_details : Random8WholeDetails := by
  have hp (k : Fin 8) : pi random8 k = if k.val % 2 = 0 then 1/8 else 3/8 :=
    AronowAudit.P027.fourPhase_pi _ _ (by norm_num) (by norm_num) (by norm_num) k
  have hj (k l : Fin 8) : joint random8 k l =
      if k.val % 4 = l.val % 4 then (if k.val % 2 = 0 then 1/8 else 3/8) else 0 :=
    AronowAudit.P027.fourPhase_joint _ _ (by norm_num) (by norm_num) (by norm_num) k l
  refine ⟨?_, ?_, by norm_num [randomSize8], ?_, ?_, ?_, ?_,
    AronowAudit.P027.four_phase_zero_pair_count.2, ?_, by norm_num⟩
  · intro k
    fin_cases k <;> norm_num [cumulativeLeft, randomSize8, Fin.sum_univ_succ]
  · intro k
    fin_cases k <;> norm_num [randomSize8]
  · norm_num [randomSize8, Fin.sum_univ_succ]
  · intro β k
    ring
  · intro k
    rw [hp]
    fin_cases k <;> norm_num [randomSize8]
  · intro k l
    rw [hp, hj]
  · have hv : variance random8 (htTotal random8 randomOutcome8) = 256/3 :=
      AronowAudit.P027.random8_counterexample.2.2.2.2.1
    have hc : expect random8 (c2Estimator random8 randomOutcome8) = 352/3 :=
      AronowAudit.P027.random8_counterexample.2.2.2.2.2.2
    rw [hv, hc]
    norm_num

end
end SAP.P027a.WH.W1
