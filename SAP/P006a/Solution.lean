import SAP.P006a.WH.W2.Proofs.T8
import SAP.P006a.WH.W1.Proofs.T2
import SAP.P006a.WH.W1.Proofs.T3
import SAP.P006a.WH.W1.Proofs.T12
import SAP.P006a.WH.W1.Proofs.T14
import SAP.P006a.Defs
import SAP.P006a.Bridge
import AronowAudit.P006.P006_CounterfactualMetrics
import AronowAudit.P006.Wave1.Gap.FidP006
import AronowAudit.P006.Wave1.Gap.GP006B1
import AronowAudit.P006.Wave1.Gap.GP006B2b
import AronowAudit.P006.Wave1.Gap.RepairT6T7
import AronowAudit.P006.Wave1.Gap.DecideF
import AronowAudit.P006.Wave1.Gap.Fid2P006

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace SAP.P006a

theorem T1 : T1Statement := by
  unfold T1Statement
  simp only [Bridge.witnessReward_eq, Bridge.witnessWelfare_eq]
  refine ⟨AronowAudit.P006.T1_average_counterexample, ?_,
    AronowAudit.P006.T1_conditional_mean_mismatch, ?_, ?_, ?_⟩
  · intro π _
    have hf : rewardE001 π = (9*π.1+10*π.2)*(4-π.1-π.2)/40 :=
      AronowAudit.P006.rewardE001_formula π
    refine ⟨Bridge.averageWitness π, hf, ?_, ?_⟩
    · rw [hf]; ring
    · simp only [binaryWelfare, effectE001, Bool.false_eq_true, ite_false, ite_true]
      ring
  all_goals norm_num [binaryWelfare, effectE001]

theorem T2 : SAP.P006a.T2WholeStatement := SAP.P006a.WH.W1.T2_whole

theorem T3 : SAP.P006a.T3WholeStatement := SAP.P006a.WH.W1.T3_whole

theorem T4 : T4Statement := by
  have h := AronowAudit.P006.T4_unbiasedness_counterexamples
  refine ⟨h, fun π _ => AronowAudit.P006.witnesses_AB_formula π,
    AronowAudit.P006.T4_zero_heterogeneity_bound_failure, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro π _
    exact ⟨Bridge.singletonATT _ _ _, Bridge.singletonATT _ _ _⟩
  · norm_num [treatedEstimatorMean, binaryRule, estA, Fintype.sum_bool]
  · norm_num [treatedEstimatorMean, binaryRule, estB, estA, Fintype.sum_bool]
  · intro π hπ
    have hf : rewardA π = -(π.1+π.2)/4 ∧ welfareA π = (π.1+π.2)/4 ∧
        rewardB π = (π.1+π.2)/4 ∧ welfareB π = -(π.1+π.2)/4 :=
      AronowAudit.P006.witnesses_AB_formula π
    change binaryFeasible π at hπ
    constructor
    · intro he
      have hsum : π.1+π.2 = 0 := by linarith [hf.1, hf.2.1]
      apply Prod.ext <;> dsimp <;> linarith [hπ.1, hπ.2.2.1]
    · intro he; subst π; rw [hf.1, hf.2.1]; norm_num
  · have hv := AronowAudit.P006.bestValue_eq h.2.2.2.2.1
    change bestValue binaryPolicies welfareA = welfareA (1,1) at hv
    rw [hv]; norm_num [welfareA, binaryWelfare]
  · norm_num [welfareB, binaryWelfare]

theorem T5 : T5Statement := by
  refine ⟨AronowAudit.P006.T5_ranking_counterexample,
    fun π _ => AronowAudit.P006.ranking_witness_formula π, ?_, ?_⟩ <;> norm_num

theorem T6 : T6Statement := by
  constructor
  · intro Ω C _ _ n E P hP hD hR hU
    exact AronowAudit.P006.Wave1.T6_corrected_TT_minimal_integrability
      (Bridge.experiment E) P hP (fun π hp => Bridge.policyDesign (hD π hp)) hR hU
  · intro Ω C _ _ n E P hD hR hU hI
    exact AronowAudit.P006.Wave1.T6_independent_estimation_minimal_integrability
      (Bridge.experiment E) P (fun π hp => Bridge.policyDesign (hD π hp)) hR hU hI

theorem T7 : T7Statement := by
  intro Ω C _ _ n E hD g hg hpos hR hU hprod hreward
  exact AronowAudit.P006.Wave1.T7_corrected_weighted_alignment_treated_integrability
    (Bridge.experiment E) (Bridge.standing hD) g hg hpos hR hU hprod hreward

theorem T8 : SAP.P006a.T8WholeStatement_W2 := SAP.P006a.WH.W2.T8_whole

theorem T9 : T9Statement := by
  refine ⟨@AronowAudit.P006.T9_denominator_identity,
    @AronowAudit.P006.T9_corrected_numeric_intervals,
    @AronowAudit.P006.T9_from_printed_table, ?_⟩
  intro vH bH vS bS hHl hHu hH hSl hSu hS
  obtain ⟨hbl,hbu,_,hcl,hcu,_⟩ :=
    AronowAudit.P006.T9_corrected_numeric_intervals vH bH vS bS hHl hHu hH hSl hSu hS
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith⟩

theorem T10 : T10Statement := by
  refine ⟨@AronowAudit.P006.T10_singleton_feasible_counterexample,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro C _ D π _ _
    exact AronowAudit.P006.oneATOExpectation_formula D π
  · intro C _ D D' π _ _ hπ hD
    exact AronowAudit.P006.oneATO_invariance D D' π hπ.1 hD
  · have h := AronowAudit.P006.T10_singleton_feasible_counterexample 1 (by norm_num)
    refine ⟨Measure.dirac ((),(1+(1 : ℝ),1)), fun _ => 1, h.1, h.2.1, ?_⟩
    norm_num
  · intro f
    exact ⟨Set.mem_singleton _, fun π hπ => by
      have he := Set.mem_singleton_iff.mp hπ; rw [he]⟩
  · intro B hB
    have h := AronowAudit.P006.T10_singleton_feasible_counterexample B hB
    have hr := h.2.2.2.2.1
    change bestValue {fun _ : Unit => (1 : ℝ)}
      (outcomeWelfare (Measure.dirac ((),(1+B,1)))) -
      outcomeWelfare (Measure.dirac ((),(1+B,1))) (fun _ => 1) = 0 at hr
    have hv : outcomeWelfare (Measure.dirac ((),(1+B,1))) (fun _ : Unit => 1) = -B :=
      h.2.2.2.1
    linarith

theorem T11 : T11Statement := by
  constructor
  · intro C _ P hP hz reward hN hI
    have h := AronowAudit.P006.T11_corrected_impossibility P hP hz reward hN hI
    refine ⟨h.1, ?_⟩
    intro D π hD hb hc B hB
    obtain ⟨hf, hl, hb', hi, hm, hr⟩ := h.2 D π hD hb hc B hB
    change (∀ q ∈ P, outcomeWelfare (shiftedOutcomeLaw D B) q =
      -B*(∫ z, q z.1 ∂D)) at hi
    have hn : ∀ q ∈ P, outcomeWelfare (shiftedOutcomeLaw D B) q ≤ 0 := by
      intro q hq
      rw [hi q hq]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
        (integral_nonneg (fun z => ((hP q hq).2 z.1).1))
    refine ⟨hf, hl, hb', hi, hm, hr, hn, ?_, ?_⟩
    · refine ⟨hz, ?_⟩
      intro q hq
      have hv0 : outcomeWelfare (shiftedOutcomeLaw D B) (fun _ => 0) = 0 := by
        simp [outcomeWelfare]
      rw [hv0]; exact hn q hq
    · intro M hM
      have ha := AronowAudit.P006.T11_unbounded_shift_arithmetic M (∫ z, π z.1 ∂D) hM hc
      have hs := h.2 D π hD hb hc ((M+1)/(∫ z, π z.1 ∂D)) ha.1
      have hr' : regret P (outcomeWelfare
          (shiftedOutcomeLaw D ((M+1)/(∫ z, π z.1 ∂D)))) π =
          ((M+1)/(∫ z, π z.1 ∂D))*(∫ z, π z.1 ∂D) := hs.2.2.2.2.2
      exact ⟨ha.1, by rw [hr']; exact ha.2⟩
  · intro B hB
    let D : OutcomeLaw Unit := Measure.dirac ((),(1+B,1))
    let P : Set (Unit → ℝ) := {fun _ => 0, fun _ => 1}
    have hd : FiniteOutcomeLaw D :=
      ⟨inferInstance, integrable_dirac (by simp), integrable_dirac (by simp)⟩
    have hr (π : Unit → ℝ) (hπ : π ∈ P) : IsBest P (fun _ => (0 : ℝ)) π :=
      ⟨hπ, fun _ _ => le_rfl⟩
    have hz : IsBest P (outcomeWelfare D) (fun _ => 0) := by
      refine ⟨by simp [P], ?_⟩
      intro π hπ
      rcases Set.mem_insert_iff.mp hπ with he | he
      · rw [he]
      · have he' := Set.mem_singleton_iff.mp he
        rw [he']; simp [outcomeWelfare, D]; linarith
    have hm : bestValue P (outcomeWelfare D) = 0 := by
      have hv := AronowAudit.P006.bestValue_eq
        (show AronowAudit.P006.IsBest P (outcomeWelfare D) (fun _ => 0) from hz)
      change bestValue P (outcomeWelfare D) = outcomeWelfare D (fun _ => 0) at hv
      simpa [outcomeWelfare] using hv
    refine ⟨hd, ?_, ?_, hr, hz, ?_, ?_⟩
    · exact ⟨D, fun _ => 1, hd, hr _ (by simp [P]), by simp [D]⟩
    · intro D1 D2 _ _ _ π _; rfl
    · rw [regret, hm]; simp [outcomeWelfare]
    · rw [regret, hm]; simp [outcomeWelfare]

theorem T12 : SAP.P006a.T12WholeStatement := SAP.P006a.WH.W1.T12_whole

theorem T13 : T13Statement := by
  intro K C _ Ω _ nk E P0 hP0 hD hmu0 hac hτ hR hU hreward
  have h := AronowAudit.P006.Wave1.T13_corrected_ranking_treated_residuals
    nk (fun k => Bridge.experiment (E k)) P0 hP0
    (fun k => Bridge.rankingDesign (hD k)) hmu0 hac hτ hR hU hreward
  refine ⟨h.1, h.2.1, ?_, h.2.2⟩
  intro j k horder
  have hk : bestValue {π | Admissible π}
      ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX)) =
      ∫ x, positivePart ((E k).τ x) ∂P0 := (h.2.1 k).2
  have hj : bestValue {π | Admissible π}
      ((E j).expectedWeightedTT (referenceWeight (nk j) P0 (E j).PX)) =
      ∫ x, positivePart ((E j).τ x) ∂P0 := (h.2.1 j).2
  exact hk.symm.trans_le ((h.2.2.1 j k horder).trans_eq hj)

theorem T14 : SAP.P006a.T14WholeStatement := SAP.P006a.WH.W1.T14_whole

theorem T15 : T15Statement := by
  refine ⟨AronowAudit.P006.T15_untreated_positivity_counterexamples,
    @AronowAudit.P006.T15_constant_private_heterogeneity, ?_⟩
  intro record
  simp [singletonObservedMass, coinMass, Fintype.sum_bool]

end SAP.P006a
