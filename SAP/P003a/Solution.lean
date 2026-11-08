import SAP.P003a.Defs
import SAP.P003a.Bridge
import AronowAudit.P003.P003_Audit
import AronowAudit.P003.Wave1.Gap.GP0031B1
import AronowAudit.P003.Wave1.Gap.GLP0031B1
import AronowAudit.P003.Wave1.Gap.GLP0031B2
import AronowAudit.P003.Wave1.Gap.GP0031B2b
import SAP.P003a.WH.W1.Proofs.T21
import SAP.P003a.WH.W1.Proofs.T22
import SAP.P003a.WH.W1.Proofs.T23
import SAP.P003a.WH.W1.Proofs.T1
import SAP.P003a.WH.W1.Proofs.T4
import SAP.P003a.WH.W2.Proofs.T5
import SAP.P003a.WH.W2.Proofs.T11
import SAP.P003a.WH.W2.Proofs.T12
import SAP.P003a.WH.W2.Proofs.T14
import SAP.P003a.WH.W2.Proofs.T9
import SAP.P003a.WH.W3.Proofs.T15
import SAP.P003a.WH.W3.Proofs.T16
import SAP.P003a.WH.W3.Proofs.T17

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a
open Bridge
open scoped BigOperators

theorem T29 : T29Statement := by
  intro v m α hm hα
  have h := AronowAudit.P003.exact_coverage (toAudit v) m α hm hα
  simpa [decode_designProb, from_to, to_tau, to_observed, to_exactInterval] using h

theorem T1 : T1WholeStatement := SAP.P003a.WH.W1.T1_whole

theorem T2 : T2Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro v m α hm hn hα μ hμ
    have h := AronowAudit.P003.Wave1.balanced_missing_coverage_proof (toAudit v) m α
      hm hn hα (liftLaw μ) ((to_IsMissingLaw v m μ).mpr hμ)
    simpa [decode_missingProb, to_tau, to_observed, to_missingInterval] using h
  · intro o r α hα ho hr
    have hr' : toAudit r ∈ AronowAudit.P003.missingMasks (toAudit o) := by simpa using hr
    have h := AronowAudit.P003.Wave1.balanced_completion_inclusion_proof
      (toAudit o) (toAudit r) α hα ho hr'
    simpa [to_completionUnion, to_missingInterval] using h
  · intro n m hm hn y y' z r hz hy' w hw α hα hp ht
    have h := AronowAudit.P003.Wave1.balanced_plus_coupling_proof
      m hm hn y y' z r hz hy' w hw α hα hp ht
    simp only [to_unitObserved, to_upper, PossibleTable_eq, unitPlus_eq, coupledPlus_eq,
      to_tableTau, outcomeEstimator_eq, to_tableEstimator, unitPValue_eq] at h
    with_unfolding_all exact h

theorem T3 : T3Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v m α hm hα μ hμ
    have h := AronowAudit.P003.completion_coverage (toAudit v) m α hm hα
      (liftLaw μ) ((to_IsMissingLaw v m μ).mpr hμ)
    simpa [decode_missingProb, to_tau, to_observed, to_completionUnion,
      to_completionHull] using h
  · intro α o r _ho hr
    have hr' : toAudit r ∈ AronowAudit.P003.missingMasks (toAudit o) := by simpa using hr
    simpa [to_exactInterval, to_completionUnion] using
      AronowAudit.P003.complete_interval_subset_union α (toAudit o) (toAudit r) hr'
  · intro α o r _ho _hr
    simpa [to_completionUnion, to_completionHull] using
      AronowAudit.P003.completion_union_subset_hull α (toAudit o) (toAudit r)
  · intro o r hr
    have hr' : toAudit r ∈ AronowAudit.P003.missingMasks (toAudit o) := by simpa using hr
    have h := AronowAudit.P003.completion_finite_facts (toAudit o) (toAudit r) hr'
    simpa [to_completions, List.mem_map, to_inj, exists_eq_right,
      List.nodup_map_iff (show Function.Injective toAudit from fun _ _ h => (to_inj _ _).mp h),
      List.length_map, to_a, to_b, to_c, to_d] using h
  · exact T29
  · simpa [decode_completionHullQ, to_badHullCoverage] using
      AronowAudit.P003.repaired_hull_example

theorem T4 : T4WholeStatement := SAP.P003a.WH.W1.T4_whole

theorem T5 : T5WholeStatement := SAP.P003a.WH.W2.T5_whole

theorem T11 : T11WholeStatement := SAP.P003a.WH.W2.T11_whole

theorem T12 : T12WholeStatement := SAP.P003a.WH.W2.T12_whole

theorem T13 : T13Statement := by
  constructor
  · intro n w hn
    simpa [to_tableCounts, to_total, to_a, to_b, to_c, to_tau, to_tableTau] using
      AronowAudit.P003.corrected_sate w hn
  · simpa [decode_tauQ] using AronowAudit.P003.printed_sate_witnesses

theorem T14 : T14WholeStatement := SAP.P003a.WH.W2.T14_whole

theorem T9 : T9WholeStatement := SAP.P003a.WH.W2.T9_whole

theorem T10 : T10Statement := by
  exact ⟨AronowAudit.P003.independent_convolution_sd,
    AronowAudit.P003.independent_convolution_shape,
    AronowAudit.P003.Wave1.parity_convolution_sd_proof⟩

theorem T15 : T15WholeStatement := SAP.P003a.WH.W3.T15_whole

theorem T16 : T16WholeStatement := SAP.P003a.WH.W3.T16_whole

theorem T17 : T17WholeStatement := SAP.P003a.WH.W3.T17_whole

theorem T21 : T21WholeStatement := SAP.P003a.WH.W1.T21_whole

theorem T22 : T22WholeStatement := SAP.P003a.WH.W1.T22_whole

theorem T23 : T23WholeStatement := SAP.P003a.WH.W1.T23_whole

end SAP.P003a
