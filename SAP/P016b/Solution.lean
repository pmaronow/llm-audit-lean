import SAP.P016b.Defs
import SAP.P016b.Bridge
import AronowAudit.P016.P016_Interference
import AronowAudit.P016.Wave1.Gap.GLP027P016P031P016B1
import SAP.P016b.WH.W1.Proofs.T12
import SAP.P016b.WH.W1.Proofs.T13
import SAP.P016b.WH.W1.Proofs.T16

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016b
open scoped BigOperators Classical
open MeasureTheory
noncomputable section

theorem T12 : SAP.P016b.T12WholeStatement := SAP.P016b.WH.W1.T12_whole

theorem T13 : SAP.P016b.T13WholeStatement := SAP.P016b.WH.W1.T13_whole

theorem T14 : T14Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Bridge.exactValidity⟩
  · intro B hB μ _ hex
    refine ⟨?_, ?_, ?_⟩
    · intro c hc
      exact AronowAudit.P016.t14_rank_bound hB μ hex c hc
    · intro α hα hα1
      exact AronowAudit.P016.t14_strict_bound hB μ hex α hα hα1
    · intro α hα hα1
      exact AronowAudit.P016.t14_corrected_valid hB μ hex α hα hα1
  · intro μ _ hex
    have h := AronowAudit.P016.t14_strict_bound (B := 1000) (by decide) μ hex
      (1/20) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  · intro μ _ hex
    have h := AronowAudit.P016.t14_strict_bound (B := 10000) (by decide) μ hex
      (1/20) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  · exact AronowAudit.P016.t14_printed_bounds.2.2.1
  · exact AronowAudit.P016.t14_printed_bounds.2.2.2
  · intro Ω _ P B s π E
    exact AronowAudit.P016.t14_iid_exchangeable (Bridge.toProjectLaw P) B s π E

theorem T15 : T15Statement := by
  exact ⟨AronowAudit.P016.t15_adjustment_witness, AronowAudit.P016.t15_ecdf_witness,
    AronowAudit.P016.t15_diagonal_witness⟩

theorem T16 : SAP.P016b.T16WholeStatement := SAP.P016b.WH.W1.T16_whole

theorem T17 : T17Statement := by
  refine ⟨?_, AronowAudit.P016.t17_comparison_witness⟩
  intro n Y z h0 h1 t
  exact AronowAudit.P016.t17_adjusted_comparison Y z h0 h1 t

theorem T18 : T18Statement := by
  refine ⟨AronowAudit.P016.t18_calibration_witness, ?_⟩
  intro a
  exact AronowAudit.P016.t19_median_nonneg (m := 128) (by decide) calibrationY calibrationZ
    AronowAudit.P016.t18_calibration_witness.2.1 (34/99) a

theorem T19 : T19Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, AronowAudit.P016.t18_calibration_witness,
    AronowAudit.P016.t19_mismatch_numbers⟩
  · intro m hm y z hz t a i
    exact AronowAudit.P016.t19_discrepancy_formula hm y z hz t a i
  · intro m hm y z hz t a
    exact AronowAudit.P016.t19_median_identity hm y z hz t a
  · intro m hm y z hz t j hj hyj
    exact ⟨(AronowAudit.P016.t19_root_discrepancies hm y z hz t j hj hyj).1,
      AronowAudit.P016.t19_calibration_roots hm y z hz t j hj hyj⟩
  · intro n Y z h1 t a ha
    exact AronowAudit.P016.t19_mean_reductions Y z h1 t a ha
  · intro m hm y t a ha
    exact AronowAudit.P016.t19_expected_reductions hm y t a ha
  · intro μ t a hμ hμt _
    exact AronowAudit.P016.t19_matched_parameter μ t a hμ hμt

theorem T20 : T20Statement := by
  refine ⟨AronowAudit.P016.t20_additive_identity, ?_, ?_⟩
  · intro n y z t t0
    exact AronowAudit.P016.t8_additive_mapping y z t t0
  · intro n S hS β τ hβ
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact AronowAudit.P016.t20_model_positive S hS β τ hβ
    · exact AronowAudit.P016.t20_zero_assignment S hS β τ hβ
    · exact AronowAudit.P016.t20_model_composition S hS β τ hβ
    · exact AronowAudit.P016.t20_model_uniformity S hS β τ hβ

theorem T21 : T21Statement := by
  intro P hP S hsym hbin y0 T
  exact ⟨(AronowAudit.P016.t21_exact_level (Bridge.toProjectLaw P) hP S hsym hbin y0 T).1,
    (AronowAudit.P016.t21_exact_level (Bridge.toProjectLaw P) hP S hsym hbin y0 T).2,
    AronowAudit.P016.t21_sampled_level (Bridge.toProjectLaw P) hP S hsym hbin y0 T⟩

end
end SAP.P016b
