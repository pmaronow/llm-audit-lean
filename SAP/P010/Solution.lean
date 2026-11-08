import SAP.P010.Defs
import SAP.P010.Bridge
import AronowAudit.P010.P010_Empirical
import AronowAudit.P010.P010_Population
import AronowAudit.P010.P010_Transport
import AronowAudit.P010.Wave1.Gap.GLP010P033B1
import AronowAudit.P010.Wave1.Gap.GLP010P033B2
import AronowAudit.P010.Wave1.Gap.GLP010P033B3
import AronowAudit.P010.Wave1.Gap.GLP010P033B4
import AronowAudit.P010.Wave1.Gap.GLP010P033B5
import AronowAudit.P010.Wave1.Gap.GP010P033B1b
import AronowAudit.P010.Wave1.PropositionOneElseTailC
import AronowAudit.P010.Wave1.PropositionOneFiniteTailC
import SAP.P010.WH.W1.Proofs.T12
import SAP.P010.WH.W1.Proofs.T17

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical Topology BigOperators

theorem SAP.P010.T1 : SAP.P010.T1Statement := by
  exact SAP.P010.Bridge.T1_correspondence.mpr (@AronowAudit.P010.empirical_overlap_counterexample)

theorem SAP.P010.T2 : SAP.P010.T2Statement := by
  exact SAP.P010.Bridge.T2_correspondence.mpr (⟨@AronowAudit.P010.empirical_exact_certificate, @AronowAudit.P010.empirical_cutoff_certificate, @AronowAudit.P010.empirical_overlap_corrected⟩)

theorem SAP.P010.T3 : SAP.P010.T3Statement := by
  exact SAP.P010.Bridge.T3_correspondence.mpr (@AronowAudit.P010.Wave1.missing_passing_condition_counterexample_proof)

theorem SAP.P010.T4 : SAP.P010.T4Statement := by
  exact SAP.P010.Bridge.T4_correspondence.mpr (@AronowAudit.P010.Wave1.proposition_one_finite_proof)

theorem SAP.P010.T5 : SAP.P010.T5Statement := by
  exact SAP.P010.Bridge.T5_correspondence.mpr (@AronowAudit.P010.Wave1.infinite_sharp_bounds_counterexample_proof)

theorem SAP.P010.T6 : SAP.P010.T6Statement := by
  exact SAP.P010.Bridge.T6_correspondence.mpr (@AronowAudit.P010.Wave1.proposition_one_else_proof)

theorem SAP.P010.T7 : SAP.P010.T7Statement := by
  exact SAP.P010.Bridge.T7_correspondence.mpr (@AronowAudit.P010.joint_independence_step_counterexample)

theorem SAP.P010.T8 : SAP.P010.T8Statement := by
  exact SAP.P010.Bridge.T8_correspondence.mpr (@AronowAudit.P010.corollary_one_corrected_proof)

theorem SAP.P010.T9 : SAP.P010.T9Statement := by
  exact SAP.P010.Bridge.T9_correspondence.mpr (@AronowAudit.P010.Wave1.simulation_width_counterexample_proof)

theorem SAP.P010.T10 : SAP.P010.T10Statement := by
  exact SAP.P010.Bridge.T10_correspondence.mpr (@AronowAudit.P010.Wave1.simulation_invariance_corrected_proof)

theorem SAP.P010.T11 : SAP.P010.T11Statement := by
  exact SAP.P010.Bridge.T11_correspondence.mpr (⟨@AronowAudit.P010.transport_logistic_certificate, @AronowAudit.P010.transport_odds_counterexample⟩)

theorem SAP.P010.T12 : SAP.P010.T12WholeStatement :=
  SAP.P010.WH.W1.T12_whole

theorem SAP.P010.T13 : SAP.P010.T13Statement := by
  exact SAP.P010.Bridge.T13_correspondence.mpr (@AronowAudit.P010.Wave1.lower_tail_upper_bound_counterexample_proof)

theorem SAP.P010.T14 : SAP.P010.T14Statement := by
  exact SAP.P010.Bridge.T14_correspondence.mpr (@AronowAudit.P010.Wave1.upper_tail_proof_corrected_proof)

theorem SAP.P010.T15 : SAP.P010.T15Statement := by
  apply SAP.P010.Bridge.T15_correspondence.mpr
  intro K d μ h a hA hc hi
  obtain ⟨hLaw, hRates, hTrim, hTail, hFinite⟩ :=
    AronowAudit.P010.Wave1.observable_upper_bound_corrected_proof μ h a hA hc hi
  exact ⟨hLaw, hRates, hTrim, fun hr => ⟨hTail, (hFinite hr).1, (hFinite hr).2⟩⟩


theorem SAP.P010.T16 : SAP.P010.T16Statement := by
  exact SAP.P010.Bridge.T16_correspondence.mpr (@AronowAudit.P010.selection_counterexample_corrected)

theorem SAP.P010.T17 : SAP.P010.T17WholeStatement :=
  SAP.P010.WH.W1.T17_whole

theorem SAP.P010.T18 : SAP.P010.T18Statement := by
  exact SAP.P010.Bridge.T18_correspondence.mpr (@AronowAudit.P010.corollary_one)

theorem SAP.P010.T19 : SAP.P010.T19Statement := by
  exact SAP.P010.Bridge.T19_correspondence.mpr (@AronowAudit.P010.lemma_one)

theorem SAP.P010.T20 : SAP.P010.T20Statement := by
  exact SAP.P010.Bridge.T20_correspondence.mpr (@AronowAudit.P010.corollary_two)

theorem SAP.P010.T21 : SAP.P010.T21Statement := by
  apply SAP.P010.Bridge.T21_correspondence.mpr
  have h := AronowAudit.P010.selection_counterexample_corrected (1/2) (by norm_num) (by norm_num)
  rcases h with ⟨hAss, hCovI, hCovB, hA, hRate, hIS, hEff, hS, hEA, hE10, hE01,
    hM0, hM1, hContrast, hne⟩
  refine ⟨AronowAudit.P010.selectionLaw (1/2), hAss, hIS, ?_, ?_, ?_,
    SAP.P010.Bridge.selection_integrableOn _ _ _,
    SAP.P010.Bridge.selection_integrableOn _ _ _,
    SAP.P010.Bridge.selection_integrableOn _ _ _, ?_⟩
  · rw [hA]; norm_num
  · rw [SAP.P010.Bridge.selection_selected_mass]; norm_num
  · rw [SAP.P010.Bridge.selection_selected_mass]; norm_num
  · rw [hContrast, hEA]
    exact hne


theorem SAP.P010.T22 : SAP.P010.T22Statement := by
  exact SAP.P010.Bridge.T22_correspondence.mpr (@AronowAudit.P010.corollary_four)

theorem SAP.P010.T23 : SAP.P010.T23Statement := by
  apply SAP.P010.Bridge.T23_correspondence.mpr
  have h := AronowAudit.P010.selection_counterexample_corrected (1/2) (by norm_num) (by norm_num)
  rcases h with ⟨hAss, hCovI, hCovB, hA, hRate, hIS, hEff, hS, hEA, hE10, hE01,
    hM0, hM1, hContrast, hne⟩
  refine ⟨AronowAudit.P010.selectionLaw (1/2), hAss.1, hAss.2.2, hCovI, hCovB,
    ?_, ?_, ?_, SAP.P010.Bridge.selection_integrableOn _ _ _,
    SAP.P010.Bridge.selection_integrableOn _ _ _,
    SAP.P010.Bridge.selection_integrableOn _ _ _, ?_⟩
  · rw [measure_congr (SAP.P010.Bridge.selection_covariate_event _ _), hA]
    norm_num
  · rw [measure_congr (SAP.P010.Bridge.selection_covariate_event _ _),
      SAP.P010.Bridge.selection_selected_mass]
    norm_num
  · rw [measure_congr (SAP.P010.Bridge.selection_covariate_event _ _),
      SAP.P010.Bridge.selection_selected_mass]
    norm_num
  · rw [AronowAudit.P010.eventMean_congr_set _ _
        (SAP.P010.Bridge.selection_covariate_event _ _),
      AronowAudit.P010.eventMean_congr_set _ _
        (SAP.P010.Bridge.selection_covariate_event _ _),
      AronowAudit.P010.eventMean_congr_set _ _
        (SAP.P010.Bridge.selection_covariate_event _ _), hContrast, hEA]
    exact hne

