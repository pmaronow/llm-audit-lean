import SAP.P003b.Defs
import SAP.P003b.Bridge
import AronowAudit.P003.Wave1.Gap.GP0031B3
import AronowAudit.P003.Wave1.Gap.GP0031B3b
import AronowAudit.P003.Wave1.Gap.GP0032B2
import AronowAudit.P003.Wave1.Gap.GLP0032B7
import AronowAudit.P003.Wave1.Gap.GP0031B2
import AronowAudit.P003.Wave1.Gap.GLP0032B3
import AronowAudit.P003.Wave1.Gap.GLP0032B6
import AronowAudit.P003.Wave1.Gap.GLP0032B2
import AronowAudit.P003.Wave1.Gap.GP0032B1b
import AronowAudit.P003.Wave1.Gap.GLP0032B5
import AronowAudit.P003.Wave1.Gap.GLP0032B4
import AronowAudit.P003.Wave1.Gap.GLP0031B2
import AronowAudit.P003.Wave1.Gap.GP0031B1b

import SAP.P003b.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W1
open SAP.P003b SAP.P003b.Bridge
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 8000
set_option maxHeartbeats 2400000

theorem T7_base : T7Statement := by
  constructor
  · intro o reject ho
    simpa only [upperRun_eq,from_to,toEndpoint,List.length_map,testBudget_eq,total_eq] using
      AronowAudit.P003.Wave1.adaptive_test_budget_proof (toCounts o) (fun v i => reject (fromCounts v) i) ho
  · intro v m K α ε hm hn hK hα hε
    have h :=
      AronowAudit.P003.Wave1.corrected_monte_inclusions_proof (toCounts v) m K α ε hm hn hK hα hε
    simp only [uniformProb_eq,canonicalObserved_eq,interval_eq,monteInterval_nativePool,monteInterval_eq,total_eq,testBudget_eq] at h ⊢
    convert h using 1 <;> rfl

theorem T32_base : T32Statement := by
  intro o α ho hn hα
  simpa only [exactUpperRun_eq,complement_eq,upper_eq,lower_eq,toEndpoint,List.length_map,total_eq,logTwo_eq,Option.map_map,Function.comp_def] using
    AronowAudit.P003.Wave1.fast_exact_interval_proof (toCounts o) α ho hn hα

theorem T6_base : T6Statement := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [adaptiveData_eq,randomStates_any,multiplicity_any,observed_any,total_eq,estimateQ_eq,
      AronowAudit.P003.binomial,binomial,List.map_map,Function.comp_def,from_to,to_inj,fromCounts] using
      AronowAudit.P003.adaptive_data_valid
  · simpa only [adaptiveData_eq,intervalQ_eq,upperRun_eq,exactRejectQ_fn,toEndpoint,
      List.length_map,traceGet_snd,traceProbability_eq] using
      AronowAudit.P003.Wave1.adaptivity_counterexample_proof
  · have h :=
      AronowAudit.P003.Wave1.adaptive_probability_inequalities_proof
    simp only [adaptiveData_eq,upperRun_eq,exactRejectQ_fn,approximateReject_fn,approximateReject_nativePool,toEndpoint,
      List.length_map,uniformProb_eq,firstMismatch_eq,traceGet_snd] at h ⊢
    convert h using 1 <;> rfl
  · have h :=
      AronowAudit.P003.Wave1.aggregate_bound_counterexample_proof
    simp only [adaptiveData_eq,upperRun_eq,approximateReject_fn,approximateReject_nativePool,toEndpoint,
      List.length_map,uniformProb_eq,traceGet_snd] at h ⊢
    convert h using 1 <;> rfl

theorem T18_base : T18Statement := by
  refine ⟨@AronowAudit.P003.balanced_algorithm_complexity,?_,?_,@AronowAudit.P003.squared_log_dominates⟩
  · intro r K hr hK
    have h :=
      AronowAudit.P003.Wave1.balanced_shuffle_lower_bounds_proof r K hr hK
    simp only [uniformProb_eq,shuffleCost_nativePool,shuffleCost_any,expectedShuffleCost_any,logTwo_eq] at h ⊢
    convert h using 1 <;> rfl
  · intro c hc
    simpa only [expectedShuffleCost_any,recommendedK_eq] using
      AronowAudit.P003.Wave1.balanced_shuffle_not_linear_polylog_proof c hc

theorem T36_base : T36Statement := by
  constructor
  · intro o K c₀ c₁ c₂ hc
    have h := AronowAudit.P003.general_finite_counts (toCounts o) K c₀ c₁ c₂ hc
    refine ⟨?_,?_,?_⟩
    · simpa only [drawCount_eq,total_eq] using h.1
    · simpa only [updateCount_eq,total_eq] using h.2.1
    · intro hn hK
      simpa only [operations_eq,total_eq] using
        h.2.2.trans (AronowAudit.P003.general_envelope_bound o.total K hn hK c₀ c₁ c₂ hc)
  · intro c₀ c₁ c₂ hc o ho hdesign
    simpa only [operations_eq] using
      AronowAudit.P003.general_complexity c₀ c₁ c₂ hc (fun p => toCounts (o p)) ho hdesign

theorem T30_base : T30Statement := by
  intro o α ho hα
  simpa only [estimate_eq,accepted_eq,interval_eq,lower_eq,upper_eq] using
    AronowAudit.P003.balanced_estimate_in_interval (toCounts o) α ho hα

end SAP.P003b.WH.W1
