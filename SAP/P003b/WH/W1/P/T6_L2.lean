import SAP.P003b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W1.P.T6_L2

open SAP.P003b SAP.P003b.Bridge
open AronowAudit.P003.Wave1
attribute [local instance 0] Classical.propDecidable

lemma event0_probability :
    uniformProb (w1T6Event (0 : Fin 4)) =
      (api5_weight (R := ℚ) api5_p api5_result_0 : ℝ) := by
  have h := api5_probability_value_actual (0 : Fin 4)
    (fun v => v.any (fun x => decide (x < 10))) api5_below_certificate
  rw [SAP.P003b.Bridge.uniformProb_eq] at h
  simp only [testBudget_eq, upperRun_eq,
    approximateReject_fn, adaptiveData_eq, Option.any_eq_true,
    decide_eq_true_eq] at h ⊢
  exact h

lemma atrExact_bridge : atr_trace_exact = w1Trace_exact.map toTrace := by rfl

lemma atrLow_bridge : atr_trace_low = w1Trace_low.map toTrace := by rfl

lemma event1_probability :
    uniformProb (w1T6Event (1 : Fin 4)) =
      (api5_weight (R := ℚ) api5_p api5_result_1 : ℝ) := by
  have h := api5_probability_actual (1 : Fin 4) (api5_bad atr_trace_exact true)
    api5_bad_rejection_certificate
  rw [atrExact_bridge] at h
  rw [SAP.P003b.Bridge.uniformProb_eq] at h
  simp only [testBudget_eq, api5_bad_iff,
    upperRun_eq, approximateReject_fn, adaptiveData_eq, firstMismatch_eq,
    traceGet_snd, List.length_map] at h ⊢
  exact h

lemma event2_probability :
    uniformProb (w1T6Event (2 : Fin 4)) =
      (api5_weight (R := ℚ) api5_p api5_result_2 : ℝ) := by
  have h := api5_probability_value_actual (2 : Fin 4)
    (fun v => v.any (fun x => decide (10 < x))) api5_above_certificate
  rw [SAP.P003b.Bridge.uniformProb_eq] at h
  simp only [testBudget_eq, upperRun_eq, approximateReject_fn, adaptiveData_eq,
    Option.any_eq_true,
    decide_eq_true_eq] at h ⊢
  exact h

lemma event3_probability :
    uniformProb (w1T6Event (3 : Fin 4)) =
      (api5_weight (R := ℚ) api5_p api5_result_3 : ℝ) := by
  have h := api5_probability_actual (3 : Fin 4) (api5_bad atr_trace_low false)
    api5_bad_acceptance_certificate
  rw [atrLow_bridge] at h
  rw [SAP.P003b.Bridge.uniformProb_eq] at h
  simp only [testBudget_eq, api5_bad_iff,
    upperRun_eq, approximateReject_fn, adaptiveData_eq, firstMismatch_eq,
    traceGet_snd, List.length_map] at h ⊢
  exact h

lemma mass0_bounds :
    (862845 : ℚ) / 1000000 < api5_weight (R := ℚ) api5_p api5_result_0 ∧
      api5_weight (R := ℚ) api5_p api5_result_0 < (862855 : ℚ) / 1000000 := by
  decide +kernel

lemma mass1_bounds :
    (948845 : ℚ) / 1000000 < api5_weight (R := ℚ) api5_p api5_result_1 ∧
      api5_weight (R := ℚ) api5_p api5_result_1 < (948855 : ℚ) / 1000000 := by
  decide +kernel

lemma mass2_bounds :
    (30045 : ℚ) / 1000000 < api5_weight (R := ℚ) api5_p api5_result_2 ∧
      api5_weight (R := ℚ) api5_p api5_result_2 < (30055 : ℚ) / 1000000 := by
  decide +kernel

lemma mass3_bounds :
    (3795 : ℚ) / 1000000 < api5_weight (R := ℚ) api5_p api5_result_3 ∧
      api5_weight (R := ℚ) api5_p api5_result_3 < (3805 : ℚ) / 1000000 := by
  decide +kernel

lemma close_mass (p m target : ℝ) (hm : p = m)
    (hl : target - 0.000005 < m) (hu : m < target + 0.000005) :
    |p - target| < 0.000005 := by
  rw [abs_lt]
  constructor <;> rw [hm] <;> linarith

end SAP.P003b.WH.W1.P.T6_L2

open SAP.P003b.WH.W1.P.T6_L2
open AronowAudit.P003.Wave1

theorem SAP.P003b.WH.W1.T6_L2_proof : SAP.P003b.WH.W1.T6_L2 := by
  intro j
  fin_cases j
  · have hl : 0.86285 - 0.000005 < (api5_weight (R := ℚ) api5_p api5_result_0 : ℝ) := by
      have hm : ((862845 : ℚ) / 1000000 : ℝ) <
          (api5_weight (R := ℚ) api5_p api5_result_0 : ℝ) := by
        exact_mod_cast mass0_bounds.1
      norm_num at hm ⊢
      linarith
    have hu : (api5_weight (R := ℚ) api5_p api5_result_0 : ℝ) < 0.86285 + 0.000005 := by
      have hm : (api5_weight (R := ℚ) api5_p api5_result_0 : ℝ) <
          ((862855 : ℚ) / 1000000 : ℝ) := by
        exact_mod_cast mass0_bounds.2
      norm_num at hm ⊢
      linarith
    exact close_mass _ _ _ event0_probability hl hu
  · have hl : 0.94885 - 0.000005 < (api5_weight (R := ℚ) api5_p api5_result_1 : ℝ) := by
      have hm : ((948845 : ℚ) / 1000000 : ℝ) <
          (api5_weight (R := ℚ) api5_p api5_result_1 : ℝ) := by
        exact_mod_cast mass1_bounds.1
      norm_num at hm ⊢
      linarith
    have hu : (api5_weight (R := ℚ) api5_p api5_result_1 : ℝ) < 0.94885 + 0.000005 := by
      have hm : (api5_weight (R := ℚ) api5_p api5_result_1 : ℝ) <
          ((948855 : ℚ) / 1000000 : ℝ) := by
        exact_mod_cast mass1_bounds.2
      norm_num at hm ⊢
      linarith
    exact close_mass _ _ _ event1_probability hl hu
  · have hl : 0.03005 - 0.000005 < (api5_weight (R := ℚ) api5_p api5_result_2 : ℝ) := by
      have hm : ((30045 : ℚ) / 1000000 : ℝ) <
          (api5_weight (R := ℚ) api5_p api5_result_2 : ℝ) := by
        exact_mod_cast mass2_bounds.1
      norm_num at hm ⊢
      linarith
    have hu : (api5_weight (R := ℚ) api5_p api5_result_2 : ℝ) < 0.03005 + 0.000005 := by
      have hm : (api5_weight (R := ℚ) api5_p api5_result_2 : ℝ) <
          ((30055 : ℚ) / 1000000 : ℝ) := by
        exact_mod_cast mass2_bounds.2
      norm_num at hm ⊢
      linarith
    exact close_mass _ _ _ event2_probability hl hu
  · have hl : 0.00380 - 0.000005 < (api5_weight (R := ℚ) api5_p api5_result_3 : ℝ) := by
      have hm : ((3795 : ℚ) / 1000000 : ℝ) <
          (api5_weight (R := ℚ) api5_p api5_result_3 : ℝ) := by
        exact_mod_cast mass3_bounds.1
      norm_num at hm ⊢
      linarith
    have hu : (api5_weight (R := ℚ) api5_p api5_result_3 : ℝ) < 0.00380 + 0.000005 := by
      have hm : (api5_weight (R := ℚ) api5_p api5_result_3 : ℝ) <
          ((3805 : ℚ) / 1000000 : ℝ) := by
        exact_mod_cast mass3_bounds.2
      norm_num at hm ⊢
      linarith
    exact close_mass _ _ _ event3_probability hl hu
