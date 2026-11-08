import SAP.P005a.WH.W1.Proofs.T14
import SAP.P005a.WH.W1.Proofs.T1
import SAP.P005a.WH.W1.Proofs.T2
import SAP.P005a.WH.W1.Proofs.T3
import SAP.P005a.WH.W1.Proofs.T4
import SAP.P005a.WH.W2.Proofs.T5
import SAP.P005a.WH.W2.Proofs.T7
import SAP.P005a.WH.W2.Proofs.T9
import SAP.P005a.WH.W2.Proofs.T10
import SAP.P005a.WH.W2.Proofs.T11
import SAP.P005a.WH.W3.Proofs.T12
import SAP.P005a.Defs
import SAP.P005a.Bridge
import AronowAudit.P005.Wave1.Gap.GP005B1b
import AronowAudit.P005.Wave1.Gap.GP005B4c
import AronowAudit.P005.Wave1.Gap.GP005B4b
import AronowAudit.P005.Wave1.Gap.GLP005B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P005a SAP.P005a.Bridge Finset Filter
open scoped BigOperators Matrix Topology

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

theorem SAP.P005a.T1 : SAP.P005a.T1WholeStatement := SAP.P005a.WH.W1.T1_whole

theorem SAP.P005a.T2 : SAP.P005a.T2WholeStatement := SAP.P005a.WH.W1.T2_whole

theorem SAP.P005a.T3 : SAP.P005a.T3WholeStatement := SAP.P005a.WH.W1.T3_whole

theorem SAP.P005a.T4 : SAP.P005a.T4WholeStatement := SAP.P005a.WH.W1.T4_whole

theorem SAP.P005a.T5 : SAP.P005a.T5WholeStatement := SAP.P005a.WH.W2.T5_whole

theorem SAP.P005a.T6 : T6Statement := by
  intro n d m P hn hm hmn hx
  have h := AronowAudit.P005.Wave1.corrected_interacted_third_bias_proof
    (toPopulation P) hn hm hmn hx
  have ht : expectation m (fun S => dot (xMean P S) (xMean P S) *
      mean S (centered P.yT)) = NTTT n m * leverageCov P P.yT := h.1
  have hc : expectation m (fun S => dot (xMean P (control S)) (xMean P (control S)) *
      mean (control S) (centered P.yC)) = NCCC n m * leverageCov P P.yC := h.2.1
  refine ⟨ht, hc, ?_, ?_, h.2.2⟩
  · simp_rw [nu3_sign]
    rw [expectation_neg, ht]
    ring
  · simp_rw [nu3_sign]
    rw [expectation_neg, hc]
    ring

theorem SAP.P005a.T7 : SAP.P005a.T7WholeStatement := SAP.P005a.WH.W2.T7_whole

theorem SAP.P005a.T9 : SAP.P005a.T9WholeStatement := SAP.P005a.WH.W2.T9_whole

theorem SAP.P005a.T10 : SAP.P005a.T10WholeStatement := SAP.P005a.WH.W2.T10_whole

theorem SAP.P005a.T11 : SAP.P005a.T11WholeStatement := SAP.P005a.WH.W2.T11_whole

theorem SAP.P005a.T12 : SAP.P005a.T12WholeStatement := SAP.P005a.WH.W3.T12_whole

theorem SAP.P005a.T13 : T13Statement := by
  intro n d m P hn hm hmn hP hinv
  exact AronowAudit.P005.Wave1.corrected_control_bias_estimator_proof
    (toPopulation P) hn hm hmn hP hinv

theorem SAP.P005a.T14 : SAP.P005a.T14WholeStatement := SAP.P005a.WH.W1.T14_whole
