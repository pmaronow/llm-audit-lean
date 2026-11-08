import SAP.P002a.Defs
import SAP.P002a.Bridge
import AronowAudit.P002.Wave1.Gap.GLP0021B1
import AronowAudit.P002.Wave1.Gap.GP0021B1
import AronowAudit.P002.Wave1.Gap.GP0021B2
import AronowAudit.P002.Wave1.Gap.GLP0022B1
import AronowAudit.P002.Wave1.Gap.GLP0022B2
import AronowAudit.P002.Wave1.Gap.GP0022B2b
import AronowAudit.P002.Wave1.Gap.GLP0022B3
import AronowAudit.P002.Wave1.Gap.Theorem2
import AronowAudit.P002.Wave1.E61Eigenvalue
import AronowAudit.P002.Wave1.Gap.DecisionLemma12
import AronowAudit.P002.Wave1.Gap.DecisionLemma20
import SAP.P002a.WH.W1.Proofs.T15
import SAP.P002a.WH.W1.Proofs.T8
import SAP.P002a.WH.W1.Proofs.T9
import SAP.P002a.WH.W1.Proofs.T11
import SAP.P002a.WH.W2.Proofs.T14
import SAP.P002a.WH.W2.Proofs.T1
import SAP.P002a.WH.W2.Proofs.T2
import SAP.P002a.WH.W2.Proofs.T4
import SAP.P002a.WH.W2.Proofs.T5
import SAP.P002a.WH.W3.Proofs.T6
import SAP.P002a.WH.W4.Proofs.T7

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
open SAP.P002a SAP.P002a.Bridge

theorem SAP.P002a.T1 : SAP.P002a.T1WholeStatement := SAP.P002a.WH.W2.T1_whole

theorem SAP.P002a.T2 : SAP.P002a.T2WholeStatement := SAP.P002a.WH.W2.T2_whole

theorem SAP.P002a.T3 : SAP.P002a.T3Statement := by
  constructor
  · exact fun h => AronowAudit.P002.ConfidenceFollowup.printed_lemma5_refuted
      (printedLemma5_correspondence.mp h)
  · exact fun h => AronowAudit.P002.ConfidenceFollowup.printed_E10_refuted
      (printedE10_correspondence.mp h)

theorem SAP.P002a.T4 : SAP.P002a.T4WholeStatement := SAP.P002a.WH.W2.T4_whole

theorem SAP.P002a.T5 : SAP.P002a.T5WholeStatement := SAP.P002a.WH.W2.T5_whole

theorem SAP.P002a.T6 : SAP.P002a.T6WholeStatement := SAP.P002a.WH.W3.T6_whole

theorem SAP.P002a.T7 : SAP.P002a.T7WholeStatement_W4 := SAP.P002a.WH.W4.T7_whole

theorem SAP.P002a.T8 : SAP.P002a.T8WholeStatement := SAP.P002a.WH.W1.T8_whole

theorem SAP.P002a.T9 : SAP.P002a.T9WholeStatement := SAP.P002a.WH.W1.T9_whole

theorem SAP.P002a.T10 : SAP.P002a.T10Statement := by
  constructor
  · exact AronowAudit.P002.centring_counterexample
  · have hA : assignments centringModel =
        ({{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}} : Finset (Finset (Fin 4))) :=
      AronowAudit.P002.centring_assignments
    simp only [T10Corrected, expectation, hA]
    simp (discharger := decide) only [Finset.sum_insert, Finset.sum_singleton,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    norm_num [S2, fraction, popVar, observedW,
      observedY, observedD, armMean, groupMean, centringModel, w, v, mean, binary,
      Fin.sum_univ_succ, Finset.sum_insert]

theorem SAP.P002a.T11 : SAP.P002a.T11WholeStatement := SAP.P002a.WH.W1.T11_whole

theorem SAP.P002a.T12 : SAP.P002a.T12Statement := by
  constructor
  · exact AronowAudit.P002.C31_counterexample
  · have hc : ({0,1,2,3} : Finset (Fin 8))ᶜ = {4,5,6,7} := by decide
    norm_num [T12Values, assignments, signModel, observedW, observedY, observedD,
      armMean, groupMean, hc, fraction, binary, Fin.sum_univ_succ, Finset.sum_insert]
    norm_num [Nat.choose]

theorem SAP.P002a.T13 : SAP.P002a.T13Statement := by
  intro n P hP q S hS r hr hlo hhi
  exact AronowAudit.P002.Wave1.corrected_C31_proof (toPopulation P) hP q S hS r hr hlo hhi

theorem SAP.P002a.T14 : SAP.P002a.T14WholeStatement := SAP.P002a.WH.W2.T14_whole

theorem SAP.P002a.T15 : SAP.P002a.T15WholeStatement := SAP.P002a.WH.W1.T15_whole
