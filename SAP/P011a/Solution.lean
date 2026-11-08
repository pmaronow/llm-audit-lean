import SAP.P011a.Defs
import SAP.P011a.Bridge
import AronowAudit.P011.P011_Audit
import AronowAudit.P011.P011_SpectralCompletion
import AronowAudit.P011.Wave1.Gap.GLP011B1
import SAP.P011a.WH.W1.Proofs.T12
import SAP.P011a.WH.W1.Proofs.T6
import SAP.P011a.WH.W1.Proofs.T7
import SAP.P011a.WH.W1.Proofs.T8
import SAP.P011a.WH.W2.Proofs.T9
import SAP.P011a.WH.W2.Proofs.T10
import SAP.P011a.WH.W2.Proofs.T1
import SAP.P011a.WH.W2.Proofs.T2
import SAP.P011a.WH.W2.Proofs.T3
import SAP.P011a.WH.W3.Proofs.T4
import SAP.P011a.WH.W3.Proofs.T5

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Finset SAP.P011a
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

theorem SAP.P011a.T1 : SAP.P011a.T1WholeStatement := SAP.P011a.WH.W2.T1_whole

theorem SAP.P011a.T2 : SAP.P011a.T2WholeStatement := SAP.P011a.WH.W2.T2_whole

theorem SAP.P011a.T3 : SAP.P011a.T3WholeStatement := SAP.P011a.WH.W2.T3_whole

theorem SAP.P011a.T4 : SAP.P011a.T4WholeStatement := SAP.P011a.WH.W3.T4_whole

theorem SAP.P011a.T5 : SAP.P011a.T5WholeStatement := SAP.P011a.WH.W3.T5_whole

theorem SAP.P011a.T6 : SAP.P011a.T6WholeStatement := SAP.P011a.WH.W1.T6_whole

theorem SAP.P011a.T7 : SAP.P011a.T7WholeStatement := SAP.P011a.WH.W1.T7_whole

theorem SAP.P011a.T8 : SAP.P011a.T8WholeStatement := SAP.P011a.WH.W1.T8_whole

theorem SAP.P011a.T9 : SAP.P011a.T9WholeStatement := SAP.P011a.WH.W2.T9_whole

theorem SAP.P011a.T10 : SAP.P011a.T10WholeStatement := SAP.P011a.WH.W2.T10_whole

theorem SAP.P011a.T11 : SAP.P011a.T11Statement := by
  exact ⟨Bridge.AlternatingCounterexample_proved, Bridge.AlternatingMoments_proved,
    Bridge.AlternatingEstimatorIdentities_proved⟩

theorem SAP.P011a.T12 : SAP.P011a.T12WholeStatement := SAP.P011a.WH.W1.T12_whole

theorem SAP.P011a.T13 : SAP.P011a.T13Statement := by
  exact ⟨Bridge.MatchingReduction_proved, Bridge.MatchingCounts_proved,
    Bridge.MatchingInstances_proved⟩

theorem SAP.P011a.T14 : SAP.P011a.T14Statement := by
  exact ⟨Bridge.RelaxationUpperBound_proved, Bridge.RelaxationGaps_proved,
    Bridge.RelaxationProgramValues_proved, Bridge.RelaxationNamedWitness_proved⟩
