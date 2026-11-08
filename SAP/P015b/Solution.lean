import SAP.P015b.Defs
import SAP.P015b.WH.W1.Proofs.T23
import SAP.P015b.WH.W1.Proofs.T24
import SAP.P015b.WH.W1.Proofs.T14
import SAP.P015b.WH.W1.Proofs.T21
import SAP.P015b.WH.W2.Proofs.T15
import SAP.P015b.WH.W2.Proofs.T22
import SAP.P015b.WH.W3.Proofs.T10
import SAP.P015b.Bridge
import AronowAudit.P015.P015_PaperAssessments
import AronowAudit.P015.Wave1.Gap.FidP015
import AronowAudit.P015.P015_PositivityRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P015b SAP.P015b.Bridge
universe u v

theorem SAP.P015b.T9 : T9Statement := by
  exact ⟨poolingCounterexample, rawPoolingCounterexample⟩

theorem SAP.P015b.T10 : SAP.P015b.T10WholeStatement_W3 := SAP.P015b.WH.W3.T10_whole

theorem SAP.P015b.T20 : T20Statement := by
  exact leverageComparison

theorem SAP.P015b.T14 : SAP.P015b.T14WholeStatement := SAP.P015b.WH.W1.T14_whole

theorem SAP.P015b.T21 : SAP.P015b.T21WholeStatement := SAP.P015b.WH.W1.T21_whole

theorem SAP.P015b.T11 : T11Statement := by
  exact ⟨taylorFailure, taylorData⟩

theorem SAP.P015b.T15 : SAP.P015b.T15WholeStatement := SAP.P015b.WH.W2.T15_whole

theorem SAP.P015b.T22 : SAP.P015b.T22WholeStatement := SAP.P015b.WH.W2.T22_whole

theorem SAP.P015b.T23 : SAP.P015b.T23WholeStatement := SAP.P015b.WH.W1.T23_whole

theorem SAP.P015b.T24 : SAP.P015b.T24WholeStatement := SAP.P015b.WH.W1.T24_whole

theorem SAP.P015b.T18 : T18Statement := by
  exact ⟨logisticMLStationarity, squareLinkFailure⟩

theorem SAP.P015b.T17 : T17Statement.{u,v} := by
  exact ⟨discretePositivity, smallWeightFamily, smallWeightConsistency,
    fittedZeroFailure, missingPairFailure⟩
