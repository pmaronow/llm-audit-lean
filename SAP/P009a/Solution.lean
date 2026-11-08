import SAP.P009a.WH.W1.Proofs.T16
import SAP.P009a.WH.W1.Proofs.T17
import SAP.P009a.WH.W1.Proofs.T1
import SAP.P009a.WH.W1.Proofs.T2
import SAP.P009a.WH.W1.Proofs.T3
import SAP.P009a.WH.W2.Proofs.T4
import SAP.P009a.WH.W2.Proofs.T5
import SAP.P009a.WH.W2.Proofs.T11
import SAP.P009a.WH.W2.Proofs.T12
import SAP.P009a.WH.W2.Proofs.T13
import SAP.P009a.WH.W3.Proofs.T14
import SAP.P009a.WH.W3.Proofs.T15
import SAP.P009a.WH.W3.Proofs.T6
import SAP.P009a.WH.W3.Proofs.T7
import SAP.P009a.WH.W3.Proofs.T8
import SAP.P009a.WH.W4.Proofs.T9
import SAP.P009a.WH.W4.Proofs.T10
import SAP.P009a.Defs
import SAP.P009a.Bridge
import AronowAudit.P009.P009_Audit
import AronowAudit.P009.P009_NormalCompletion
import AronowAudit.P009.P009_LimsupCompletion
import AronowAudit.P009.P009_DiagonalCompletion
import AronowAudit.P009.P009_MixingBasics
import AronowAudit.P009.P009_OverwhelmingCompletion
import AronowAudit.P009.Wave1.Gap.GLP0091B1
import AronowAudit.P009.Wave1.Gap.GLP0091B2
import AronowAudit.P009.Wave1.Gap.GLP0091B3
import AronowAudit.P009.Wave1.Gap.GLP0091B7
import AronowAudit.P009.Wave1.Gap.GP0091B1b
import AronowAudit.P009.Wave1.Gap.GP0092B2
import AronowAudit.P009.Wave1.Gap.GLP0092B5


set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P009a SAP.P009a.Bridge Filter MeasureTheory
open scoped BigOperators Topology Classical

noncomputable section

theorem SAP.P009a.T1 : SAP.P009a.T1WholeStatement :=
  SAP.P009a.WH.W1.T1_whole

theorem SAP.P009a.T2 : SAP.P009a.T2WholeStatement :=
  SAP.P009a.WH.W1.T2_whole

theorem SAP.P009a.T3 : SAP.P009a.T3WholeStatement :=
  SAP.P009a.WH.W1.T3_whole

theorem SAP.P009a.T4 : SAP.P009a.T4WholeStatement :=
  SAP.P009a.WH.W2.T4_whole

theorem SAP.P009a.T5 : SAP.P009a.T5WholeStatement :=
  SAP.P009a.WH.W2.T5_whole

theorem SAP.P009a.T6 : SAP.P009a.T6WholeStatement :=
  SAP.P009a.WH.W3.T6_whole

theorem SAP.P009a.T7 : SAP.P009a.T7WholeStatement :=
  SAP.P009a.WH.W3.T7_whole

theorem SAP.P009a.T8 : SAP.P009a.T8WholeStatement :=
  SAP.P009a.WH.W3.T8_whole

theorem SAP.P009a.T9 : SAP.P009a.T9WholeStatement :=
  SAP.P009a.WH.W4.T9_whole

theorem SAP.P009a.T10 : SAP.P009a.T10WholeStatement :=
  SAP.P009a.WH.W4.T10_whole

theorem SAP.P009a.T11 : SAP.P009a.T11WholeStatement :=
  SAP.P009a.WH.W2.T11_whole

theorem SAP.P009a.T12 : SAP.P009a.T12WholeStatement :=
  SAP.P009a.WH.W2.T12_whole

theorem SAP.P009a.T13 : SAP.P009a.T13WholeStatement :=
  SAP.P009a.WH.W2.T13_whole

theorem SAP.P009a.T14 : SAP.P009a.T14WholeStatement :=
  SAP.P009a.WH.W3.T14_whole

theorem SAP.P009a.T15 : SAP.P009a.T15WholeStatement :=
  SAP.P009a.WH.W3.T15_whole

theorem SAP.P009a.T16 : SAP.P009a.T16WholeStatement :=
  SAP.P009a.WH.W1.T16_whole

theorem SAP.P009a.T17 : SAP.P009a.T17WholeStatement :=
  SAP.P009a.WH.W1.T17_whole

end
