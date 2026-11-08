import SAP.P029a.Defs
import SAP.P029a.Bridge
import AronowAudit.P029.P029_Audit
import AronowAudit.P029.Wave1.Gap.GP029B2b
import AronowAudit.P029.Wave1.Gap.GP029B4
import AronowAudit.P029.Wave1.Gap.GP029B5
import AronowAudit.P029.Wave1.Gap.GP029B1
import SAP.P029a.WH.W1.Proofs.T2
import SAP.P029a.WH.W1.Proofs.T4
import SAP.P029a.WH.W1.Proofs.T7

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P029a

universe u v

theorem SAP.P029a.T1 : T1Statement := by
  exact Bridge.target1

theorem SAP.P029a.T2 : SAP.P029a.T2WholeStatement := SAP.P029a.WH.W1.T2_whole

theorem SAP.P029a.T3 : T3Statement := by
  exact Bridge.target3

theorem SAP.P029a.T4 : SAP.P029a.T4WholeStatement := SAP.P029a.WH.W1.T4_whole

theorem SAP.P029a.T5 : T5Statement := by
  exact Bridge.target5

theorem SAP.P029a.T6 : T6Statement.{u} := by
  exact Bridge.target6

theorem SAP.P029a.T7 : SAP.P029a.T7WholeStatement := SAP.P029a.WH.W1.T7_whole

theorem SAP.P029a.T8 : T8Statement.{u,v} := by
  exact Bridge.target8

theorem SAP.P029a.T9 : T9Statement := by
  exact Bridge.target9

theorem SAP.P029a.T10 : T10Statement.{u} := by
  exact Bridge.target10

theorem SAP.P029a.T11 : T11Statement := by
  exact Bridge.target11

theorem SAP.P029a.T12 : T12Statement.{u,v} := by
  exact Bridge.target12

theorem SAP.P029a.T13 : T13Statement := by
  exact Bridge.target13
