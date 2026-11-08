import SAP.P031.Defs
import SAP.P031.Bridge
import SAP.P031.WH.W1.Proofs.T10
import SAP.P031.WH.W1.Proofs.T5
import SAP.P031.WH.W1.Proofs.T6
import SAP.P031.WH.W3.Proofs.LeafChecks
import SAP.P031.WH.W2.Proofs.T5

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P031

theorem SAP.P031.T1 : T1Statement := by
  exact SAP.P031.Bridge.t1

theorem SAP.P031.T2 : T2Statement := by
  exact SAP.P031.Bridge.t2

theorem SAP.P031.T3 : T3Statement := by
  exact SAP.P031.Bridge.t3

theorem SAP.P031.T4 : T4Statement := by
  exact SAP.P031.Bridge.t4

-- Imported W1 T5/T6 proofs remain as uncredited related evidence for the
-- broader normality-only contract; neither proves a canonical target.

theorem SAP.P031.T6 : SAP.P031.T6CitedRegimeStatement :=
  SAP.P031.WH.W3.T6_assembly
    SAP.P031.WH.W3.GateAudit.first_leaf
    SAP.P031.WH.W3.GateAudit.second_leaf

theorem SAP.P031.T5 : SAP.P031.T5CitedRegimeStatement :=
  SAP.P031.WH.W2.T5_cited

theorem SAP.P031.T7 : T7Statement := by
  exact SAP.P031.Bridge.t7

theorem SAP.P031.T8 : T8Statement := by
  exact SAP.P031.Bridge.t8

theorem SAP.P031.T9 : T9Statement := by
  exact SAP.P031.Bridge.t9

theorem SAP.P031.T10 : SAP.P031.T10WholeStatement :=
  SAP.P031.WH.W1.T10_whole

theorem SAP.P031.T11 : T11Statement := by
  exact SAP.P031.Bridge.t11

