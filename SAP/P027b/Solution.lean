import SAP.P027b.Defs
import SAP.P027b.Bridge
import AronowAudit.P027.P027_Audit
import AronowAudit.P027.Wave1.Gap.GLP027P016P031B2
import AronowAudit.P027.Wave1.Gap.GP027P016P031B1b
import SAP.P027b.WH.W1.Proofs.T14
import SAP.P027b.WH.W1.Proofs.T16

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem SAP.P027b.T14 : SAP.P027b.T14WholeStatement := SAP.P027b.WH.W1.T14_whole

theorem SAP.P027b.T15 : SAP.P027b.T15Statement := SAP.P027b.Bridge.T15_proof

theorem SAP.P027b.T16 : SAP.P027b.T16WholeStatement := SAP.P027b.WH.W1.T16_whole

theorem SAP.P027b.T17 : SAP.P027b.T17Statement := SAP.P027b.Bridge.T17_proof

theorem SAP.P027b.T18 : SAP.P027b.T18Statement := SAP.P027b.Bridge.T18_proof

theorem SAP.P027b.T19 : SAP.P027b.T19Statement := SAP.P027b.Bridge.T19_proof

theorem SAP.P027b.T20 : SAP.P027b.T20Statement := SAP.P027b.Bridge.T20_proof

theorem SAP.P027b.T21 : SAP.P027b.T21Statement := SAP.P027b.Bridge.T21_proof

theorem SAP.P027b.T22 : SAP.P027b.T22Statement := SAP.P027b.Bridge.T22_proof

theorem SAP.P027b.T23 : SAP.P027b.T23Statement := SAP.P027b.Bridge.T23_proof

theorem SAP.P027b.T24 : SAP.P027b.T24Statement := SAP.P027b.Bridge.T24_proof
