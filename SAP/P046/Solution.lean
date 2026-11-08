import SAP.P046.Defs
import SAP.P046.Bridge
import SAP.P046.WH.W1.Proofs.T1
import SAP.P046.WH.W1.Proofs.T2
import SAP.P046.WH.W1.Proofs.T3
import SAP.P046.WH.W1.Proofs.T4
import SAP.P046.WH.W1.Proofs.T5
import SAP.P046.WH.W2.Proofs.T8
import SAP.P046.WH.W2.Proofs.T9

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P046

theorem SAP.P046.T1 : SAP.P046.T1WholeStatement := SAP.P046.WH.W1.T1_whole

theorem SAP.P046.T2 : SAP.P046.T2WholeStatement := SAP.P046.WH.W1.T2_whole

theorem SAP.P046.T3 : SAP.P046.T3WholeStatement := SAP.P046.WH.W1.T3_whole

theorem SAP.P046.T4 : SAP.P046.T4WholeStatement := SAP.P046.WH.W1.T4_whole

theorem SAP.P046.T5 : SAP.P046.T5WholeStatement := SAP.P046.WH.W1.T5_whole

theorem SAP.P046.T6 : T6Statement := SAP.P046.Bridge.target6

theorem SAP.P046.T7 : T7Statement := SAP.P046.Bridge.target7

theorem SAP.P046.T8 : SAP.P046.T8WholeStatement := SAP.P046.WH.W2.T8_whole

theorem SAP.P046.T9 : SAP.P046.T9WholeStatement := SAP.P046.WH.W2.T9_whole

theorem SAP.P046.T10 : T10Statement := SAP.P046.Bridge.target10
