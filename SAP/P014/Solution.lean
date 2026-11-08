import SAP.P014.Defs
import SAP.P014.Bridge
import AronowAudit.P014.P014_LocalRandomization
import SAP.P014.WH.W1.Proofs.T2
import SAP.P014.WH.W1.Proofs.T6

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

theorem SAP.P014.T1 : SAP.P014.T1Statement := SAP.P014.Bridge.T1_proof
theorem SAP.P014.T2 : SAP.P014.T2WholeStatement := SAP.P014.WH.W1.T2_whole
theorem SAP.P014.T3 : SAP.P014.T3Statement.{u} := SAP.P014.Bridge.T3_proof
theorem SAP.P014.T4 : SAP.P014.T4Statement := SAP.P014.Bridge.T4_proof
theorem SAP.P014.T5 : SAP.P014.T5Statement := SAP.P014.Bridge.T5_proof
theorem SAP.P014.T6 : SAP.P014.T6WholeStatement := SAP.P014.WH.W1.T6_whole
theorem SAP.P014.T7 : SAP.P014.T7Statement.{u} := SAP.P014.Bridge.T7_proof
theorem SAP.P014.T8 : SAP.P014.T8Statement := SAP.P014.Bridge.T8_proof
theorem SAP.P014.T9 : SAP.P014.T9Statement := SAP.P014.Bridge.T9_proof
theorem SAP.P014.T10 : SAP.P014.T10Statement := SAP.P014.Bridge.T10_proof
