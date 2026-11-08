import SAP.P039.Defs
import SAP.P039.Bridge
import SAP.P039.WH.W1.Proofs.T3
import SAP.P039.WH.W1.Proofs.T4
import SAP.P039.WH.W1.Proofs.T7

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P039

theorem SAP.P039.T1 : T1Statement := by
  exact SAP.P039.Bridge.T1_correspondence

theorem SAP.P039.T2 : T2Statement := by
  exact SAP.P039.Bridge.T2_correspondence

theorem SAP.P039.T3 : SAP.P039.T3WholeStatement := SAP.P039.WH.W1.T3_whole

theorem SAP.P039.T4 : SAP.P039.T4WholeStatement := SAP.P039.WH.W1.T4_whole

theorem SAP.P039.T5 : T5Statement := by
  exact SAP.P039.Bridge.T5_correspondence

theorem SAP.P039.T6 : T6Statement := by
  exact SAP.P039.Bridge.T6_correspondence

theorem SAP.P039.T7 : SAP.P039.T7WholeStatement := SAP.P039.WH.W1.T7_whole
