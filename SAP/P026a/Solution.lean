import SAP.P026a.WH.W2.Proofs.T7
import SAP.P026a.WH.W1.Proofs.T6
import SAP.P026a.WH.W1.Proofs.T5
import SAP.P026a.WH.W1.Proofs.T4
import SAP.P026a.WH.W1.Proofs.T1
import SAP.P026a.WH.W1.Proofs.T9
import SAP.P026a.Defs
import SAP.P026a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a

theorem T1 : SAP.P026a.T1WholeStatement := SAP.P026a.WH.W1.T1_whole

theorem T2 : T2Statement := Bridge.target2

theorem T3 : T3Statement := Bridge.target3

theorem T4 : SAP.P026a.T4WholeStatement := SAP.P026a.WH.W1.T4_whole

theorem T5 : SAP.P026a.T5WholeStatement := SAP.P026a.WH.W1.T5_whole

theorem T6 : SAP.P026a.T6WholeStatement := SAP.P026a.WH.W1.T6_whole

theorem T7 : SAP.P026a.T7WholeStatement := SAP.P026a.WH.W2.T7_whole

theorem T8 : T8Statement := Bridge.target8

theorem T9 : SAP.P026a.T9WholeStatement := SAP.P026a.WH.W1.T9_whole

theorem T10 : T10Statement := Bridge.target10

theorem T11 : T11Statement := Bridge.target11

theorem T12 : T12Statement := Bridge.target12

end SAP.P026a
