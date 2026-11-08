import SAP.P019b.WH.W1.Leaves
import SAP.P019b.WH.W1.P.T12_L1
import SAP.P019b.WH.W1.P.T12_L2
import SAP.P019b.WH.W1.P.T12_L3
import SAP.P019b.WH.W1.P.T12_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P019b.WH.W1.T21_whole : SAP.P019b.T21WholeStatement :=
  SAP.P019b.WH.W1.T21_assembly SAP.P019b.WH.W1.T12_L1_proof SAP.P019b.WH.W1.T12_L2_proof SAP.P019b.WH.W1.T12_L3_proof SAP.P019b.WH.W1.T12_L4_proof
