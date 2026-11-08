import SAP.P005b.WH.W1.Leaves
import SAP.P005b.WH.W1.P.T21_L1
import SAP.P005b.WH.W1.P.T21_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P005b.WH.W1.T21_whole : SAP.P005b.T21WholeStatement :=
  SAP.P005b.WH.W1.T21_assembly SAP.P005b.WH.W1.T21_L1_proof SAP.P005b.WH.W1.T21_L2_proof
