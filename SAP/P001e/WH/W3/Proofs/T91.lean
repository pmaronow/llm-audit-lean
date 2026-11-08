import SAP.P001e.WH.W3.Leaves
import SAP.P001e.WH.W3.P.T91_L3V2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Existing assembly of the weaker cylinder-process diagnostic example. -/
theorem SAP.P001e.WH.W3.T91_whole : SAP.P001e.T91WholeStatement :=
  SAP.P001e.WH.W3.T91_assembly SAP.P001e.WH.W3.T91_L3V2_proof
