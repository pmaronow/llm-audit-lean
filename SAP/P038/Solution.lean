import SAP.P038.Defs
import SAP.P038.Bridge
import AronowAudit.P038.P038_EmpiricalNullCorrection

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem SAP.P038.T1 : SAP.P038.T1Statement := by
  simpa only [SAP.P038.T1Statement, SAP.P038.Bridge.referenceWeeks_eq,
    SAP.P038.Bridge.tailCount_eq, SAP.P038.Bridge.empiricalP_eq,
    SAP.P038.Bridge.roundsTo_eq, SAP.P038.Bridge.tailWeeks_eq,
    SAP.P038.Bridge.electionDayAdjustedP_eq] using
    AronowAudit.P038.corrected_election_hours_window
