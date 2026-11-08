import SAP.P012b.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012b.Bridge

/-- The SAP scalar objective agrees with the credited project's formula. -/
theorem annealingObjective_eq (ε h p : ℝ) :
    annealingObjective ε h p = AronowAudit.P012.objective ε h p := rfl

end SAP.P012b.Bridge
