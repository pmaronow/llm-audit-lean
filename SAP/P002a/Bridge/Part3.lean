import SAP.P002a.Defs
import AronowAudit.P002.P002_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.Bridge
noncomputable section

/-! The standard normal absolute tail used by T7 has the same body as the project's. -/

theorem normalTail_eq : @SAP.P002a.normalTail = @AronowAudit.P002.normalTail := rfl

end
end SAP.P002a.Bridge
