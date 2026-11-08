import SAP.P054.Defs
import AronowAudit.P054.P054_Reconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P054.Bridge

variable {I : Type*} [Fintype I]

theorem groupCount_eq (d : I → ℝ) :
    SAP.P054.groupCount d = AronowAudit.P054.groupCount d := rfl

theorem groupWeight_eq (d w : I → ℝ) :
    SAP.P054.groupWeight d w = AronowAudit.P054.groupWeight d w := rfl

theorem weightedProportion_eq (d w y : I → ℝ) :
    SAP.P054.weightedProportion d w y = AronowAudit.P054.weightedProportion d w y := rfl

theorem ratioResidual_eq (d w y : I → ℝ) (i : I) :
    SAP.P054.ratioResidual d w y i = AronowAudit.P054.ratioResidual d w y i := rfl

end SAP.P054.Bridge
