import SAP.P012a.Bridge.Part1
import AronowAudit.P012.P012_Identification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.Bridge

open SAP.P012a
open scoped Classical
noncomputable section

@[simp] theorem hValues_eq (D : Data) : AronowAudit.P012.hValues (data D) = hValues D := by
  ext r
  simp only [AronowAudit.P012.hValues, hValues, Set.mem_ofPred_eq,
    exists_state, Compatible_eq, homophily_eq]

@[simp] theorem pValues_eq (D : Data) : AronowAudit.P012.pValues (data D) = pValues D := by
  ext r
  simp only [AronowAudit.P012.pValues, pValues, Set.mem_ofPred_eq,
    exists_state, Compatible_eq, preferential_eq]

@[simp] theorem full_h_eq (D : Data) (L U : ℝ) :
    AronowAudit.P012.FullHomophilyRegion (data D) L U = FullHomophilyRegion D L U := by
  simp only [AronowAudit.P012.FullHomophilyRegion, FullHomophilyRegion,
    forall_state, Compatible_eq, HomophilyDefined_eq, hValues_eq]

@[simp] theorem full_p_eq (D : Data) (L U : ℝ) :
    AronowAudit.P012.FullPreferentialRegion (data D) L U = FullPreferentialRegion D L U := by
  simp only [AronowAudit.P012.FullPreferentialRegion, FullPreferentialRegion,
    forall_state, Compatible_eq, PreferentialDefined_eq, pValues_eq]

@[simp] theorem point_eq (S : Set ℝ) : AronowAudit.P012.PointIdentified S = PointIdentified S := rfl

@[simp] theorem proposalData_eq : AronowAudit.P012.proposalData = data SAP.P012a.proposalData := rfl

@[simp] theorem proofStepData_eq : AronowAudit.P012.proofStepData = data SAP.P012a.proofStepData := rfl

@[simp] theorem a2Data_eq : AronowAudit.P012.a2Data = data SAP.P012a.a2Data := rfl

@[simp] theorem domainA_eq : AronowAudit.P012.domainA = data SAP.P012a.domainA := rfl

@[simp] theorem proposalDataB_eq : AronowAudit.P012.proposalDataB = data SAP.P012a.proposalDataB := rfl

@[simp] theorem cleanupData_eq : AronowAudit.P012.cleanupData = data SAP.P012a.cleanupData := rfl

@[simp] theorem emptyPoolData_eq : AronowAudit.P012.emptyPoolData = data SAP.P012a.emptyPoolData := rfl

@[simp] theorem proposalStart_eq : AronowAudit.P012.proposalStart = state SAP.P012a.proposalStart := rfl

@[simp] theorem result1BadStart_eq : AronowAudit.P012.result1BadStart = state SAP.P012a.result1BadStart := rfl

@[simp] theorem result1BadEnd_eq : AronowAudit.P012.result1BadEnd = state SAP.P012a.result1BadEnd := rfl

@[simp] theorem result2BadStart_eq : AronowAudit.P012.result2BadStart = state SAP.P012a.result2BadStart := rfl

@[simp] theorem result2BadEnd_eq : AronowAudit.P012.result2BadEnd = state SAP.P012a.result2BadEnd := rfl

@[simp] theorem proposalStartB_eq : AronowAudit.P012.proposalStartB = state SAP.P012a.proposalStartB := rfl

@[simp] theorem cleanupStart_eq : AronowAudit.P012.cleanupStart = state SAP.P012a.cleanupStart := rfl

@[simp] theorem proposalBad_eq (t : Bool) : AronowAudit.P012.proposalBad t = state (SAP.P012a.proposalBad t) := rfl

@[simp] theorem a2State_eq (t : Bool) : AronowAudit.P012.a2State t = state (SAP.P012a.a2State t) := rfl

@[simp] theorem proposalBadB_eq (t : Bool) : AronowAudit.P012.proposalBadB t = state (SAP.P012a.proposalBadB t) := rfl

@[simp] theorem dyad_eq (t1 t2 : Bool) : AronowAudit.P012.dyad t1 t2 = state (dyad t1 t2) := rfl

end
end SAP.P012a.Bridge
