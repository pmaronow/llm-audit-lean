import SAP.P005b.Defs
import AronowAudit.P005.P005_Formalization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005b.Bridge

/-- The project population has exactly the same three fixed arrays. -/
def toProject {n d : ℕ} (P : SAP.P005b.Population n d) :
    AronowAudit.P005.Population n d := ⟨P.x, P.yT, P.yC⟩

def fromProject {n d : ℕ} (P : AronowAudit.P005.Population n d) :
    SAP.P005b.Population n d := ⟨P.x, P.yT, P.yC⟩

theorem from_to {n d : ℕ} (P : SAP.P005b.Population n d) :
    fromProject (toProject P) = P := rfl

theorem to_from {n d : ℕ} (P : AronowAudit.P005.Population n d) :
    toProject (fromProject P) = P := rfl

def toArm (t : SAP.P005b.Arm) : AronowAudit.P005.Arm :=
  match t with | .treated => .treated | .control => .control

theorem armSet_eq {n : ℕ} (t : SAP.P005b.Arm) (S : Finset (Fin n)) :
    SAP.P005b.armSet t S = AronowAudit.P005.armSet (toArm t) S := by cases t <;> rfl

theorem armSize_eq (n m : ℕ) (t : SAP.P005b.Arm) :
    SAP.P005b.armSize n m t = AronowAudit.P005.armSize n m (toArm t) := by cases t <;> rfl

theorem design_eq : @SAP.P005b.design = @AronowAudit.P005.design := rfl

theorem control_eq : @SAP.P005b.control = @AronowAudit.P005.control := rfl

theorem mean_eq : @SAP.P005b.mean = @AronowAudit.P005.mean := rfl

theorem popMean_eq : @SAP.P005b.popMean = @AronowAudit.P005.popMean := rfl

theorem expectation_eq : @SAP.P005b.expectation = @AronowAudit.P005.expectation := rfl

theorem variance_eq : @SAP.P005b.variance = @AronowAudit.P005.variance := rfl

theorem probability_eq : @SAP.P005b.probability = @AronowAudit.P005.probability := rfl

theorem sampleCov_eq : @SAP.P005b.sampleCov = @AronowAudit.P005.sampleCov := rfl

theorem popCov_eq : @SAP.P005b.popCov = @AronowAudit.P005.popCov := rfl

theorem centered_eq : @SAP.P005b.centered = @AronowAudit.P005.centered := rfl

theorem covarianceBound_eq : @SAP.P005b.covarianceBound = @AronowAudit.P005.covarianceBound := rfl

theorem dot_eq : @SAP.P005b.dot = @AronowAudit.P005.dot := rfl

theorem pT_eq : @SAP.P005b.pT = @AronowAudit.P005.pT := rfl

theorem pC_eq : @SAP.P005b.pC = @AronowAudit.P005.pC := rfl

theorem NTTT_eq : @SAP.P005b.NTTT = @AronowAudit.P005.NTTT := rfl

theorem NCCC_eq : @SAP.P005b.NCCC = @AronowAudit.P005.NCCC := rfl

theorem NTTC_eq : @SAP.P005b.NTTC = @AronowAudit.P005.NTTC := rfl

theorem stochasticO_eq : @SAP.P005b.stochasticO = @AronowAudit.P005.stochasticO := rfl

theorem stochasticLittleO_eq : @SAP.P005b.stochasticLittleO = @AronowAudit.P005.stochasticLittleO := rfl

theorem indicator_eq : @SAP.P005b.indicator = @AronowAudit.P005.indicator := rfl

theorem repeatedPair_eq : @SAP.P005b.repeatedPair = @AronowAudit.P005.repeatedPair := rfl

theorem distinctTriple_eq : @SAP.P005b.distinctTriple = @AronowAudit.P005.distinctTriple := rfl

theorem observedResidual_eq : @SAP.P005b.observedResidual = @AronowAudit.P005.observedResidual := rfl

end SAP.P005b.Bridge
