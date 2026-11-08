import SAP.P044.Defs
import AronowAudit.P044.P044_NetworkSpillovers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P044.Bridge

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- The four labels correspond in their printed order. -/
def labels : SAP.P044.Exposure ≃ AronowAudit.P044.Exposure where
  toFun a := match a with
    | .d11 => .d11 | .d10 => .d10 | .d01 => .d01 | .d00 => .d00
  invFun a := match a with
    | .d11 => .d11 | .d10 => .d10 | .d01 => .d01 | .d00 => .d00
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

@[simp] theorem labels_inj (a b : SAP.P044.Exposure) :
    labels a = labels b ↔ a = b := labels.injective.eq_iff

@[simp] theorem labels_eq (a : SAP.P044.Exposure) (b : AronowAudit.P044.Exposure) :
    labels a = b ↔ a = labels.symm b := labels.eq_symm_apply.symm

@[simp] theorem labels_d11 : labels SAP.P044.Exposure.d11 = .d11 := rfl
@[simp] theorem labels_d10 : labels SAP.P044.Exposure.d10 = .d10 := rfl
@[simp] theorem labels_d01 : labels SAP.P044.Exposure.d01 = .d01 := rfl
@[simp] theorem labels_d00 : labels SAP.P044.Exposure.d00 = .d00 := rfl
@[simp] theorem back_d11 : labels.symm AronowAudit.P044.Exposure.d11 = .d11 := rfl
@[simp] theorem back_d10 : labels.symm AronowAudit.P044.Exposure.d10 = .d10 := rfl
@[simp] theorem back_d01 : labels.symm AronowAudit.P044.Exposure.d01 = .d01 := rfl
@[simp] theorem back_d00 : labels.symm AronowAudit.P044.Exposure.d00 = .d00 := rfl

/-- The same finite probability masses and their two certification fields. -/
def toDesign {Ω : Type*} [Fintype Ω] (P : SAP.P044.FiniteDesign Ω) :
    AronowAudit.P044.FiniteDesign Ω := ⟨P.mass, P.nonneg, P.total⟩

@[simp] theorem design_mass {Ω : Type*} [Fintype Ω] (P : SAP.P044.FiniteDesign Ω) :
    (toDesign P).mass = P.mass := rfl

@[simp] theorem sap_forall (P : SAP.P044.Exposure → Prop) :
    (∀ a, P a) ↔ P .d11 ∧ P .d10 ∧ P .d01 ∧ P .d00 := by
  constructor
  · intro h; exact ⟨h _, h _, h _, h _⟩
  · rintro ⟨h1,h2,h3,h4⟩ a; cases a <;> assumption

@[simp] theorem project_forall (P : AronowAudit.P044.Exposure → Prop) :
    (∀ a, P a) ↔ P .d11 ∧ P .d10 ∧ P .d01 ∧ P .d00 := by
  constructor
  · intro h; exact ⟨h _, h _, h _, h _⟩
  · rintro ⟨h1,h2,h3,h4⟩ a; cases a <;> assumption

@[simp] theorem sum_back {K : Type*} [AddCommMonoid K] (h : SAP.P044.Exposure → K) :
    (∑ a : AronowAudit.P044.Exposure, h (labels.symm a)) = ∑ a, h a :=
  labels.symm.sum_comp h

@[simp] theorem peerCount_eq : @AronowAudit.P044.peerCount = @SAP.P044.peerCount := rfl

@[simp] theorem expect_eq : @AronowAudit.P044.expect = @SAP.P044.expect := rfl

@[simp] theorem designVariance_eq : @AronowAudit.P044.designVariance = @SAP.P044.designVariance := rfl

@[simp] theorem observed_eq : @AronowAudit.P044.observed = @SAP.P044.observed := rfl

@[simp] theorem tau_eq : @AronowAudit.P044.tau = @SAP.P044.tau := rfl

@[simp] theorem marginal_eq : @AronowAudit.P044.marginal = @SAP.P044.marginal := rfl

@[simp] theorem joint_eq : @AronowAudit.P044.joint = @SAP.P044.joint := rfl

@[simp] theorem htTerm_eq : @AronowAudit.P044.htTerm = @SAP.P044.htTerm := rfl

@[simp] theorem htMean_eq : @AronowAudit.P044.htMean = @SAP.P044.htMean := rfl

@[simp] theorem htContrast_eq : @AronowAudit.P044.htContrast = @SAP.P044.htContrast := rfl

@[simp] theorem totalVarianceEstimate_eq : @AronowAudit.P044.totalVarianceEstimate = @SAP.P044.totalVarianceEstimate := rfl

@[simp] theorem totalCovarianceEstimate_eq : @AronowAudit.P044.totalCovarianceEstimate = @SAP.P044.totalCovarianceEstimate := rfl

@[simp] theorem varianceEstimate_eq : @AronowAudit.P044.varianceEstimate = @SAP.P044.varianceEstimate := rfl

@[simp] theorem zeroSurplus_eq : @AronowAudit.P044.zeroSurplus = @SAP.P044.zeroSurplus := rfl

@[simp] theorem commonSupport_eq : @AronowAudit.P044.commonSupport = @SAP.P044.commonSupport := rfl

@[simp] theorem insertOwn_eq : @AronowAudit.P044.insertOwn = @SAP.P044.insertOwn := rfl

@[simp] theorem NoInterference_eq : @AronowAudit.P044.NoInterference = @SAP.P044.NoInterference := rfl

@[simp] theorem Interference_eq : @AronowAudit.P044.Interference = @SAP.P044.Interference := rfl

@[simp] theorem completeProfiles_eq : @AronowAudit.P044.completeProfiles = @SAP.P044.completeProfiles := rfl

@[simp] theorem starAdj_eq : @AronowAudit.P044.starAdj = @SAP.P044.starAdj := rfl

@[simp] theorem starAssignments_eq : @AronowAudit.P044.starAssignments = @SAP.P044.starAssignments := rfl

@[simp] theorem cycle8Adj_eq : @AronowAudit.P044.cycle8Adj = @SAP.P044.cycle8Adj := rfl

@[simp] theorem cycle8Assignments_eq : @AronowAudit.P044.cycle8Assignments = @SAP.P044.cycle8Assignments := rfl

@[simp] theorem exposureCount_eq : @AronowAudit.P044.exposureCount = @SAP.P044.exposureCount := rfl

@[simp] theorem jointCount_eq : @AronowAudit.P044.jointCount = @SAP.P044.jointCount := rfl

@[simp] theorem smoothedWeight_eq : @AronowAudit.P044.smoothedWeight = @SAP.P044.smoothedWeight := rfl

@[simp] theorem smoothedJoint_eq : @AronowAudit.P044.smoothedJoint = @SAP.P044.smoothedJoint := rfl

@[simp] theorem degree_eq : @AronowAudit.P044.degree = @SAP.P044.degree := rfl

@[simp] theorem twoWalkDegree_eq : @AronowAudit.P044.twoWalkDegree = @SAP.P044.twoWalkDegree := rfl

@[simp] theorem degreeScale_eq : @AronowAudit.P044.degreeScale = @SAP.P044.degreeScale := rfl

@[simp] theorem baseline_eq : @AronowAudit.P044.baseline = @SAP.P044.baseline := rfl

@[simp] theorem normalPair_eq : @AronowAudit.P044.normalPair = @SAP.P044.normalPair := rfl

@[simp] theorem baselineLaw_eq : @AronowAudit.P044.baselineLaw = @SAP.P044.baselineLaw := rfl

@[simp] theorem halfNormalLaw_eq : @AronowAudit.P044.halfNormalLaw = @SAP.P044.halfNormalLaw := rfl

@[simp] theorem blockEdgeProbability_eq : @AronowAudit.P044.blockEdgeProbability = @SAP.P044.blockEdgeProbability := rfl

@[simp] theorem withinEdges_eq : @AronowAudit.P044.withinEdges = @SAP.P044.withinEdges := rfl

@[simp] theorem normalPopulation_eq : @AronowAudit.P044.normalPopulation = @SAP.P044.normalPopulation := rfl

@[simp] theorem generatedBaselines_eq : @AronowAudit.P044.generatedBaselines = @SAP.P044.generatedBaselines := rfl

@[simp] theorem standardNormalCDF_eq : @AronowAudit.P044.standardNormalCDF = @SAP.P044.standardNormalCDF := rfl

@[simp] theorem cliquePairs_eq : @AronowAudit.P044.cliquePairs = @SAP.P044.cliquePairs := rfl

@[simp] theorem cliqueAssignments_eq : @AronowAudit.P044.cliqueAssignments = @SAP.P044.cliqueAssignments := rfl

@[simp] theorem cliqueAdj_eq : @AronowAudit.P044.cliqueAdj = @SAP.P044.cliqueAdj := rfl

@[simp] theorem retainedAssignments_eq : @AronowAudit.P044.retainedAssignments = @SAP.P044.retainedAssignments := rfl

@[simp] theorem cliqueJointMass_eq : @AronowAudit.P044.cliqueJointMass = @SAP.P044.cliqueJointMass := rfl

@[simp] theorem cliqueObservationMass_eq : @AronowAudit.P044.cliqueObservationMass = @SAP.P044.cliqueObservationMass := rfl

end
end SAP.P044.Bridge
