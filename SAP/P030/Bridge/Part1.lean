import SAP.P030.Defs
import AronowAudit.P030.P030_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P030.Bridge
open scoped BigOperators
noncomputable section

/-- Preserve the finite support, masses, nonnegativity, and total mass. -/
def toLaw {A : Type*} (μ : FiniteLaw A) : AronowAudit.P030.FiniteLaw A :=
  ⟨μ.support, μ.mass, μ.nonneg, μ.total⟩

theorem probability_eq {A : Type*} (μ : FiniteLaw A) (P : A → Prop) :
    AronowAudit.P030.probability (toLaw μ) P = probability μ P := rfl

theorem lowerTail_eq {A : Type*} (μ : FiniteLaw A) (f : A → ℝ) (x : ℝ) :
    AronowAudit.P030.lowerTail (toLaw μ) f x = lowerTail μ f x := rfl

theorem upperTail_eq {A : Type*} (μ : FiniteLaw A) (f : A → ℝ) (x : ℝ) :
    AronowAudit.P030.upperTail (toLaw μ) f x = upperTail μ f x := rfl

theorem uniformLaw_eq {A : Type*} (Ω : Finset A) (hΩ : Ω.Nonempty) :
    toLaw (uniformLaw Ω hΩ) = AronowAudit.P030.uniformLaw Ω hΩ := rfl

/-- Every remaining correspondence is definitional equality, including proof fields. -/
theorem Assignment_eq : @AronowAudit.P030.Assignment = @SAP.P030.Assignment := rfl
theorem AssignmentSet_eq : @AronowAudit.P030.AssignmentSet = @SAP.P030.AssignmentSet := rfl
theorem FixedIndicator_eq : @AronowAudit.P030.FixedIndicator = @SAP.P030.FixedIndicator := rfl
theorem PotentialOutcomes_eq : @AronowAudit.P030.PotentialOutcomes = @SAP.P030.PotentialOutcomes := rfl
theorem treatment_eq : @AronowAudit.P030.treatment = @SAP.P030.treatment := rfl
theorem conditionalAssignments_eq : @AronowAudit.P030.conditionalAssignments = @SAP.P030.conditionalAssignments := rfl
theorem NoEffects_eq : @AronowAudit.P030.NoEffects = @SAP.P030.NoEffects := rfl
theorem NoInterference_eq : @AronowAudit.P030.NoInterference = @SAP.P030.NoInterference := rfl
theorem FixedOutcomeNull_eq : @AronowAudit.P030.FixedOutcomeNull = @SAP.P030.FixedOutcomeNull := rfl
theorem fixedOutcomes_eq : @AronowAudit.P030.fixedOutcomes = @SAP.P030.fixedOutcomes := rfl
theorem statistic_eq : @AronowAudit.P030.statistic = @SAP.P030.statistic := rfl
theorem referenceStatistic_eq : @AronowAudit.P030.referenceStatistic = @SAP.P030.referenceStatistic := rfl
theorem uniformProbability_eq : @AronowAudit.P030.uniformProbability = @SAP.P030.uniformProbability := rfl
theorem printedReject_eq : @AronowAudit.P030.printedReject = @SAP.P030.printedReject := rfl
theorem correctedReject_eq : @AronowAudit.P030.correctedReject = @SAP.P030.correctedReject := rfl
theorem twoTailP_eq : @AronowAudit.P030.twoTailP = @SAP.P030.twoTailP := rfl
theorem averageRank_eq : @AronowAudit.P030.averageRank = @SAP.P030.averageRank := rfl
theorem centeredRanks_eq : @AronowAudit.P030.centeredRanks = @SAP.P030.centeredRanks := rfl
theorem rankCross_eq : @AronowAudit.P030.rankCross = @SAP.P030.rankCross := rfl
theorem rankSquares_eq : @AronowAudit.P030.rankSquares = @SAP.P030.rankSquares := rfl
theorem spearman_eq : @AronowAudit.P030.spearman = @SAP.P030.spearman := rfl
theorem rankCov_eq : @AronowAudit.P030.rankCov = @SAP.P030.rankCov := rfl
theorem printedRho_eq : @AronowAudit.P030.printedRho = @SAP.P030.printedRho := rfl
theorem Nonconstant_eq : @AronowAudit.P030.Nonconstant = @SAP.P030.Nonconstant := rfl
theorem nearestDistance_eq : @AronowAudit.P030.nearestDistance = @SAP.P030.nearestDistance := rfl
theorem fiveX_eq : @AronowAudit.P030.fiveX = @SAP.P030.fiveX := rfl
theorem fiveS_eq : @AronowAudit.P030.fiveS = @SAP.P030.fiveS := rfl
theorem fiveY_eq : @AronowAudit.P030.fiveY = @SAP.P030.fiveY := rfl
theorem fiveAssignment_eq : @AronowAudit.P030.fiveAssignment = @SAP.P030.fiveAssignment := rfl
theorem fiveΩ_eq : @AronowAudit.P030.fiveΩ = @SAP.P030.fiveΩ := rfl
theorem fiveFixed_eq : @AronowAudit.P030.fiveFixed = @SAP.P030.fiveFixed := rfl
theorem fiveOutcomes_eq : @AronowAudit.P030.fiveOutcomes = @SAP.P030.fiveOutcomes := rfl
theorem fiveDistances_eq : @AronowAudit.P030.fiveDistances = @SAP.P030.fiveDistances := rfl
theorem fiveStatistic_eq : @AronowAudit.P030.fiveStatistic = @SAP.P030.fiveStatistic := rfl
theorem tenX_eq : @AronowAudit.P030.tenX = @SAP.P030.tenX := rfl
theorem tenS_eq : @AronowAudit.P030.tenS = @SAP.P030.tenS := rfl
theorem tenAssignment_eq : @AronowAudit.P030.tenAssignment = @SAP.P030.tenAssignment := rfl
theorem tenΩ_eq : @AronowAudit.P030.tenΩ = @SAP.P030.tenΩ := rfl
theorem tenYnull_eq : @AronowAudit.P030.tenYnull = @SAP.P030.tenYnull := rfl
theorem tenFixed_eq : @AronowAudit.P030.tenFixed = @SAP.P030.tenFixed := rfl
theorem tableTreatment_eq : @AronowAudit.P030.tableTreatment = @SAP.P030.tableTreatment := rfl
theorem tableΩ_eq : @AronowAudit.P030.tableΩ = @SAP.P030.tableΩ := rfl
theorem tableY_eq : @AronowAudit.P030.tableY = @SAP.P030.tableY := rfl
theorem tableDistances_eq : @AronowAudit.P030.tableDistances = @SAP.P030.tableDistances := rfl
theorem tableRho_eq : @AronowAudit.P030.tableRho = @SAP.P030.tableRho := rfl
theorem tableValues_eq : @AronowAudit.P030.tableValues = @SAP.P030.tableValues := rfl
theorem tenPsi_eq : @AronowAudit.P030.tenPsi = @SAP.P030.tenPsi := rfl
theorem tenTheta_eq : @AronowAudit.P030.tenTheta = @SAP.P030.tenTheta := rfl
theorem tenYexample_eq : @AronowAudit.P030.tenYexample = @SAP.P030.tenYexample := rfl
theorem tenG_eq : @AronowAudit.P030.tenG = @SAP.P030.tenG := rfl
theorem PrintedTwoTailedExactness_eq : @AronowAudit.P030.PrintedTwoTailedExactness = @SAP.P030.PrintedTwoTailedExactness := rfl
theorem partialRealQuotient_eq : @AronowAudit.P030.partialRealQuotient = @SAP.P030.partialRealQuotient := rfl
theorem inverseSquare_eq : @AronowAudit.P030.inverseSquare = @SAP.P030.inverseSquare := rfl
theorem inverseSquareIndirect_eq : @AronowAudit.P030.inverseSquareIndirect = @SAP.P030.inverseSquareIndirect := rfl
theorem inverseSquareSpatial_eq : @AronowAudit.P030.inverseSquareSpatial = @SAP.P030.inverseSquareSpatial := rfl
theorem completeAssignments_eq : @AronowAudit.P030.completeAssignments = @SAP.P030.completeAssignments := rfl
theorem proximalExposure_eq : @AronowAudit.P030.proximalExposure = @SAP.P030.proximalExposure := rfl
theorem uniformMean_eq : @AronowAudit.P030.uniformMean = @SAP.P030.uniformMean := rfl
theorem fixedSizeObjective_eq : @AronowAudit.P030.fixedSizeObjective = @SAP.P030.fixedSizeObjective := rfl

end
end SAP.P030.Bridge

