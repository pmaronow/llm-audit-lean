import SAP.P042.Defs
import AronowAudit.P042.P042_Turnout
import AronowAudit.P041.Wave1.Gap.GP041P042P045B2
import AronowAudit.P042.Wave1.Gap.GLP041P042P045P042B1
import AronowAudit.P042.Wave1.PrintedPoolingVariance
import AronowAudit.P042.Wave1.PrintedComparisonVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042.Bridge

noncomputable section
open SAP.P042 Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

theorem precisionWeight_eq : @SAP.P042.precisionWeight = @AronowAudit.P042.precisionWeight := rfl

theorem totalWeight_eq : @SAP.P042.totalWeight = @AronowAudit.P042.totalWeight := rfl

theorem normalizedWeight_eq : @SAP.P042.normalizedWeight = @AronowAudit.P042.normalizedWeight := rfl

theorem pooled_eq : @SAP.P042.pooled = @AronowAudit.P042.pooled := rfl

theorem diagonalVariance_eq : @SAP.P042.diagonalVariance = @AronowAudit.P042.diagonalVariance := rfl

theorem covarianceForm_eq : @SAP.P042.covarianceForm = @AronowAudit.P042.covarianceForm := rfl

theorem offDiagonal_eq : @SAP.P042.offDiagonal = @AronowAudit.P042.offDiagonal := rfl

theorem subsetWeight_eq : @SAP.P042.subsetWeight = @AronowAudit.P042.subsetWeight := rfl

theorem armSampleMean_eq : @SAP.P042.armSampleMean = @AronowAudit.P042.armSampleMean := rfl

theorem effectCorrelation_eq : @SAP.P042.effectCorrelation = @AronowAudit.P042.effectCorrelation := rfl

theorem finiteExpectation_eq : @SAP.P042.finiteExpectation = @AronowAudit.P042.finiteExpectation := rfl

theorem finiteCovariance_eq : @SAP.P042.finiteCovariance = @AronowAudit.P042.finiteCovariance := rfl

theorem completeThreeAllocations_eq : @SAP.P042.completeThreeAllocations = @AronowAudit.P042.completeThreeAllocations := rfl

theorem populationMean_eq : @SAP.P042.populationMean = @AronowAudit.P042.populationMean := rfl

theorem populationCovariance_eq : @SAP.P042.populationCovariance = @AronowAudit.P042.populationCovariance := rfl

theorem randomizedArmMean_eq : @SAP.P042.randomizedArmMean = @AronowAudit.P042.randomizedArmMean := rfl

theorem rationalMean_eq : @SAP.P042.rationalMean = @AronowAudit.P042.rationalMean := rfl

theorem rationalVariance_eq : @SAP.P042.rationalVariance = @AronowAudit.P042.rationalVariance := rfl

theorem rationalCovariance_eq : @SAP.P042.rationalCovariance = @AronowAudit.P042.rationalCovariance := rfl

theorem sixOutcome_eq : @SAP.P042.sixOutcome = @AronowAudit.P042.sixOutcome := rfl

theorem sixAllocations_eq : @SAP.P042.sixAllocations = @AronowAudit.P042.sixAllocations := rfl

theorem sixControl_eq : @SAP.P042.sixControl = @AronowAudit.P042.sixControl := rfl

theorem sixGroupMean_eq : @SAP.P042.sixGroupMean = @AronowAudit.P042.sixGroupMean := rfl

theorem sixD1_eq : @SAP.P042.sixD1 = @AronowAudit.P042.sixD1 := rfl

theorem sixD2_eq : @SAP.P042.sixD2 = @AronowAudit.P042.sixD2 := rfl

theorem binomialD1_eq : @SAP.P042.binomialD1 = @AronowAudit.P042.binomialD1 := rfl

theorem binomialD2_eq : @SAP.P042.binomialD2 = @AronowAudit.P042.binomialD2 := rfl

theorem binomialPooled_eq : @SAP.P042.binomialPooled = @AronowAudit.P042.binomialPooled := rfl

theorem coversZero_eq : @SAP.P042.coversZero = @AronowAudit.P042.coversZero := rfl

theorem roboEffects_eq : @SAP.P042.roboEffects = @AronowAudit.P042.roboEffects := rfl

theorem roboSE_eq : @SAP.P042.roboSE = @AronowAudit.P042.roboSE := rfl

theorem roboVariances_eq : @SAP.P042.roboVariances = @AronowAudit.P042.roboVariances := rfl

theorem roboFixedMean_eq : @SAP.P042.roboFixedMean = @AronowAudit.P042.roboFixedMean := rfl

theorem roboFixedVariance_eq : @SAP.P042.roboFixedVariance = @AronowAudit.P042.roboFixedVariance := rfl

theorem roboQ_eq : @SAP.P042.roboQ = @AronowAudit.P042.roboQ := rfl

theorem roboC_eq : @SAP.P042.roboC = @AronowAudit.P042.roboC := rfl

theorem roboTauSq_eq : @SAP.P042.roboTauSq = @AronowAudit.P042.roboTauSq := rfl

theorem roboRandomVariances_eq : @SAP.P042.roboRandomVariances = @AronowAudit.P042.roboRandomVariances := rfl

theorem roboRandomMean_eq : @SAP.P042.roboRandomMean = @AronowAudit.P042.roboRandomMean := rfl

theorem roboRandomVariance_eq : @SAP.P042.roboRandomVariance = @AronowAudit.P042.roboRandomVariance := rfl

theorem completeAssignments_eq : @SAP.P042.completeAssignments = @AronowAudit.P042.completeAssignments := rfl

theorem assignedTreatmentMean_eq : @SAP.P042.assignedTreatmentMean = @AronowAudit.P042.assignedTreatmentMean := rfl

theorem assignedControlMean_eq : @SAP.P042.assignedControlMean = @AronowAudit.P042.assignedControlMean := rfl

theorem assignedOutcome_eq : @SAP.P042.assignedOutcome = @AronowAudit.P042.assignedOutcome := rfl

theorem complierCount_eq : @SAP.P042.complierCount = @AronowAudit.P042.complierCount := rfl

theorem complierShare_eq : @SAP.P042.complierShare = @AronowAudit.P042.complierShare := rfl

theorem complierEffect_eq : @SAP.P042.complierEffect = @AronowAudit.P042.complierEffect := rfl

theorem assignmentEffect_eq : @SAP.P042.assignmentEffect = @AronowAudit.P042.assignmentEffect := rfl

theorem contactedOutcome_eq : @SAP.P042.contactedOutcome = @AronowAudit.P042.contactedOutcome := rfl

theorem assignedContactRate_eq : @SAP.P042.assignedContactRate = @AronowAudit.P042.assignedContactRate := rfl

/-- Replace the computational coefficient by Mathlib's binomial coefficient. -/
theorem binomialMass_eq : SAP.P042.binomialMass = AronowAudit.P042.binomialMass := by
  funext n x
  simp only [SAP.P042.binomialMass, AronowAudit.P042.binomialMass,
    AronowAudit.P042.exactChoose_eq]

theorem binomialArmExpectation_eq :
    SAP.P042.binomialArmExpectation = AronowAudit.P042.binomialArmExpectation := by
  funext f
  simp only [SAP.P042.binomialArmExpectation, AronowAudit.P042.binomialArmExpectation,
    binomialMass_eq]

theorem binomialTripleExpectation_eq :
    SAP.P042.binomialTripleExpectation = AronowAudit.P042.binomialTripleExpectation := by
  funext f
  simp only [SAP.P042.binomialTripleExpectation, AronowAudit.P042.binomialTripleExpectation,
    binomialMass_eq]

theorem binomialTripleVariance_eq :
    SAP.P042.binomialTripleVariance = AronowAudit.P042.binomialTripleVariance := by
  funext f
  simp only [SAP.P042.binomialTripleVariance, AronowAudit.P042.binomialTripleVariance,
    binomialTripleExpectation_eq]

theorem binomialTripleCovariance_eq :
    SAP.P042.binomialTripleCovariance = AronowAudit.P042.binomialTripleCovariance := by
  funext f g
  simp only [SAP.P042.binomialTripleCovariance, AronowAudit.P042.binomialTripleCovariance,
    binomialTripleExpectation_eq]

theorem coverageCount_eq : SAP.P042.coverageCount = AronowAudit.P042.coverageCount := by
  funext r
  simp only [SAP.P042.coverageCount, AronowAudit.P042.coverageCount,
    AronowAudit.P042.exactChoose_eq]

theorem binomialCoverage_eq : SAP.P042.binomialCoverage = AronowAudit.P042.binomialCoverage := by
  funext r
  simp only [SAP.P042.binomialCoverage, AronowAudit.P042.binomialCoverage, coverageCount_eq]

end
end SAP.P042.Bridge
