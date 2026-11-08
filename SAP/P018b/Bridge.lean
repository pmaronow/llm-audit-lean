import SAP.P018b.Defs
import AronowAudit.P018.P018_Audit
import AronowAudit.P018.P018_PaperDomains
import AronowAudit.P018.Wave1.Gap.GLP0181B2
import AronowAudit.P018.Wave1.Gap.TailBRareLimits
import AronowAudit.P018.Wave1.Gap.GP0181B3
import AronowAudit.P018.Wave1.Gap.DecideC
import AronowAudit.P018.Wave1.PrintedLemma1
import AronowAudit.P018.Wave1.Gap.GLP0181B4
import AronowAudit.P018.Wave1.PrintedScalarCorollaries

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b.Bridge
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

/-! The SAP finite sums and analytic predicates have the same bodies. -/

theorem Vec_eq : @SAP.P018b.Vec = @AronowAudit.P018.Vec := rfl

theorem Mat_eq : @SAP.P018b.Mat = @AronowAudit.P018.Mat := rfl

theorem outer_eq : @SAP.P018b.outer = @AronowAudit.P018.outer := rfl

theorem dot_eq : @SAP.P018b.dot = @AronowAudit.P018.dot := rfl

theorem dyads_eq : @SAP.P018b.dyads = @AronowAudit.P018.dyads := rfl

theorem Dyad_eq : @SAP.P018b.Dyad = @AronowAudit.P018.Dyad := rfl

theorem members_eq : @SAP.P018b.members = @AronowAudit.P018.members := rfl

theorem neighbors_eq : @SAP.P018b.neighbors = @AronowAudit.P018.neighbors := rfl

theorem overlap_eq : @SAP.P018b.overlap = @AronowAudit.P018.overlap := rfl

theorem sandwich_eq : @SAP.P018b.sandwich = @AronowAudit.P018.sandwich := rfl

theorem score_eq : @SAP.P018b.score = @AronowAudit.P018.score := rfl

theorem meat_eq : @SAP.P018b.meat = @AronowAudit.P018.meat := rfl

theorem unitScore_eq : @SAP.P018b.unitScore = @AronowAudit.P018.unitScore := rfl

theorem dyadMeat_eq : @SAP.P018b.dyadMeat = @AronowAudit.P018.dyadMeat := rfl

theorem individualMeat_eq : @SAP.P018b.individualMeat = @AronowAudit.P018.individualMeat := rfl

theorem nonincidentMeat_eq : @SAP.P018b.nonincidentMeat = @AronowAudit.P018.nonincidentMeat := rfl

theorem clusterMeat_eq : @SAP.P018b.clusterMeat = @AronowAudit.P018.clusterMeat := rfl

theorem orderedNonincidentMeat_eq : @SAP.P018b.orderedNonincidentMeat = @AronowAudit.P018.orderedNonincidentMeat := rfl

theorem orderedClusterMeat_eq : @SAP.P018b.orderedClusterMeat = @AronowAudit.P018.orderedClusterMeat := rfl

theorem crossUnitMeat_eq : @SAP.P018b.crossUnitMeat = @AronowAudit.P018.crossUnitMeat := rfl

theorem incidentDiagonalMeat_eq : @SAP.P018b.incidentDiagonalMeat = @AronowAudit.P018.incidentDiagonalMeat := rfl

theorem sixMembers_eq : @SAP.P018b.sixMembers = @AronowAudit.P018.sixMembers := rfl

theorem orderedWitness_eq : @SAP.P018b.orderedWitness = @AronowAudit.P018.orderedWitness := rfl

theorem sampleGram_eq : @SAP.P018b.sampleGram = @AronowAudit.P018.sampleGram := rfl

theorem sampleOLS_eq : @SAP.P018b.sampleOLS = @AronowAudit.P018.sampleOLS := rfl

theorem fittedResidual_eq : @SAP.P018b.fittedResidual = @AronowAudit.P018.fittedResidual := rfl

theorem sampleVariance_eq : @SAP.P018b.sampleVariance = @AronowAudit.P018.sampleVariance := rfl

theorem negativeX_eq : @SAP.P018b.negativeX = @AronowAudit.P018.negativeX := rfl

theorem negativeY_eq : @SAP.P018b.negativeY = @AronowAudit.P018.negativeY := rfl

theorem negativeE_eq : @SAP.P018b.negativeE = @AronowAudit.P018.negativeE := rfl

theorem standardError_eq : @SAP.P018b.standardError = @AronowAudit.P018.standardError := rfl

theorem tableSE_eq : @SAP.P018b.tableSE = @AronowAudit.P018.tableSE := rfl

theorem expit_eq : @SAP.P018b.expit = @AronowAudit.P018.expit := rfl

theorem logisticScore_eq : @SAP.P018b.logisticScore = @AronowAudit.P018.logisticScore := rfl

theorem logisticBread_eq : @SAP.P018b.logisticBread = @AronowAudit.P018.logisticBread := rfl

theorem logLikelihood_eq : @SAP.P018b.logLikelihood = @AronowAudit.P018.logLikelihood := rfl

theorem logisticNegativeJacobian_eq : @SAP.P018b.logisticNegativeJacobian = @AronowAudit.P018.logisticNegativeJacobian := rfl

theorem meanVec_eq : @SAP.P018b.meanVec = @AronowAudit.P018.meanVec := rfl

theorem meanMat_eq : @SAP.P018b.meanMat = @AronowAudit.P018.meanMat := rfl

theorem covMat_eq : @SAP.P018b.covMat = @AronowAudit.P018.covMat := rfl

theorem varMat_eq : @SAP.P018b.varMat = @AronowAudit.P018.varMat := rfl

theorem inProbability_eq : @SAP.P018b.inProbability = @AronowAudit.P018.inProbability := rfl

theorem weakLimit_eq : @SAP.P018b.weakLimit = @AronowAudit.P018.weakLimit := rfl

theorem centeredNormalLaw_eq : @SAP.P018b.centeredNormalLaw = @AronowAudit.P018.centeredNormalLaw := rfl

theorem firstUnit_eq : @SAP.P018b.firstUnit = @AronowAudit.P018.firstUnit := rfl

theorem secondUnit_eq : @SAP.P018b.secondUnit = @AronowAudit.P018.secondUnit := rfl

theorem Dreal_eq : @SAP.P018b.Dreal = @AronowAudit.P018.Dreal := rfl

theorem fairLaw_eq : @SAP.P018b.fairLaw = @AronowAudit.P018.fairLaw := rfl

theorem signValue_eq : @SAP.P018b.signValue = @AronowAudit.P018.signValue := rfl

theorem finiteUnitLaw_eq : @SAP.P018b.finiteUnitLaw = @AronowAudit.P018.finiteUnitLaw := rfl

theorem heterogeneityTable_eq : @SAP.P018b.heterogeneityTable = @AronowAudit.P018.heterogeneityTable := rfl

theorem uiSquares_eq : @SAP.P018b.uiSquares = @AronowAudit.P018.uiSquares := rfl

theorem SimulationIndex_eq : @SAP.P018b.SimulationIndex = @AronowAudit.P018.SimulationIndex := rfl

theorem simulationLaw_eq : @SAP.P018b.simulationLaw = @AronowAudit.P018.simulationLaw := rfl

theorem simulationX_eq : @SAP.P018b.simulationX = @AronowAudit.P018.simulationX := rfl

theorem simulationError_eq : @SAP.P018b.simulationError = @AronowAudit.P018.simulationError := rfl

theorem endpointZ1_eq : @SAP.P018b.endpointZ1 = @AronowAudit.P018.endpointZ1 := rfl

theorem endpointZ2_eq : @SAP.P018b.endpointZ2 = @AronowAudit.P018.endpointZ2 := rfl

theorem sharedCov_eq : @SAP.P018b.sharedCov = @AronowAudit.P018.sharedCov := rfl

theorem twoRoleCov_eq : @SAP.P018b.twoRoleCov = @AronowAudit.P018.twoRoleCov := rfl

theorem genericScoreMeat_eq : @SAP.P018b.genericScoreMeat = @AronowAudit.P018.genericScoreMeat := rfl

/-- Field adapter; the unit space and its measurable structure are unchanged. -/
def toKernel {U : Type*} [MeasurableSpace U] {k : ℕ} (K : SAP.P018b.Kernel U k) :
    AronowAudit.P018.Kernel U k := ⟨K.μ, K.X, K.Y⟩

def fromKernel {U : Type*} [MeasurableSpace U] {k : ℕ} (K : AronowAudit.P018.Kernel U k) :
    SAP.P018b.Kernel U k := ⟨K.μ, K.X, K.Y⟩

theorem kernel_roundtrip {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : AronowAudit.P018.Kernel U k) : toKernel (fromKernel K) = K := rfl

theorem unitSampleLaw_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (K : SAP.P018b.Kernel U k) :
    SAP.P018b.unitSampleLaw K = AronowAudit.P018.unitSampleLaw (toKernel K) := rfl

theorem populationGram_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (K : SAP.P018b.Kernel U k) :
    SAP.P018b.populationGram K = AronowAudit.P018.populationGram (toKernel K) := rfl

theorem populationBeta_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (K : SAP.P018b.Kernel U k) :
    SAP.P018b.populationBeta K = AronowAudit.P018.populationBeta (toKernel K) := rfl

theorem populationResidual_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (K : SAP.P018b.Kernel U k) :
    SAP.P018b.populationResidual K = AronowAudit.P018.populationResidual (toKernel K) := rfl

theorem design_eq {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : SAP.P018b.Kernel U k) :
    @SAP.P018b.design U _ k N K = @AronowAudit.P018.design U _ k N (toKernel K) := rfl

theorem response_eq {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : SAP.P018b.Kernel U k) :
    @SAP.P018b.response U _ k N K = @AronowAudit.P018.response U _ k N (toKernel K) := rfl

theorem epsilon_eq {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : SAP.P018b.Kernel U k) :
    @SAP.P018b.epsilon U _ k N K = @AronowAudit.P018.epsilon U _ k N (toKernel K) := rfl

theorem populationScore_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (K : SAP.P018b.Kernel U k) :
    SAP.P018b.populationScore K = AronowAudit.P018.populationScore (toKernel K) := rfl

theorem scoreSum_eq {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : SAP.P018b.Kernel U k) :
    @SAP.P018b.scoreSum U _ k N K = @AronowAudit.P018.scoreSum U _ k N (toKernel K) := rfl

theorem Standing_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (K : SAP.P018b.Kernel U k) :
    SAP.P018b.Standing K = AronowAudit.P018.Standing (toKernel K) := rfl

theorem Proposition1Extra_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (K : SAP.P018b.Kernel U k) :
    SAP.P018b.Proposition1Extra K = AronowAudit.P018.Proposition1Extra (toKernel K) := rfl

theorem SampleRank_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (K : SAP.P018b.Kernel U k) :
    SAP.P018b.SampleRank K = AronowAudit.P018.SampleRank (toKernel K) := rfl

theorem trueTarget_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (K : SAP.P018b.Kernel U k) :
    SAP.P018b.trueTarget K = AronowAudit.P018.trueTarget (toKernel K) := rfl

theorem designSigma_eq {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : SAP.P018b.Kernel U k) :
    @SAP.P018b.designSigma U _ k N K = @AronowAudit.P018.designSigma U _ k N (toKernel K) := rfl

theorem conditionalResidualMean_eq {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : SAP.P018b.Kernel U k) :
    @SAP.P018b.conditionalResidualMean U _ k N K = @AronowAudit.P018.conditionalResidualMean U _ k N (toKernel K) := rfl

theorem conditionalResidualCov_eq {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : SAP.P018b.Kernel U k) :
    @SAP.P018b.conditionalResidualCov U _ k N K = @AronowAudit.P018.conditionalResidualCov U _ k N (toKernel K) := rfl

theorem conditionalTerm_eq {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : SAP.P018b.Kernel U k) :
    @SAP.P018b.conditionalTerm U _ k N K = @AronowAudit.P018.conditionalTerm U _ k N (toKernel K) := rfl

theorem printedSigma_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (K : SAP.P018b.Kernel U k) :
    SAP.P018b.printedSigma K = AronowAudit.P018.printedSigma (toKernel K) := rfl

theorem projection_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (K : SAP.P018b.Kernel U k) :
    SAP.P018b.projection K = AronowAudit.P018.projection (toKernel K) := rfl

theorem projectionGamma_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (K : SAP.P018b.Kernel U k) :
    SAP.P018b.projectionGamma K = AronowAudit.P018.projectionGamma (toKernel K) := rfl

theorem limitingTarget_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (K : SAP.P018b.Kernel U k) :
    SAP.P018b.limitingTarget K = AronowAudit.P018.limitingTarget (toKernel K) := rfl

theorem coefficientError_eq {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : SAP.P018b.Kernel U k) :
    @SAP.P018b.coefficientError U _ k N K = @AronowAudit.P018.coefficientError U _ k N (toKernel K) := rfl

theorem finiteNegativeKernel_eq : toKernel SAP.P018b.finiteNegativeKernel =
    AronowAudit.P018.finiteNegativeKernel := rfl

theorem signKernel_eq : toKernel SAP.P018b.signKernel = AronowAudit.P018.signKernel := rfl

/-- Repeated-record adapter; the dependent record index has the same definition. -/
def toRepeated {U : Type*} [MeasurableSpace U] {k : ℕ} (R : SAP.P018b.RepeatedKernel U k) :
    AronowAudit.P018.RepeatedKernel U k := ⟨R.μ, R.T, R.X, R.Y⟩

def fromRepeated {U : Type*} [MeasurableSpace U] {k : ℕ} (R : AronowAudit.P018.RepeatedKernel U k) :
    SAP.P018b.RepeatedKernel U k := ⟨R.μ, R.T, R.X, R.Y⟩

theorem repeated_roundtrip {U : Type*} [MeasurableSpace U] {k : ℕ}
    (R : AronowAudit.P018.RepeatedKernel U k) : toRepeated (fromRepeated R) = R := rfl

theorem repeatedLaw_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (R : SAP.P018b.RepeatedKernel U k) :
    SAP.P018b.repeatedLaw R = AronowAudit.P018.repeatedLaw (toRepeated R) := rfl

theorem repeatedL_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (R : SAP.P018b.RepeatedKernel U k) :
    SAP.P018b.repeatedL R = AronowAudit.P018.repeatedL (toRepeated R) := rfl

theorem repeatedBeta_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (R : SAP.P018b.RepeatedKernel U k) :
    SAP.P018b.repeatedBeta R = AronowAudit.P018.repeatedBeta (toRepeated R) := rfl

theorem RepeatedStanding_eq {U : Type*} [MeasurableSpace U] {k : ℕ} (R : SAP.P018b.RepeatedKernel U k) :
    SAP.P018b.RepeatedStanding R = AronowAudit.P018.RepeatedStanding (toRepeated R) := rfl

theorem repeatedX_eq {U : Type*} [MeasurableSpace U] {k N : ℕ} (R : SAP.P018b.RepeatedKernel U k) :
    @SAP.P018b.repeatedX U _ k N R = @AronowAudit.P018.repeatedX U _ k N (toRepeated R) := rfl

theorem repeatedY_eq {U : Type*} [MeasurableSpace U] {k N : ℕ} (R : SAP.P018b.RepeatedKernel U k) :
    @SAP.P018b.repeatedY U _ k N R = @AronowAudit.P018.repeatedY U _ k N (toRepeated R) := rfl

theorem repeatedGram_eq {U : Type*} [MeasurableSpace U] {k N : ℕ} (R : SAP.P018b.RepeatedKernel U k) :
    @SAP.P018b.repeatedGram U _ k N R = @AronowAudit.P018.repeatedGram U _ k N (toRepeated R) := rfl

theorem repeatedOLS_eq {U : Type*} [MeasurableSpace U] {k N : ℕ} (R : SAP.P018b.RepeatedKernel U k) :
    @SAP.P018b.repeatedOLS U _ k N R = @AronowAudit.P018.repeatedOLS U _ k N (toRepeated R) := rfl

theorem repeatedBlockScore_eq {U : Type*} [MeasurableSpace U] {k N : ℕ} (R : SAP.P018b.RepeatedKernel U k) :
    @SAP.P018b.repeatedBlockScore U _ k N R = @AronowAudit.P018.repeatedBlockScore U _ k N (toRepeated R) := rfl

theorem repeatedVariance_eq {U : Type*} [MeasurableSpace U] {k N : ℕ} (R : SAP.P018b.RepeatedKernel U k) :
    @SAP.P018b.repeatedVariance U _ k N R = @AronowAudit.P018.repeatedVariance U _ k N (toRepeated R) := rfl

end SAP.P018b.Bridge
