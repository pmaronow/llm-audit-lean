import SAP.P010.Defs
import AronowAudit.P010.P010_Empirical
import AronowAudit.P010.P010_Population
import AronowAudit.P010.P010_Transport
import AronowAudit.P010.Wave1.Gap.GLP010P033B1
import AronowAudit.P010.Wave1.Gap.GLP010P033B2
import AronowAudit.P010.Wave1.Gap.GLP010P033B3
import AronowAudit.P010.Wave1.Gap.GLP010P033B4
import AronowAudit.P010.Wave1.Gap.GLP010P033B5
import AronowAudit.P010.Wave1.Gap.GP010P033B1b
import AronowAudit.P010.Wave1.PropositionOneElseTailC
import AronowAudit.P010.Wave1.PropositionOneFiniteTailC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P010.Bridge

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical Topology BigOperators

/-! Definitional correspondences for all SAP notions. -/

theorem sampleSize_eq : @SAP.P010.sampleSize = @AronowAudit.P010.armN := rfl

theorem failures_eq : @SAP.P010.failures = @AronowAudit.P010.armFailures := rfl

theorem passers_eq : @SAP.P010.passers = @AronowAudit.P010.armPassers := rfl

theorem preferCount_eq : @SAP.P010.preferCount = @AronowAudit.P010.preferenceOnes := rfl

theorem approveCount_eq : @SAP.P010.approveCount = @AronowAudit.P010.approvalOnes := rfl

theorem failureShare_eq : @SAP.P010.failureShare = @AronowAudit.P010.empiricalFailure := rfl

theorem trimShare_eq : @SAP.P010.trimShare = @AronowAudit.P010.empiricalTrim := rfl

theorem keptLower_eq : @SAP.P010.keptLower = @AronowAudit.P010.lowerRetained := rfl

theorem keptUpper_eq : @SAP.P010.keptUpper = @AronowAudit.P010.upperRetained := rfl

theorem sampleBounds_eq : @SAP.P010.sampleBounds = @AronowAudit.P010.empiricalBounds := rfl

theorem sampleInterval_eq : @SAP.P010.sampleInterval = @AronowAudit.P010.empiricalInterval := rfl

theorem minAlwaysShare_eq : @SAP.P010.minAlwaysShare = @AronowAudit.P010.empiricalAlwaysMass := rfl

theorem fractionalPreference_eq : @SAP.P010.fractionalPreference = @AronowAudit.P010.fractionalBounds := rfl

theorem propensity_eq : @SAP.P010.propensity = @AronowAudit.P010.studyPropensity := rfl

theorem odds_eq : @SAP.P010.odds = @AronowAudit.P010.printedOdds := rfl

theorem reverseOdds_eq : @SAP.P010.reverseOdds = @AronowAudit.P010.correctedOdds := rfl

theorem normalizeMass_eq : @SAP.P010.normalizeMass = @AronowAudit.P010.reweighted := rfl

theorem originalDistribution_eq : @SAP.P010.originalDistribution = @AronowAudit.P010.originalMass := rfl

theorem replicationDistribution_eq : @SAP.P010.replicationDistribution = @AronowAudit.P010.replicationMass := rfl

theorem cellPropensity_eq : @SAP.P010.cellPropensity = @AronowAudit.P010.examplePropensity := rfl

theorem sigmoid_eq : @SAP.P010.sigmoid = @AronowAudit.P010.logisticProbability := rfl

theorem normalizeDensity_eq : @SAP.P010.normalizeDensity = @AronowAudit.P010.reweightedDensity := rfl

theorem Population_eq : @SAP.P010.Population = @AronowAudit.P010.State := rfl

theorem potentialOutcome_eq : @SAP.P010.potentialOutcome = @AronowAudit.P010.potentialY := rfl

theorem potentialCheck_eq : @SAP.P010.potentialCheck = @AronowAudit.P010.potentialS := rfl

theorem arm_eq : @SAP.P010.arm = @AronowAudit.P010.assignment := rfl

theorem features_eq : @SAP.P010.features = @AronowAudit.P010.covariates := rfl

theorem response_eq : @SAP.P010.response = @AronowAudit.P010.observedY := rfl

theorem check_eq : @SAP.P010.check = @AronowAudit.P010.observedS := rfl

theorem allPass_eq : @SAP.P010.allPass = @AronowAudit.P010.alwaysPass := rfl

theorem sameCheck_eq : @SAP.P010.sameCheck = @AronowAudit.P010.commonStatus := rfl

theorem assigned_eq : @SAP.P010.assigned = @AronowAudit.P010.armEvent := rfl

theorem passed_eq : @SAP.P010.passed = @AronowAudit.P010.passEvent := rfl

theorem wouldPass_eq : @SAP.P010.wouldPass = @AronowAudit.P010.potentialPass := rfl

theorem meanOn_eq : @SAP.P010.meanOn = @AronowAudit.P010.eventMean := rfl

theorem randomAssignment_eq : @SAP.P010.randomAssignment = @AronowAudit.P010.Ignorability := rfl

theorem passRate_eq : @SAP.P010.passRate = @AronowAudit.P010.passingRate := rfl

theorem positivePassRates_eq : @SAP.P010.positivePassRates = @AronowAudit.P010.NonzeroPassing := rfl

theorem populationAssumptions_eq : @SAP.P010.populationAssumptions = @AronowAudit.P010.Assumptions := rfl

theorem covariateRandomAssignment_eq : @SAP.P010.covariateRandomAssignment = @AronowAudit.P010.CovariateIgnorability := rfl

theorem covariateBalance_eq : @SAP.P010.covariateBalance = @AronowAudit.P010.CovariateBalance := rfl

theorem conditionalLaw_eq : @SAP.P010.conditionalLaw = @AronowAudit.P010.eventLaw := rfl

theorem trimmingRatio_eq : @SAP.P010.trimmingRatio = @AronowAudit.P010.trimRatio := rfl

theorem passerDistribution_eq : @SAP.P010.passerDistribution = @AronowAudit.P010.passerLaw := rfl

theorem leftQuantile_eq : @SAP.P010.leftQuantile = @AronowAudit.P010.quantile := rfl

theorem realQuantile_eq : @SAP.P010.realQuantile = @AronowAudit.P010.quantileReal := rfl

theorem noAtoms_eq : @SAP.P010.noAtoms = @AronowAudit.P010.Atomless := rfl

theorem fullRealSupport_eq : @SAP.P010.fullRealSupport = @AronowAudit.P010.FullRealSupport := rfl

theorem allMoments_eq : @SAP.P010.allMoments = @AronowAudit.P010.AllMoments := rfl

theorem lowerEndpoint_eq : @SAP.P010.lowerEndpoint = @AronowAudit.P010.lowerBound := rfl

theorem upperEndpoint_eq : @SAP.P010.upperEndpoint = @AronowAudit.P010.upperBound := rfl

theorem compatiblePopulations_eq : @SAP.P010.compatiblePopulations = @AronowAudit.P010.Compatible := rfl

theorem compatibleMeans_eq : @SAP.P010.compatibleMeans = @AronowAudit.P010.identifiedMeans := rfl

theorem extendedCompatibleMeans_eq : @SAP.P010.extendedCompatibleMeans = @AronowAudit.P010.extendedMeans := rfl

theorem passerEssentialInf_eq : @SAP.P010.passerEssentialInf = @AronowAudit.P010.passerInf := rfl

theorem passerEssentialSup_eq : @SAP.P010.passerEssentialSup = @AronowAudit.P010.passerSup := rfl

theorem otherArmsPass_eq : @SAP.P010.otherArmsPass = @AronowAudit.P010.otherPass := rfl

theorem potentialTrimShare_eq : @SAP.P010.potentialTrimShare = @AronowAudit.P010.potentialTrim := rfl

theorem tailCoupling_eq : @SAP.P010.tailCoupling = @AronowAudit.P010.TailCoupling := rfl

theorem upperTailMean_eq : @SAP.P010.upperTailMean = @AronowAudit.P010.tailUpper := rfl

theorem finitePopulation_eq : @SAP.P010.finitePopulation = @AronowAudit.P010.finiteLaw := rfl

theorem jointDependenceAtoms_eq : @SAP.P010.jointDependenceAtoms = @AronowAudit.P010.jointStepAtoms := rfl

theorem jointDependencePopulation_eq : @SAP.P010.jointDependencePopulation = @AronowAudit.P010.jointStepLaw := rfl

theorem selectionPopulationAtoms_eq : @SAP.P010.selectionPopulationAtoms = @AronowAudit.P010.selectionAtoms := rfl

theorem selectionPopulation_eq : @SAP.P010.selectionPopulation = @AronowAudit.P010.selectionLaw := rfl

theorem unitExponential_eq : @SAP.P010.unitExponential = @AronowAudit.P010.exponentialOne := rfl

theorem laplaceDistribution_eq : @SAP.P010.laplaceDistribution = @AronowAudit.P010.laplaceRate := rfl

theorem fairArmDistribution_eq : @SAP.P010.fairArmDistribution = @AronowAudit.P010.fairAssignment := rfl

theorem stratumPopulation_eq : @SAP.P010.stratumPopulation = @AronowAudit.P010.stratumLaw := rfl

theorem missingPassingPopulation_eq : @SAP.P010.missingPassingPopulation = @AronowAudit.P010.missingPassLaw := rfl

theorem betaPasserDistribution_eq : @SAP.P010.betaPasserDistribution = @AronowAudit.P010.beta33 := rfl

theorem heavyTailDistribution_eq : @SAP.P010.heavyTailDistribution = @AronowAudit.P010.heavySix := rfl

theorem commonOutcomePopulation_eq : @SAP.P010.commonOutcomePopulation = @AronowAudit.P010.diagonalLaw := rfl

theorem boundedPasserPopulation_eq : @SAP.P010.boundedPasserPopulation = @AronowAudit.P010.boundedPassLaw := rfl

theorem betaEndpointPopulation_eq : @SAP.P010.betaEndpointPopulation = @AronowAudit.P010.betaEndpointLaw := rfl

theorem normalCommonPopulation_eq : @SAP.P010.normalCommonPopulation = @AronowAudit.P010.normalCommonLaw := rfl

theorem simulationSubject_eq : @SAP.P010.simulationSubject = @AronowAudit.P010.simulationState := rfl

theorem simulationPopulation_eq : @SAP.P010.simulationPopulation = @AronowAudit.P010.simulationLaw := rfl

theorem checkCorrelation_eq : @SAP.P010.checkCorrelation = @AronowAudit.P010.checkCorrelation := rfl

theorem effectIntervalWidth_eq : @SAP.P010.effectIntervalWidth = @AronowAudit.P010.effectBoundWidth := rfl

theorem normalMixture_eq : @SAP.P010.normalMixture = @AronowAudit.P010.normalMixture := rfl

theorem mixtureLowerMean_eq : @SAP.P010.mixtureLowerMean = @AronowAudit.P010.mixtureLower := rfl

theorem mixtureUpperMean_eq : @SAP.P010.mixtureUpperMean = @AronowAudit.P010.mixtureUpper := rfl

theorem correctedEndpoints_eq : @SAP.P010.correctedEndpoints = @AronowAudit.P010.correctedBoundPair := rfl

end SAP.P010.Bridge
