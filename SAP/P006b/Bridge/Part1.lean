import SAP.P006b.Defs
import AronowAudit.P006.P006_CounterfactualMetrics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b.Bridge

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

/-- The finite probability, reward, selection and missing-data definitions agree by reduction. -/
theorem Admissible_eq : @SAP.P006b.Admissible = @AronowAudit.P006.Admissible := rfl

theorem bit_eq : @SAP.P006b.bit = @AronowAudit.P006.bit := rfl

theorem treatedCount_eq : @SAP.P006b.treatedCount = @AronowAudit.P006.treatedCount := rfl

theorem wATO_eq : @SAP.P006b.wATO = @AronowAudit.P006.wATO := rfl

theorem wATT_eq : @SAP.P006b.wATT = @AronowAudit.P006.wATT := rfl

theorem wWeightedTT_eq : @SAP.P006b.wWeightedTT = @AronowAudit.P006.wWeightedTT := rfl

theorem wTT_eq : @SAP.P006b.wTT = @AronowAudit.P006.wTT := rfl

theorem IsBest_eq : @SAP.P006b.IsBest = @AronowAudit.P006.IsBest := rfl

theorem bestValue_eq : @SAP.P006b.bestValue = @AronowAudit.P006.bestValue := rfl

theorem regret_eq : @SAP.P006b.regret = @AronowAudit.P006.regret := rfl

theorem positiveRule_eq : @SAP.P006b.positiveRule = @AronowAudit.P006.positiveRule := rfl

theorem printedAverageRule_eq : @SAP.P006b.printedAverageRule = @AronowAudit.P006.printedAverageRule := rfl

theorem emptyFactor_eq : @SAP.P006b.emptyFactor = @AronowAudit.P006.emptyFactor := rfl

theorem BinaryPolicy_eq : @SAP.P006b.BinaryPolicy = @AronowAudit.P006.BinaryPolicy := rfl

theorem binaryRule_eq : @SAP.P006b.binaryRule = @AronowAudit.P006.binaryRule := rfl

theorem binaryFeasible_eq : @SAP.P006b.binaryFeasible = @AronowAudit.P006.binaryFeasible := rfl

theorem binaryPolicies_eq : @SAP.P006b.binaryPolicies = @AronowAudit.P006.binaryPolicies := rfl

theorem coinMass_eq : @SAP.P006b.coinMass = @AronowAudit.P006.coinMass := rfl

theorem twoATO_eq : @SAP.P006b.twoATO = @AronowAudit.P006.twoATO := rfl

theorem oneTT_eq : @SAP.P006b.oneTT = @AronowAudit.P006.oneTT := rfl

theorem binaryWelfare_eq : @SAP.P006b.binaryWelfare = @AronowAudit.P006.binaryWelfare := rfl

theorem outcomeP1_eq : @SAP.P006b.outcomeP1 = @AronowAudit.P006.outcomeP1 := rfl

theorem effectP1_eq : @SAP.P006b.effectP1 = @AronowAudit.P006.effectP1 := rfl

theorem rewardP1_eq : @SAP.P006b.rewardP1 = @AronowAudit.P006.rewardP1 := rfl

theorem eventMean_eq : @SAP.P006b.eventMean = @AronowAudit.P006.eventMean := rfl

theorem finiteMass_eq : @SAP.P006b.finiteMass = @AronowAudit.P006.finiteMass := rfl

theorem finiteA_eq : @SAP.P006b.finiteA = @AronowAudit.P006.finiteA := rfl

theorem untreatedProbability_eq : @SAP.P006b.untreatedProbability = @AronowAudit.P006.untreatedProbability := rfl

theorem untreatedConditionalLaw_eq : @SAP.P006b.untreatedConditionalLaw = @AronowAudit.P006.untreatedConditionalLaw := rfl

theorem selectedBaseline_eq : @SAP.P006b.selectedBaseline = @AronowAudit.P006.selectedBaseline := rfl

theorem maximumDeviation_eq : @SAP.P006b.maximumDeviation = @AronowAudit.P006.maximumDeviation := rfl

theorem finiteSelectedBaseline_eq : @SAP.P006b.finiteSelectedBaseline = @AronowAudit.P006.finiteSelectedBaseline := rfl

theorem leaveOnlyType_eq : @SAP.P006b.leaveOnlyType = @AronowAudit.P006.leaveOnlyType := rfl

theorem treatOnlyType_eq : @SAP.P006b.treatOnlyType = @AronowAudit.P006.treatOnlyType := rfl

theorem twoTTConstant_eq : @SAP.P006b.twoTTConstant = @AronowAudit.P006.twoTTConstant := rfl

theorem logistic_eq : @SAP.P006b.logistic = @AronowAudit.P006.logistic := rfl

theorem signedOutcome_eq : @SAP.P006b.signedOutcome = @AronowAudit.P006.signedOutcome := rfl

theorem signedBernoulliMean_eq : @SAP.P006b.signedBernoulliMean = @AronowAudit.P006.signedBernoulliMean := rfl

theorem logisticWitnessMass_eq : @SAP.P006b.logisticWitnessMass = @AronowAudit.P006.logisticWitnessMass := rfl

theorem empiricalGroup_eq : @SAP.P006b.empiricalGroup = @AronowAudit.P006.empiricalGroup := rfl

theorem empiricalMean_eq : @SAP.P006b.empiricalMean = @AronowAudit.P006.empiricalMean := rfl

theorem empiricalGamma_eq : @SAP.P006b.empiricalGamma = @AronowAudit.P006.empiricalGamma := rfl

theorem missingWorldPrevalence_eq : @SAP.P006b.missingWorldPrevalence = @AronowAudit.P006.missingWorldPrevalence := rfl

theorem missingObservationProbability_eq : @SAP.P006b.missingObservationProbability = @AronowAudit.P006.missingObservationProbability := rfl

theorem missingWorldMass_eq : @SAP.P006b.missingWorldMass = @AronowAudit.P006.missingWorldMass := rfl

theorem missingRecord_eq : @SAP.P006b.missingRecord = @AronowAudit.P006.missingRecord := rfl

theorem missingObservedMass_eq : @SAP.P006b.missingObservedMass = @AronowAudit.P006.missingObservedMass := rfl

theorem missingWorldMean_eq : @SAP.P006b.missingWorldMean = @AronowAudit.P006.missingWorldMean := rfl

theorem missingUntreatedObservedMean_eq : @SAP.P006b.missingUntreatedObservedMean = @AronowAudit.P006.missingUntreatedObservedMean := rfl

theorem lowerBoundY0_eq : @SAP.P006b.lowerBoundY0 = @AronowAudit.P006.lowerBoundY0 := rfl

theorem lowerBoundY1_eq : @SAP.P006b.lowerBoundY1 = @AronowAudit.P006.lowerBoundY1 := rfl

theorem lowerBoundReward_eq : @SAP.P006b.lowerBoundReward = @AronowAudit.P006.lowerBoundReward := rfl

theorem lowerBoundWelfare_eq : @SAP.P006b.lowerBoundWelfare = @AronowAudit.P006.lowerBoundWelfare := rfl

theorem lowerBoundGamma_eq : @SAP.P006b.lowerBoundGamma = @AronowAudit.P006.lowerBoundGamma := rfl

theorem finiteIIDAverage_eq : @SAP.P006b.finiteIIDAverage = @AronowAudit.P006.finiteIIDAverage := rfl

theorem finiteIIDTT_eq : @SAP.P006b.finiteIIDTT = @AronowAudit.P006.finiteIIDTT := rfl

end SAP.P006b.Bridge
