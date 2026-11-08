import SAP.P029a.Bridge.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029a.Bridge

universe u v

theorem target1 : T1Statement := by
  exact ⟨proveIgnorabilityWitnessFacts, provePotentialPairIndependence, proveIgnorabilityWitnessMeans⟩

theorem target2 : T2Statement.{u,v} := by
  exact ⟨proveIgnorabilityIncomparability, proveBaselineSelectionFacts,
    proveBaselineEffectFacts, proveOneSidedImplication⟩

theorem target3 : T3Statement := by
  exact ⟨proveMarginalWitnessFacts, proveMarginalNestedProbabilities,
    proveConditionalWitnessFacts, proveConditionalWitnessDependence,
    proveIndependenceWitnessMeans, proveIndependenceWitnessNumbers⟩

theorem target4 : T4Statement.{u,v} := by
  exact ⟨proveWeightedPopulationIdentities, proveJointIndependenceSufficiency,
    proveMarginalWitnessFacts, proveConditionalWitnessFacts, proveIndependenceWitnessMeans⟩

theorem target5 : T5Statement := by
  exact ⟨proveNoiseScoringWitnessFacts, proveNoiseDesignDeterminant,
    proveNoiseWitnessAdmissibility, provePositiveWeightRecovery, proveNoiseCrossProductFacts,
    proveConstantRunScoringFacts⟩

theorem target6 : T6Statement.{u} := by
  refine ⟨?_, proveConstantSampleEffect, proveConstantPopulationEffect,
    proveCorrectedRMSE, proveUniformCovariateMoments, proveBenchmarkMoments,
    proveSquaredErrorIdentity, proveFiniteRunErrorIdentity, proveFiniteExpectedErrorIdentity,
    proveExpectedErrorIdentity, proveNoiseScoringWitnessFacts, proveNoiseWitnessAdmissibility⟩
  intro y
  ring

theorem target7 : T7Statement.{u,v} := by
  exact ⟨proveInsideLogWeightIdentity, proveInsideLogMinimumInvariance,
    proveZeroWeightContribution, proveZeroWeightObjective, proveSpecifiedScoreWaldFacts,
    proveSpecifiedTwoSidedFacts, proveSpecifiedPerturbationFacts, provePerturbationDerivatives⟩

theorem target8 : T8Statement.{u,v} := by
  exact ⟨proveZeroAndUnitWeights, proveIntegerWeightReplication, proveCellStrictConcavity,
    proveCellUniqueMaximum, proveFreeCellUniqueMinimum, proveConcreteFreeCellFits,
    proveConstantWeightEquivalence, proveSpecifiedScoreWaldFacts, proveSpecifiedTwoSidedFacts,
    proveSpecifiedPerturbationFacts⟩

theorem target9 : T9Statement := by
  exact ⟨proveRaceCompletionFacts, proveRawRaceCodePreservation,
    proveRecordedAssignmentSupport, proveRaceReverseComparisons⟩

theorem target10 : T10Statement.{u} := by
  exact ⟨proveBinaryPopulationSign, proveRaleighContactComparisons, proveRaceCompletionFacts,
    proveRecordedAssignmentSupport, proveGroupedCovarianceIdentity⟩

theorem target11 : T11Statement := by
  exact ⟨proveSEMDefierFacts, proveSEMDependenceFacts, proveSEMWitnessMeans⟩

theorem target12 : T12Statement.{u,v} := by
  exact ⟨proveSEMDefierFacts, proveSEMDependenceFacts, proveSEMConstantEffect,
    proveHeterogeneousIVFacts, proveHeterogeneousWitnessMeans⟩

theorem target13 : T13Statement := by
  exact ⟨proveSaturatedBiasWitnessFacts, proveSaturatedScoreBiasFacts,
    proveFivePerArmBiasFacts, proveClosedLikelihoodCertificates, proveClosedFitValues⟩

end SAP.P029a.Bridge
