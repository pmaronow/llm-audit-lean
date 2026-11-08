import SAP.P029a.Defs
import AronowAudit.P029.P029_Audit
import AronowAudit.P029.Wave1.Gap.GP029B2b
import AronowAudit.P029.Wave1.Gap.GP029B4
import AronowAudit.P029.Wave1.Gap.GP029B5
import AronowAudit.P029.Wave1.Gap.GP029B1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace SAP.P029a.Bridge

open SAP.P029a MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology

noncomputable section

/-- Preserve every potential response and covariate field. -/
def toAudit {X : Type*} (u : PotentialResponse X) : AronowAudit.P029.PotentialUnit X :=
  ⟨u.x, u.d0, u.d1, u.y0, u.y1⟩

theorem effect_eq {X : Type*} (u : PotentialResponse X) :
    (toAudit u).tau = u.treatmentEffect := rfl

theorem receipt_eq {X : Type*} (u : PotentialResponse X) (z : Bool) :
    (toAudit u).receipt z = u.receivedTreatment z := rfl

theorem outcome_eq {X : Type*} (u : PotentialResponse X) (z : Bool) :
    (toAudit u).outcome z = u.observedOutcome z := rfl

theorem finite_conditions_iff {L X : Type*} [Fintype L] (p : L → ℝ)
    (U : L → PotentialResponse X) (Z : L → Bool) :
    FiniteIVConditions p U Z ↔ AronowAudit.P029.FIV p (fun i => toAudit (U i)) Z :=
  Iff.rfl

theorem finite_wald_eq {L X : Type*} [Fintype L] (p : L → ℝ)
    (U : L → PotentialResponse X) (Z : L → Bool) (w : L → ℝ) :
    finiteWald p U Z w = AronowAudit.P029.fWald p (fun i => toAudit (U i)) Z w := rfl

theorem conditions_iff {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialResponse X) (Z : Ω → Bool) :
    IVConditions μ U Z ↔ AronowAudit.P029.IVAssumptions μ (fun ω => toAudit (U ω)) Z :=
  Iff.rfl

theorem wald_eq {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialResponse X) (Z : Ω → Bool) (w : Ω → ℝ) :
    populationWald μ U Z w =
      AronowAudit.P029.mWald μ (fun ω => toAudit (U ω)) Z w := rfl

theorem score_eq {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialResponse X) (x : X) :
    complianceProbability μ U x =
      AronowAudit.P029.scoreAt μ (fun ω => toAudit (U ω)) x := rfl

theorem ignorability_response_eq (i : Fin 3) :
    toAudit (ignorabilityResponse i) = AronowAudit.P029.case1Unit i := rfl

theorem baseline_response_eq (i : Fin 3) :
    toAudit (baselineResponse i) = AronowAudit.P029.case2Unit i := rfl

theorem binary_response_eq (i : BinaryTriple × Bool) :
    toAudit (binaryEffectResponse i) = AronowAudit.P029.independenceUnit i := rfl

theorem noise_response_eq (b : Bool) (i : NoiseRecord) :
    toAudit (noisePotentialResponse b i) = AronowAudit.P029.rmseHomogeneousUnit b i := rfl

theorem record_response_eq (Y : CanvassingRecord → ℝ) (i : CanvassingRecord) :
    toAudit (recordPotentialResponse Y i) = AronowAudit.P029.canvassUnit Y i := rfl


theorem proveIgnorabilityWitnessFacts : IgnorabilityWitnessFacts := by
  exact @AronowAudit.P029.ignorability_counterexample

theorem provePotentialPairIndependence : PotentialPairIndependence := by
  exact @AronowAudit.P029.potential_pair_independent_of_receipt

theorem proveOneSidedImplication : OneSidedImplication := by
  intro Ω X _ _ _ μ _ U Z hiv hside x hx hc hi
  exact AronowAudit.P029.Wave1.one_sided_ignorability_implication_proof μ
    (fun ω => toAudit (U ω)) Z hiv hside x hx hc hi

theorem proveBaselineSelectionFacts : BaselineSelectionFacts := by
  exact @AronowAudit.P029.baseline_selection_counterexample

theorem proveIgnorabilityIncomparability : IgnorabilityIncomparability := by
  exact @AronowAudit.P029.corrected_ignorability_incomparability

theorem proveConditionalWitnessFacts : ConditionalWitnessFacts := by
  exact @AronowAudit.P029.conditional_independence_counterexample

theorem proveConditionalWitnessDependence : ConditionalWitnessDependence := by
  exact @AronowAudit.P029.conditional_witness_not_marginally_independent

theorem proveMarginalWitnessFacts : MarginalWitnessFacts := by
  exact @AronowAudit.P029.marginal_independence_counterexample

theorem proveMarginalNestedProbabilities : MarginalNestedProbabilities := by
  exact @AronowAudit.P029.marginal_witness_nested_probabilities

theorem proveWeightedPopulationIdentities : WeightedPopulationIdentities := by
  intro Ω X _ _ _ _ μ _ U Z hiv hpos w hw
  exact AronowAudit.P029.Wave1.corrected_weighted_limits_proof μ
    (fun ω => toAudit (U ω)) Z hiv hpos w hw

theorem proveJointIndependenceSufficiency : JointIndependenceSufficiency := by
  intro Ω X _ _ _ _ μ _ U Z hiv hpos hind
  exact AronowAudit.P029.Wave1.joint_independence_suffices_proof μ
    (fun ω => toAudit (U ω)) Z hiv hpos hind

theorem proveNoiseScoringWitnessFacts : NoiseScoringWitnessFacts := by
  exact @AronowAudit.P029.homogeneous_rmse_counterexample

theorem proveNoiseDesignDeterminant : NoiseDesignDeterminant := by
  exact @AronowAudit.P029.rmse_design_determinant

theorem provePositiveWeightRecovery : PositiveWeightRecovery := by
  exact @AronowAudit.P029.rmse_positive_weight_recovery

theorem proveNoiseWitnessAdmissibility : NoiseWitnessAdmissibility := by
  exact @AronowAudit.P029.rmse_witness_admissible

theorem proveNoiseWitnessOutcomes : NoiseWitnessOutcomes := by
  exact @AronowAudit.P029.rmse_witness_outcomes

theorem proveBenchmarkMoments : BenchmarkMoments := by
  exact @AronowAudit.P029.Wave1.heterogeneous_benchmark_moments_proof

theorem proveExpectedErrorIdentity : ExpectedErrorIdentity := by
  exact @AronowAudit.P029.expected_mse_discrepancy

theorem proveFiniteExpectedErrorIdentity : FiniteExpectedErrorIdentity := by
  exact @AronowAudit.P029.finite_expected_mse_discrepancy

theorem proveFiniteRunErrorIdentity : FiniteRunErrorIdentity := by
  intro R t B _
  exact AronowAudit.P029.finite_run_mse_discrepancy t B

theorem proveConstantPopulationEffect : ConstantPopulationEffect := by
  exact @AronowAudit.P029.homogeneous_population_effect

theorem proveConstantSampleEffect : ConstantSampleEffect := by
  exact @AronowAudit.P029.homogeneous_sample_effect

theorem proveSquaredErrorIdentity : SquaredErrorIdentity := by
  exact @AronowAudit.P029.squared_error_discrepancy

theorem proveUniformCovariateMoments : UniformCovariateMoments := by
  exact @AronowAudit.P029.uniform_covariate_moments

theorem provePerturbationDerivatives : PerturbationDerivatives := by
  exact @AronowAudit.P029.bootstrap_first_step_derivative

theorem proveSpecifiedPerturbationFacts : SpecifiedPerturbationFacts := by
  exact @AronowAudit.P029.bootstrap_refit_ratio

theorem proveInsideLogMinimumInvariance : InsideLogMinimumInvariance := by
  exact @AronowAudit.P029.inside_log_minimizers

theorem proveInsideLogWeightIdentity : InsideLogWeightIdentity := by
  exact @AronowAudit.P029.inside_log_weights_identity

theorem proveSpecifiedTwoSidedFacts : SpecifiedTwoSidedFacts := by
  exact @AronowAudit.P029.two_sided_weight_counterexample

theorem proveSpecifiedScoreWaldFacts : SpecifiedScoreWaldFacts := by
  exact @AronowAudit.P029.weighted_score_counterexample

theorem proveZeroWeightContribution : ZeroWeightContribution := by
  exact @AronowAudit.P029.zero_weight_infinite_contribution

theorem proveZeroWeightObjective : ZeroWeightObjective := by
  exact @AronowAudit.P029.zero_weight_objective_infinite

theorem proveConstantWeightEquivalence : ConstantWeightEquivalence := by
  exact @AronowAudit.P029.constant_weight_minimizers

theorem proveZeroAndUnitWeights : ZeroAndUnitWeights := by
  intro I _ L _
  constructor
  · intro i
    exact (AronowAudit.P029.corrected_objective_zero_unit L i).1
  · simp [observationWeightedObjective, insideLogObjective]

theorem proveIntegerWeightReplication : IntegerWeightReplication := by
  exact @AronowAudit.P029.integer_weight_replication

theorem proveFreeCellUniqueMinimum : FreeCellUniqueMinimum := by
  exact @AronowAudit.P029.saturated_weighted_objective_minimum

theorem proveCellStrictConcavity : CellStrictConcavity := by
  exact @AronowAudit.P029.weighted_cell_strict_concavity

theorem proveCellUniqueMaximum : CellUniqueMaximum := by
  exact @AronowAudit.P029.weighted_cell_unique_max

theorem proveRecordedAssignmentSupport : RecordedAssignmentSupport := by
  exact @AronowAudit.P029.canvass_assignment_supported

theorem proveRaceCompletionFacts : RaceCompletionFacts := by
  exact @AronowAudit.P029.racial_completion_counterexample

theorem proveRawRaceCodePreservation : RawRaceCodePreservation := by
  exact @AronowAudit.P029.racial_raw_code_preservation

theorem proveGroupedCovarianceIdentity : GroupedCovarianceIdentity := by
  intro n G _ s A group
  obtain ⟨hcov, hgroup⟩ :=
    AronowAudit.P029.Wave1.grouped_covariance_decomposition_proof s A group
  exact ⟨hcov, fun g _ hconst => hgroup g hconst⟩

theorem proveBinaryPopulationSign : BinaryPopulationSign := by
  exact @AronowAudit.P029.binary_population_count_sign

theorem proveRaleighContactComparisons : RaleighContactComparisons := by
  exact @AronowAudit.P029.raleigh_recorded_comparison

theorem proveSEMDefierFacts : SEMDefierFacts := by
  exact @AronowAudit.P029.sem_defier_counterexample

theorem proveSEMDependenceFacts : SEMDependenceFacts := by
  exact @AronowAudit.P029.sem_dependence_counterexample

theorem proveHeterogeneousIVFacts : HeterogeneousIVFacts := by
  exact @AronowAudit.P029.heterogeneous_iv_counterexample

theorem proveSEMConstantEffect : SEMConstantEffect := by
  exact @AronowAudit.P029.sem_forces_constant_effect

theorem proveConstantScorePopulationFacts : ConstantScorePopulationFacts := by
  exact @AronowAudit.P029.constant_score_counterexample_law

end
end SAP.P029a.Bridge
