import SAP.P029a.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace SAP.P029a.Bridge

open SAP.P029a MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

noncomputable section

/-- Evaluation of the additional means in the already certified six-atom law. -/
theorem proveIgnorabilityWitnessMeans : IgnorabilityWitnessMeans := by
  norm_num [IgnorabilityWitnessMeans, FiniteLatentIgnorability,
    finiteConditionalMean, finiteExpectation, finiteProbability, finiteComplianceScore,
    sixAtomMass, bernoulliProductMass, complianceTypeMass, assignResponse,
    ignorabilityResponse, PotentialResponse.treatmentEffect, PotentialResponse.isComplier,
    PotentialResponse.receivedTreatment, PotentialResponse.observedOutcome, indicatorValue,
    Fintype.sum_prod_type, Fin.sum_univ_succ, Bool.forall_bool]

theorem proveBaselineEffectFacts : BaselineEffectFacts := by
  norm_num [BaselineEffectFacts, finiteExpectation, finiteConditionalMean, finiteProbability,
    sixAtomMass, bernoulliProductMass, complianceTypeMass, baselineResponse,
    PotentialResponse.treatmentEffect, PotentialResponse.isComplier,
    Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Fixed, finite sums supplement the existing independence counterexamples. -/
theorem proveIndependenceWitnessMeans : IndependenceWitnessMeans := by
  norm_num [IndependenceWitnessMeans, finiteArmDifference, finiteConditionalMean,
    finiteExpectation, finiteProbability, finiteComplianceScore,
    marginalWitnessMass, conditionalWitnessMass, bernoulliProductMass,
    marginalBaseMass, conditionalBaseMass, binaryEffectResponse, assignResponse,
    PotentialResponse.treatmentEffect, PotentialResponse.isComplier,
    PotentialResponse.receivedTreatment, PotentialResponse.observedOutcome, indicatorValue,
    Fintype.sum_prod_type, Fintype.sum_bool, Bool.forall_bool]

theorem proveIndependenceWitnessNumbers : IndependenceWitnessNumbers := by
  norm_num [IndependenceWitnessNumbers, finiteArmDifference, finiteConditionalMean,
    finiteExpectation, finiteProbability, finiteComplianceScore,
    marginalWitnessMass, conditionalWitnessMass, bernoulliProductMass,
    marginalBaseMass, conditionalBaseMass, binaryEffectResponse, assignResponse,
    PotentialResponse.isComplier, PotentialResponse.receivedTreatment,
    PotentialResponse.observedOutcome, indicatorValue,
    Fintype.sum_prod_type, Fintype.sum_bool, Bool.forall_bool]

/-- Reassociate the exported design/outcome equations and evaluate the five-entry products. -/
theorem proveNoiseCrossProductFacts : NoiseCrossProductFacts := by
  obtain ⟨gram, _, _, fit5, fit6, _, _⟩ := proveNoiseScoringWitnessFacts
  obtain ⟨out5, out6, _⟩ := proveNoiseWitnessOutcomes
  have cross5 : noiseDesignMatrix.transpose.mulVec (fun i => 5 + 5 * indicatorValue i.2.2) =
      noiseGramMatrix.mulVec ![5,5,0,0,0] := by
    rw [← funext out5, Matrix.mulVec_mulVec, gram]
  have cross6 : noiseDesignMatrix.transpose.mulVec (fun i => 5 + 6 * indicatorValue i.2.2) =
      noiseGramMatrix.mulVec ![5,6,0,0,0] := by
    rw [← funext out6, Matrix.mulVec_mulVec, gram]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cross5]
    ext j
    fin_cases j <;> norm_num [noiseGramMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · rw [cross6]
    ext j
    fin_cases j <;> norm_num [noiseGramMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · rw [cross5]
    exact fit5
  · rw [cross6]
    exact fit6

/-- This is the defining formula for every positive replicate count. -/
theorem proveCorrectedRMSE : CorrectedRMSE := by
  intro R _ t
  rfl

theorem proveConstantRunScoringFacts : ConstantRunScoringFacts := by
  intro R hR
  have hR0 : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hR)
  norm_num [rootMeanSquaredError, hR0]

theorem proveSEMWitnessMeans : SEMWitnessMeans := by
  norm_num [SEMWitnessMeans, finiteConditionalMean, finiteExpectation, finiteProbability,
    finiteCovariance, semDefierWitnessMass, bernoulliProductMass, semComplianceMass,
    semDefierResponse, semDependentResponse, semDependentAssignment,
    PotentialResponse.receivedTreatment, PotentialResponse.observedOutcome, indicatorValue,
    Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]

theorem proveHeterogeneousWitnessMeans : HeterogeneousWitnessMeans := by
  norm_num [HeterogeneousWitnessMeans, finiteConditionalMean, finiteExpectation,
    finiteProbability, finiteCovariance, bernoulliProductMass, heterogeneousResponse,
    PotentialResponse.treatmentEffect, PotentialResponse.isComplier,
    PotentialResponse.receivedTreatment, indicatorValue,
    Fintype.sum_prod_type, Fintype.sum_bool, Bool.forall_bool]

theorem proveClosedLikelihoodCertificates : ClosedLikelihoodCertificates := by
  intro p q
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem proveClosedFitValues : ClosedFitValues := by
  norm_num [ClosedFitValues, twoReceiptFit, twoReceiptLikelihood, bernoulliContribution,
    twoReceiptMass, Prod.forall, Bool.forall_bool]

theorem recordMean_eq_cell (v : Fin 9 → ℝ) (A : Fin 9 → Prop) :
    finiteConditionalMean recordMass (fun i => v i.1) (fun i => A i.1) =
      finiteConditionalMean recordCellMass v A := by
  exact AronowAudit.P029.canvass_cell_conditional_mean v A

theorem proveRaceReverseComparisons : RaceReverseComparisons := by
  let a : Fin 9 → ℝ := fun k => indicatorValue (decide (k.val < 3))
  let b : Fin 9 → ℝ := fun k => indicatorValue (decide (k.val < 3 ∨ 6 ≤ k.val))
  let yes : Fin 9 → Prop := fun k => decide (k.val % 3 = 0) = true
  let no : Fin 9 → Prop := fun k => decide (k.val % 3 = 0) = false
  change
    (finiteConditionalMean recordMass (fun i => a i.1) (fun i => yes i.1) >
      finiteConditionalMean recordMass (fun i => a i.1) (fun i => no i.1)) ∧
    (finiteConditionalMean recordMass (fun i => b i.1) (fun i => yes i.1) <
      finiteConditionalMean recordMass (fun i => b i.1) (fun i => no i.1))
  rw [recordMean_eq_cell a yes, recordMean_eq_cell a no,
    recordMean_eq_cell b yes, recordMean_eq_cell b no]
  norm_num [a, b, yes, no, finiteConditionalMean, finiteExpectation, finiteProbability,
    recordCellMass, recordCellCount, indicatorValue, Fin.sum_univ_succ]

end
end SAP.P029a.Bridge
