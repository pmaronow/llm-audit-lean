import SAP.P029a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P029a

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

def ConditionalWitnessFacts : Prop :=
    FiniteIVConditions conditionalWitnessMass (assignResponse binaryEffectResponse) Prod.snd ∧
    FiniteConditionallyIndependent conditionalWitnessMass (fun i => i.1.1.2.1)
      (fun i => ((binaryEffectResponse i.1).d0, (binaryEffectResponse i.1).d1))
      (fun i => (binaryEffectResponse i.1).x) ∧
    FiniteLatentIgnorability conditionalWitnessMass (assignResponse binaryEffectResponse) ∧
    finiteComplianceScore conditionalWitnessMass (assignResponse binaryEffectResponse) false = 1/4 ∧
    finiteComplianceScore conditionalWitnessMass (assignResponse binaryEffectResponse) true = 3/4 ∧
    (1/8 : ℝ) < finiteComplianceScore conditionalWitnessMass (assignResponse binaryEffectResponse) false ∧
    (1/8 : ℝ) < finiteComplianceScore conditionalWitnessMass (assignResponse binaryEffectResponse) true ∧
    finiteConditionalMean conditionalWitnessMass (fun i => (binaryEffectResponse i.1).treatmentEffect)
      (fun i => (binaryEffectResponse i.1).x = false) = 1/4 ∧
    finiteConditionalMean conditionalWitnessMass (fun i => (binaryEffectResponse i.1).treatmentEffect)
      (fun i => (binaryEffectResponse i.1).x = true) = 3/4 ∧
    finiteExpectation conditionalWitnessMass (fun i => (binaryEffectResponse i.1).treatmentEffect) = 1/2 ∧
    finiteExpectation conditionalWitnessMass (fun i => if (binaryEffectResponse i.1).isComplier then
      (binaryEffectResponse i.1).treatmentEffect else 0) = 5/16 ∧
    finiteWald conditionalWitnessMass (assignResponse binaryEffectResponse) Prod.snd (fun _ => 1) = 5/8 ∧
    finiteWald conditionalWitnessMass (assignResponse binaryEffectResponse) Prod.snd
      (fun i => 1 / finiteComplianceScore conditionalWitnessMass (assignResponse binaryEffectResponse)
        (binaryEffectResponse i.1).x) = 1/2

def ConditionalWitnessDependence : Prop :=
    ¬ FiniteIndependent conditionalWitnessMass (fun i => i.1.1.2.1)
      (fun i => ((binaryEffectResponse i.1).d0, (binaryEffectResponse i.1).d1))

def MarginalWitnessFacts : Prop :=
    FiniteIVConditions marginalWitnessMass (assignResponse binaryEffectResponse) Prod.snd ∧
    FiniteIndependent marginalWitnessMass (fun i => i.1.1.2.1)
      (fun i => ((binaryEffectResponse i.1).d0, (binaryEffectResponse i.1).d1)) ∧
    finiteProbability marginalWitnessMass (fun i => i.1.1.2.1 = true) = 1/2 ∧
    finiteProbability marginalWitnessMass (fun i => i.1.1.2.1 = false) = 1/2 ∧
    finiteProbability marginalWitnessMass (fun i => (binaryEffectResponse i.1).x = false) = 5/8 ∧
    finiteProbability marginalWitnessMass (fun i => (binaryEffectResponse i.1).x = true) = 3/8 ∧
    finiteComplianceScore marginalWitnessMass (assignResponse binaryEffectResponse) false = 2/5 ∧
    finiteComplianceScore marginalWitnessMass (assignResponse binaryEffectResponse) true = 2/3 ∧
    (1/3 : ℝ) < finiteComplianceScore marginalWitnessMass (assignResponse binaryEffectResponse) false ∧
    (1/3 : ℝ) < finiteComplianceScore marginalWitnessMass (assignResponse binaryEffectResponse) true ∧
    finiteConditionalMean marginalWitnessMass (fun i => (binaryEffectResponse i.1).treatmentEffect)
      (fun i => (binaryEffectResponse i.1).x = false) = 2/5 ∧
    finiteConditionalMean marginalWitnessMass (fun i => (binaryEffectResponse i.1).treatmentEffect)
      (fun i => (binaryEffectResponse i.1).isComplier ∧ (binaryEffectResponse i.1).x = false) = 1/4 ∧
    finiteConditionalMean marginalWitnessMass (fun i => (binaryEffectResponse i.1).treatmentEffect)
      (fun i => (binaryEffectResponse i.1).x = true) = 2/3 ∧
    finiteConditionalMean marginalWitnessMass (fun i => (binaryEffectResponse i.1).treatmentEffect)
      (fun i => (binaryEffectResponse i.1).isComplier ∧ (binaryEffectResponse i.1).x = true) = 3/4 ∧
    finiteExpectation marginalWitnessMass (fun i => (binaryEffectResponse i.1).treatmentEffect) = 1/2 ∧
    finiteWald marginalWitnessMass (assignResponse binaryEffectResponse) Prod.snd (fun _ => 1) = 1/2 ∧
    finiteExpectation marginalWitnessMass (fun i => 1 / finiteComplianceScore marginalWitnessMass (assignResponse binaryEffectResponse)
      (binaryEffectResponse i.1).x) = 17/8 ∧
    finiteWald marginalWitnessMass (assignResponse binaryEffectResponse) Prod.snd
      (fun i => 1 / finiteComplianceScore marginalWitnessMass (assignResponse binaryEffectResponse)
        (binaryEffectResponse i.1).x) = 7/16

def MarginalNestedProbabilities : Prop :=
    finiteConditionalMean marginalWitnessMass (fun i => indicatorValue (binaryEffectResponse i.1).d1)
      (fun i => (binaryEffectResponse i.1).x = false) = 7/10 ∧
    finiteConditionalMean marginalWitnessMass (fun i => indicatorValue (binaryEffectResponse i.1).d1)
      (fun i => (binaryEffectResponse i.1).x = true) = 5/6 ∧
    finiteConditionalMean marginalWitnessMass (fun i => indicatorValue (binaryEffectResponse i.1).d0)
      (fun i => (binaryEffectResponse i.1).d1 = true ∧ (binaryEffectResponse i.1).x = false) = 3/7 ∧
    finiteConditionalMean marginalWitnessMass (fun i => indicatorValue (binaryEffectResponse i.1).d0)
      (fun i => (binaryEffectResponse i.1).d1 = true ∧ (binaryEffectResponse i.1).x = true) = 1/5

def WeightedPopulationIdentities : Prop :=
  ∀ {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialResponse X) (Z : Ω → Bool)
    (hiv : IVConditions μ U Z)
    (hpos : ∀ x, 0 < eventProbability μ {ω | (U ω).x = x} → 0 < complianceProbability μ U x)
    (w : X → ℝ) (hw : ∀ x, 0 < w x),
    populationWald μ U Z (fun ω => w (U ω).x) =
      (∫ ω, w (U ω).x * (if (U ω).isComplier then (U ω).treatmentEffect else 0) ∂μ) /
      (∫ ω, w (U ω).x * (if (U ω).isComplier then 1 else 0) ∂μ) ∧
    populationWald μ U Z (fun ω => w (U ω).x) =
      (∑ x, eventProbability μ {ω | (U ω).x = x} * w x * complianceProbability μ U x * complierMeanEffect μ U x) /
      (∑ x, eventProbability μ {ω | (U ω).x = x} * w x * complianceProbability μ U x) ∧
    populationWald μ U Z (fun _ => 1) = eventMean μ (fun ω => (U ω).treatmentEffect) {ω | (U ω).isComplier} ∧
    populationWald μ U Z (fun ω => 1 / complianceProbability μ U (U ω).x) =
      ∑ x, eventProbability μ {ω | (U ω).x = x} * complierMeanEffect μ U x ∧
    populationWald μ U Z (fun _ => 1) - populationWald μ U Z (fun ω => 1 / complianceProbability μ U (U ω).x) =
      populationCovariance μ (fun ω => complianceProbability μ U (U ω).x) (fun ω => complierMeanEffect μ U (U ω).x) /
      eventProbability μ {ω | (U ω).isComplier} ∧
    (eventMean μ (fun ω => (U ω).treatmentEffect) {ω | (U ω).isComplier} = (∫ ω, (U ω).treatmentEffect ∂μ) →
      populationWald μ U Z (fun _ => 1) = (∫ ω, (U ω).treatmentEffect ∂μ)) ∧
    ((∀ x, 0 < eventProbability μ {ω | (U ω).x = x} → LatentMeanEquality μ U x) →
      populationWald μ U Z (fun ω => 1 / complianceProbability μ U (U ω).x) = (∫ ω, (U ω).treatmentEffect ∂μ))

def JointIndependenceSufficiency : Prop :=
  ∀ {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialResponse X) (Z : Ω → Bool)
    (hiv : IVConditions μ U Z)
    (hpos : ∀ x, 0 < eventProbability μ {ω | (U ω).x = x} → 0 < complianceProbability μ U x)
    (hind : IndepFun (fun ω => (U ω).treatmentEffect)
        (fun ω => (decide (U ω).isComplier, (U ω).x)) μ ∨
      IndepFun (fun ω => decide (U ω).isComplier)
        (fun ω => ((U ω).treatmentEffect, (U ω).x)) μ),
    eventMean μ (fun ω => (U ω).treatmentEffect) {ω | (U ω).isComplier} = (∫ ω, (U ω).treatmentEffect ∂μ) ∧
    (∀ x, 0 < eventProbability μ {ω | (U ω).x = x} → LatentMeanEquality μ U x) ∧
    populationWald μ U Z (fun _ => 1) = (∫ ω, (U ω).treatmentEffect ∂μ) ∧
    populationWald μ U Z (fun ω => 1 / complianceProbability μ U (U ω).x) = (∫ ω, (U ω).treatmentEffect ∂μ)

def NoiseScoringWitnessFacts : Prop :=
    noiseDesignMatrix.transpose * noiseDesignMatrix = noiseGramMatrix ∧
    (∀ opposite i, (noisePotentialResponse opposite i).treatmentEffect = 5 ∧
      (noisePotentialResponse opposite i).receivedTreatment i.2.2 = i.2.2 ∧
      (noisePotentialResponse opposite i).observedOutcome i.2.2 =
        5 + (if opposite then 6 else 5) * indicatorValue i.2.2) ∧
    codedBenchmark (fun _ : Fin 500 => ![1/5,0,0]) = 6 ∧
    noiseGramMatrix⁻¹.mulVec (noiseGramMatrix.mulVec ![5,5,0,0,0]) = ![5,5,0,0,0] ∧
    noiseGramMatrix⁻¹.mulVec (noiseGramMatrix.mulVec ![5,6,0,0,0]) = ![5,6,0,0,0] ∧
    ((5 - 6 : ℝ)^2 = 1 ∧ (5 - 5 : ℝ)^2 = 0) ∧
    ((6 - 6 : ℝ)^2 = 0 ∧ (6 - 5 : ℝ)^2 = 1)

def NoiseDesignDeterminant : Prop :=
    noiseGramMatrix.det = 3906250000

def PositiveWeightRecovery : Prop :=
  ∀ (w : NoiseRecord → ℝ) (hw : ∀ i, 0 < w i)
    (b : Fin 5 → ℝ),
    let G := noiseDesignMatrix.transpose * Matrix.diagonal w * noiseDesignMatrix
    IsUnit G.det ∧ G⁻¹.mulVec (noiseDesignMatrix.transpose.mulVec
      ((Matrix.diagonal w).mulVec (noiseDesignMatrix.mulVec b))) = b

def NoiseWitnessAdmissibility : Prop :=
    (-1 : ℝ) < 1/5 ∧ (1/5 : ℝ) < 1 ∧
    (∀ k : Fin 5, ∀ j : Fin 3, (-1 : ℝ) < observedNoiseProfile k j ∧ observedNoiseProfile k j < 1) ∧
    (∀ z, latentAlwaysOrComplier 2 = 1 ∧ latentAlwaysTaker 2 (-2) = 0 ∧ latentComplier 2 (-2) = 1 ∧
      latentReceipt 2 (-2) z = indicatorValue z) ∧
    (∑ i : NoiseRecord, indicatorValue i.2.2) = 250

def NoiseWitnessOutcomes : Prop :=
    (∀ i : NoiseRecord, noiseDesignMatrix.mulVec ![5,5,0,0,0] i = 5 + 5 * indicatorValue i.2.2) ∧
    (∀ i : NoiseRecord, noiseDesignMatrix.mulVec ![5,6,0,0,0] i = 5 + 6 * indicatorValue i.2.2) ∧
    codedBenchmark (fun _ : Fin 500 => ![1/5,0,0]) = 6

def BenchmarkMoments : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (X : Fin n → Fin 3 → Ω → ℝ)
    (hm : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun ij : Fin n × Fin 3 => X ij.1 ij.2) μ)
    (hlaw : ∀ i j, Measure.map (X i j) μ = uniformCovariateLaw),
    (∫ ω, codedBenchmark (fun i j => X i j ω) ∂μ) = 5 ∧
    populationCovariance μ (fun ω => codedBenchmark (fun i j => X i j ω))
      (fun ω => codedBenchmark (fun i j => X i j ω)) = 25 / n

def ExpectedErrorIdentity : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t B : Ω → ℝ)
    (ht : MemLp t 2 μ) (hB2 : MemLp B 2 μ) (hB : (∫ ω, B ω ∂μ) = 5),
    (∫ ω, (t ω - B ω)^2 ∂μ) - (∫ ω, (t ω - 5)^2 ∂μ) =
      populationCovariance μ B B - 2 * populationCovariance μ t B

def FiniteExpectedErrorIdentity : Prop :=
  ∀ {L : Type*} [Fintype L]
    (p t B : L → ℝ) (hp : IsFiniteLaw p) (hB : finiteExpectation p B = 5),
    finiteExpectation p (fun i => (t i - B i)^2) - finiteExpectation p (fun i => (t i - 5)^2) =
      finiteVariance p B - 2 * finiteCovariance p t B

def FiniteRunErrorIdentity : Prop :=
  ∀ {R : ℕ} (t B : Fin R → ℝ) (hR : 0 < R),
    (∑ r, (t r - B r)^2) / R - (∑ r, (t r - 5)^2) / R =
      (∑ r, (B r - 5)^2) / R - (2 / R) * ∑ r, (t r - 5) * (B r - 5)

def ConstantPopulationEffect : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y0 : Ω → ℝ)
    (C : Set Ω) (hC : MeasurableSet C) (hc : 0 < eventProbability μ C),
    (∫ ω, ((Y0 ω + 5) - Y0 ω) ∂μ) = 5 ∧
    eventMean μ (fun ω => (Y0 ω + 5) - Y0 ω) C = 5

def ConstantSampleEffect : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (Y0 : Fin n → ℝ),
    (∑ i, ((Y0 i + 5) - Y0 i)) / (n : ℝ) = 5

def SquaredErrorIdentity : Prop :=
  ∀ (t B : ℝ),
    (t - B)^2 - (t - 5)^2 = (B - 5)^2 - 2 * (t - 5) * (B - 5)

def UniformCovariateMoments : Prop :=
    (∫ u, u ∂uniformCovariateLaw) = 0 ∧
    (∫ u, u^2 ∂uniformCovariateLaw) = 1/3

def PerturbationDerivatives : Prop :=
    HasDerivAt (fun t : ℝ => (t + 11) / (t + 7)) (-1/16) 1 ∧
    HasDerivAt (fun _ : ℝ => (3/2 : ℝ)) 0 1

def SpecifiedPerturbationFacts : Prop :=
  ∀ (t : ℝ) (ht : 0 < t),
    specifiedPerturbedScores t false = 1/(3+t) ∧ specifiedPerturbedScores t true = 3/4 ∧
    finiteWald (fun _ : Bool × Bool × Fin 4 => 1/16) weightWitnessResponse weightWitnessAssignment
      (fun i => perturbedRecordWeight t i / specifiedUnweightedScores i.1) = 3/2 ∧
    finiteWald (fun _ : Bool × Bool × Fin 4 => 1/16) weightWitnessResponse weightWitnessAssignment
      (fun i => perturbedRecordWeight t i / specifiedPerturbedScores t i.1) = (t+11)/(t+7)

def InsideLogMinimumInvariance : Prop :=
  ∀ {I Θ : Type*} [Fintype I]
    (L : Θ → I → ℝ) (w : I → ℝ) (hL : ∀ θ i, 0 < L θ i)
    (hw : ∀ i, 0 < w i) (θ : Θ),
    IsGlobalMinimum (fun t => insideLogObjective (L t) w) θ ↔
      IsGlobalMinimum (fun t => observationWeightedObjective (L t) (fun _ => 1)) θ

def InsideLogWeightIdentity : Prop :=
  ∀ {I : Type*} [Fintype I]
    (L w : I → ℝ) (hL : ∀ i, 0 < L i) (hw : ∀ i, 0 < w i),
    insideLogObjective L w = insideLogObjective L (fun _ => 1) - ∑ i, Real.log (w i)

def SpecifiedTwoSidedFacts : Prop :=
    (∀ x, 0 < specifiedInsideLogRates (x,false) ∧ specifiedInsideLogRates (x,false) < specifiedInsideLogRates (x,true) ∧
      specifiedInsideLogRates (x,true) < 1) ∧
    (∀ x, 0 < specifiedWeightedRates (x,false) ∧ specifiedWeightedRates (x,false) < specifiedWeightedRates (x,true) ∧
      specifiedWeightedRates (x,true) < 1) ∧
    fourCellLikelihood specifiedWeightedRates / fourCellLikelihood specifiedInsideLogRates = 729/1500625 ∧
    (729/1500625 : ℝ) < 1 ∧
    specifiedWeightedRates (false,true) - specifiedWeightedRates (false,false) = 3/20 ∧
    specifiedWeightedRates (true,true) - specifiedWeightedRates (true,false) = 3/14

def SpecifiedScoreWaldFacts : Prop :=
    (9 / (9 + 3) : ℝ) = specifiedWeightedScores false ∧
    (27 / (27 + 1) : ℝ) = specifiedWeightedScores true ∧
    finiteWald (fun _ : Bool × Bool × Fin 4 => 1/16) weightWitnessResponse weightWitnessAssignment
      (fun i => receiptDependentWeight i / specifiedUnweightedScores i.1) = 3/2 ∧
    finiteWald (fun _ : Bool × Bool × Fin 4 => 1/16) weightWitnessResponse weightWitnessAssignment
      (fun i => receiptDependentWeight i / specifiedWeightedScores i.1) = 17/10 ∧
    (3/2 : ℝ) ≠ 17/10

def ZeroWeightContribution : Prop :=
  ∀ (L : ℝ),
    L * 0 = 0 ∧ extendedNegativeLog (L * 0) = ⊤

def ZeroWeightObjective : Prop :=
  ∀ {I : Type*} [Fintype I]
    (L w : I → ℝ) (hL : ∀ j, L j ∈ Ioc (0 : ℝ) 1) (i : I)
    (hi : w i = 0) (hw : ∀ j, j ≠ i → 0 < w j),
    extendedInsideLogObjective L w = ⊤

end
end SAP.P029a
