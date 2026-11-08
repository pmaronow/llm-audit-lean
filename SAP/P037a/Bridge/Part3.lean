import SAP.P037a.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.Bridge

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

theorem treatmentPair_eq : treatmentPair = AronowAudit.P037.treatedPair := rfl
theorem treatment_eq : treatment = AronowAudit.P037.blockTreatment := rfl
theorem eligibleFraction_eq : eligibleFraction = AronowAudit.P037.witnessEligibleFraction := rfl
theorem stratumMass_eq : stratumMass = AronowAudit.P037.stratumCountMass := rfl
theorem countMass_eq : countMass = AronowAudit.P037.schoolCountMass := rfl
theorem stratumReferents_eq : stratumReferents = AronowAudit.P037.witnessStratumReferents := rfl
theorem assignmentMass_eq : assignmentMass = AronowAudit.P037.witnessStateMass := rfl
theorem compositionColumn_eq : compositionColumn = AronowAudit.P037.witnessInteraction := rfl
theorem potentialOutcome_eq : potentialOutcome = AronowAudit.P037.witnessPotentialOutcome := rfl
theorem observedOutcome_eq : observedOutcome = AronowAudit.P037.witnessObservedOutcome := rfl
theorem centeredCross_eq : centeredCross = AronowAudit.P037.blockCross := rfl
theorem regressionColumns_eq : regressionColumns = AronowAudit.P037.witnessColumns := rfl
theorem compositionMean_eq : compositionMean = AronowAudit.P037.witnessMean := rfl
theorem populationGram_eq : populationGram = AronowAudit.P037.witnessGram := rfl
theorem populationRhs_eq : populationRhs = AronowAudit.P037.witnessRhs := rfl
theorem mixturePotential_eq : mixturePotential = AronowAudit.P037.witnessMixturePotentialOutcome := rfl
theorem mixtureObserved_eq : mixtureObserved = AronowAudit.P037.witnessMixtureObservedOutcome := rfl

theorem witness_mixture_observed (w : CompositionAssignment) (i : Fin 4) :
    mixtureObserved (3/10) (-1/5) 0 (-1) 0 w i = observedOutcome w i := by
  simp only [mixtureObserved, observedOutcome]
  ring

theorem witness_mixture_potential (i : Fin 4) (treated : Bool) (c : ℝ) :
    mixturePotential (3/10) (-1/5) 0 (-1) 0 i treated c = potentialOutcome i treated c := by
  cases treated <;> simp only [mixturePotential, potentialOutcome, Bool.false_eq_true,
    ite_false, ite_true] <;> ring
theorem centeredBlockCross_eq : @centeredBlockCross = @AronowAudit.P037.withinBlocksCross := rfl
theorem innovation_eq : innovation = AronowAudit.P037.witnessInnovation := rfl
theorem expandedColumns_eq : expandedColumns = AronowAudit.P037.witnessExpandedColumns := rfl
theorem centeredColumns_eq : centeredColumns = AronowAudit.P037.witnessCenteredColumns := rfl
theorem compositionEquations_eq : @CompositionEquations = @AronowAudit.P037.WitnessEquations := rfl
theorem seedCompositionMean_eq : @seedCompositionMean = @AronowAudit.P037.stratifiedCompositionMean := rfl
theorem eligibleShare_eq : @eligibleShare = @AronowAudit.P037.stratifiedEligibleFraction := rfl
theorem seedComposition_eq : @seedComposition = @AronowAudit.P037.stratifiedSeedComposition := rfl

theorem randomized_iff {Ω : Type*} [Fintype Ω] {B : ℕ} (d : Design Ω)
    (D : Ω → (Fin B × Fin 4) → Bool) (R : Ω → (Fin B × Fin 4) → ℝ) :
    CompositionRandomized d D R ↔ AronowAudit.P037.RandomizedComposition (toDesign d) D R := Iff.rfl

theorem normal_iff {Ω K : Type*} [Fintype Ω] [Fintype K] {B : ℕ} (d : Design Ω)
    (X : K → Ω → (Fin B × Fin 4) → ℝ) (Y : Ω → (Fin B × Fin 4) → ℝ) (theta : K → ℝ) :
    NormalEquations d X Y theta ↔
      AronowAudit.P037.ExpectedNormalEquations (toDesign d) X Y theta := Iff.rfl

theorem extended_iff {Ω K : Type*} [Fintype Ω] [Fintype K] {B : ℕ} (d : Design Ω)
    (W : K → Ω → (Fin B × Fin 4) → ℝ) (R Y : Ω → (Fin B × Fin 4) → ℝ)
    (delta : K → ℝ) (beta : ℝ) :
    ExtendedNormalEquations d W R Y delta beta ↔
      AronowAudit.P037.AugmentedNormalEquations (toDesign d) W R Y delta beta := Iff.rfl

theorem waldStatistic_eq : waldStatistic = AronowAudit.P037.waldRatio := rfl
theorem tableS6Bins_eq : tableS6Bins = AronowAudit.P037.printsTableS6 := rfl
theorem reduction_eq : reduction = AronowAudit.P037.relativeReduction := rfl
theorem eligibleCount_eq : eligibleCount = AronowAudit.P037.seedEligibleCount := rfl
theorem fittedEffect_eq : fittedEffect = AronowAudit.P037.compositionEffect := rfl
theorem uniformDraw_eq : uniformDraw = AronowAudit.P037.unitUniformLaw := rfl
theorem normalizedWeights_eq : @normalizedWeights = @AronowAudit.P037.normalizeWeights := rfl
theorem openSimplex_eq : openSimplex = AronowAudit.P037.openProbabilitySimplex := rfl
theorem appendSimplex_eq : appendSimplex = AronowAudit.P037.completeSimplex := rfl
theorem simplexLaw_eq : simplexLaw = AronowAudit.P037.bayesianBootstrapLaw := rfl
theorem uniformWeightLaw_eq : uniformWeightLaw = AronowAudit.P037.normalizedUniformLaw := rfl
theorem ratioEvent_eq : ratioEvent = AronowAudit.P037.bootstrapWitnessEvent := rfl
theorem wls_eq : @WLS = @AronowAudit.P037.WeightedLeastSquares := rfl
theorem gramWeighted_eq : @gramWeighted = @AronowAudit.P037.weightedGram := rfl
theorem rhsWeighted_eq : @rhsWeighted = @AronowAudit.P037.weightedRhs := rfl
theorem wlsCoefficient_eq : @wlsCoefficient = @AronowAudit.P037.weightedCoefficient := rfl

end SAP.P037a.Bridge
