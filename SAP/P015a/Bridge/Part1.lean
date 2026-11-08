import SAP.P015a.Defs
import AronowAudit.P015.P015_Regression
import AronowAudit.P015.P015_PaperSpecializations
import AronowAudit.P015.P015_PaperDomains
import AronowAudit.P015.Wave1.Gap.FidP015

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015a.Bridge
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
attribute [local instance] Classical.propDecidable
universe u v

open AronowAudit.P015 AronowAudit.P015.Wave1

theorem mean_eq : @SAP.P015a.mean = @AronowAudit.P015.fExpectation := rfl

theorem IsProbabilityVector_eq : @SAP.P015a.IsProbabilityVector = @AronowAudit.P015.IsLaw := rfl

theorem eventMass_eq : @SAP.P015a.eventMass = @AronowAudit.P015.fMass := rfl

theorem conditionalMean_eq : @SAP.P015a.conditionalMean = @AronowAudit.P015.fCondMean := rfl

theorem conditionalProbability_eq : @SAP.P015a.conditionalProbability = @AronowAudit.P015.fCondProb := rfl

theorem residualWeight_eq : @SAP.P015a.residualWeight = @AronowAudit.P015.fWeight := rfl

theorem effectiveLaw_eq : @SAP.P015a.effectiveLaw = @AronowAudit.P015.fEffective := rfl

theorem ConditionalIndependent_eq : @SAP.P015a.ConditionalIndependent = @AronowAudit.P015.fCondIndep := rfl

theorem effectContrast_eq : @SAP.P015a.effectContrast = @AronowAudit.P015.contrast := rfl

theorem inverseProbabilityVariable_eq : @SAP.P015a.inverseProbabilityVariable = @AronowAudit.P015.ipw := rfl

theorem variance_eq : @SAP.P015a.variance = @AronowAudit.P015.fVariance := rfl

theorem populationCoefficients_eq : @SAP.P015a.populationCoefficients = @AronowAudit.P015.populationOLS := rfl

theorem binaryCovariate_eq : @SAP.P015a.binaryCovariate = @AronowAudit.P015.binaryX := rfl

theorem binaryTreatment_eq : @SAP.P015a.binaryTreatment = @AronowAudit.P015.binaryD := rfl

theorem rareProbability_eq : @SAP.P015a.rareProbability = @AronowAudit.P015.rareLaw := rfl

theorem rarePotentialOutcome_eq : @SAP.P015a.rarePotentialOutcome = @AronowAudit.P015.rareY := rfl

theorem rareIPW_eq : @SAP.P015a.rareIPW = @AronowAudit.P015.rareZ := rfl

theorem uniformProbability_eq : @SAP.P015a.uniformProbability = @AronowAudit.P015.multiLaw := rfl

theorem multivaluedTreatment_eq : @SAP.P015a.multivaluedTreatment = @AronowAudit.P015.multiD := rfl

theorem outcomeWorldA_eq : @SAP.P015a.outcomeWorldA = @AronowAudit.P015.worldA := rfl

theorem outcomeWorldB_eq : @SAP.P015a.outcomeWorldB = @AronowAudit.P015.worldB := rfl

theorem fittedResidual_eq : @SAP.P015a.fittedResidual = @AronowAudit.P015.sampleResidual := rfl

theorem leastSquares_eq : @SAP.P015a.leastSquares = @AronowAudit.P015.ols := rfl

theorem fittedZeroControls_eq : @SAP.P015a.fittedZeroControls = @AronowAudit.P015.zeroSampleV := rfl

theorem fittedZeroDesign_eq : @SAP.P015a.fittedZeroDesign = @AronowAudit.P015.zeroSampleW := rfl

theorem fittedZeroTreatment_eq : @SAP.P015a.fittedZeroTreatment = @AronowAudit.P015.zeroSampleD := rfl

theorem inverseLogit_eq : @SAP.P015a.inverseLogit = @AronowAudit.P015.logistic := rfl

theorem logOdds_eq : @SAP.P015a.logOdds = @AronowAudit.P015.logit := rfl

theorem firstTaylorPolynomial_eq : @SAP.P015a.firstTaylorPolynomial = @AronowAudit.P015.firstTaylor := rfl

theorem bernoulliLogLikelihood_eq : @SAP.P015a.bernoulliLogLikelihood = @AronowAudit.P015.binomialLogLikelihood := rfl

theorem likelihoodMultiplier_eq : @SAP.P015a.likelihoodMultiplier = @AronowAudit.P015.scoreMultiplier := rfl

theorem canonicalContribution_eq : @SAP.P015a.canonicalContribution = @AronowAudit.P015.canonicalLogLikelihood := rfl

theorem residualEquation_eq : @SAP.P015a.residualEquation = @AronowAudit.P015.groupedResidual := rfl

theorem likelihoodScore_eq : @SAP.P015a.likelihoodScore = @AronowAudit.P015.groupedScore := rfl

theorem logLikelihood_eq : @SAP.P015a.logLikelihood = @AronowAudit.P015.groupedLikelihood := rfl

theorem oddsDesign_eq : @SAP.P015a.oddsDesign = @AronowAudit.P015.oddsW := rfl

theorem oddsCounts_eq : @SAP.P015a.oddsCounts = @AronowAudit.P015.oddsSuccess := rfl

theorem oddsInverseLink_eq : @SAP.P015a.oddsInverseLink = @AronowAudit.P015.oddsMean := rfl

theorem standardNormalCDF_eq : @SAP.P015a.standardNormalCDF = @AronowAudit.P015.normalCDF := rfl

theorem standardNormalDensity_eq : @SAP.P015a.standardNormalDensity = @AronowAudit.P015.normalPDF := rfl

theorem probitQuantile_eq : @SAP.P015a.probitQuantile = @AronowAudit.P015.probitA := rfl

theorem probitDesign_eq : @SAP.P015a.probitDesign = @AronowAudit.P015.probitW := rfl

theorem probitCounts_eq : @SAP.P015a.probitCounts = @AronowAudit.P015.probitSuccess := rfl

theorem probitMultiplier_eq : @SAP.P015a.probitMultiplier = @AronowAudit.P015.probitH := rfl

theorem squareLinkCovariate_eq : @SAP.P015a.squareLinkCovariate = @AronowAudit.P015.rootX := rfl

theorem squareLinkTreatment_eq : @SAP.P015a.squareLinkTreatment = @AronowAudit.P015.rootD := rfl

theorem squareLinkProbability_eq : @SAP.P015a.squareLinkProbability = @AronowAudit.P015.rootLaw := rfl

theorem squareLinkPropensity_eq : @SAP.P015a.squareLinkPropensity = @AronowAudit.P015.rootE := rfl

theorem squareLinkBaseline_eq : @SAP.P015a.squareLinkBaseline = @AronowAudit.P015.rootBaseline := rfl

theorem squareLinkDesign_eq : @SAP.P015a.squareLinkDesign = @AronowAudit.P015.rootZ := rfl

theorem squareLinkPotential_eq : @SAP.P015a.squareLinkPotential = @AronowAudit.P015.rootPotential := rfl

theorem squareLinkResponseProbability_eq : @SAP.P015a.squareLinkResponseProbability = @AronowAudit.P015.rootProbability := rfl

theorem squareInverseLink_eq : @SAP.P015a.squareInverseLink = @AronowAudit.P015.rootMean := rfl

theorem squareLinkExpectedLikelihood_eq : @SAP.P015a.squareLinkExpectedLikelihood = @AronowAudit.P015.rootLikelihood := rfl

theorem SquareLinkAdmissible_eq : @SAP.P015a.SquareLinkAdmissible = @AronowAudit.P015.rootAdmissible := rfl

theorem SquareLinkMLDerivative_eq : @SAP.P015a.SquareLinkMLDerivative = @AronowAudit.P015.RootMLDerivative := rfl

theorem uniformUnitInterval_eq : @SAP.P015a.uniformUnitInterval = @AronowAudit.P015.rootUniformLaw := rfl

theorem squareLinkUnitLaw_eq : @SAP.P015a.squareLinkUnitLaw = @AronowAudit.P015.rootUnitLaw := rfl

theorem unitCovariate_eq : @SAP.P015a.unitCovariate = @AronowAudit.P015.rootUnitX := rfl

theorem unitTreatment_eq : @SAP.P015a.unitTreatment = @AronowAudit.P015.rootUnitD := rfl

theorem unitUniform_eq : @SAP.P015a.unitUniform = @AronowAudit.P015.rootUnitU := rfl

theorem unitPotentialOutcome_eq : @SAP.P015a.unitPotentialOutcome = @AronowAudit.P015.rootUnitY := rfl

theorem unitEffect_eq : @SAP.P015a.unitEffect = @AronowAudit.P015.rootUnitTau := rfl

theorem squareLinkScore_eq : @SAP.P015a.squareLinkScore = @AronowAudit.P015.rootScore := rfl

theorem conditionalCellLaw_eq : @SAP.P015a.conditionalCellLaw = @AronowAudit.P015.cellLaw := rfl

theorem cellExpectation_eq : @SAP.P015a.cellExpectation = @AronowAudit.P015.cellMean := rfl

theorem cellVariance_eq : @SAP.P015a.cellVariance = @AronowAudit.P015.cellVar := rfl

theorem cellProbability_eq : @SAP.P015a.cellProbability = @AronowAudit.P015.cellProb := rfl

theorem discreteResidualWeight_eq : @SAP.P015a.discreteResidualWeight = @AronowAudit.P015.discreteWeight := rfl

theorem discreteEffectiveLaw_eq : @SAP.P015a.discreteEffectiveLaw = @AronowAudit.P015.discreteEffective := rfl

theorem independentDrawLaw_eq : @SAP.P015a.independentDrawLaw = @AronowAudit.P015.iidLaw := rfl

theorem empiricalMean_eq : @SAP.P015a.empiricalMean = @AronowAudit.P015.sampleAverage := rfl

theorem inverseLogitTaylor_eq : @SAP.P015a.inverseLogitTaylor = @AronowAudit.P015.logisticTaylor := rfl

theorem canonicalSampleLikelihood_eq : @SAP.P015a.canonicalSampleLikelihood = @AronowAudit.P015.canonicalLikelihood := rfl

theorem ValidCanonicalFamily_eq : @SAP.P015a.ValidCanonicalFamily = @AronowAudit.P015.CanonicalFamily := rfl

theorem UniformIndependentSampling_eq : @SAP.P015a.UniformIndependentSampling = @AronowAudit.P015.MultiSampling := rfl

theorem observedTriple_eq : @SAP.P015a.observedTriple = @AronowAudit.P015.multivaluedObserved := rfl

theorem populationResidualWeight_eq : @SAP.P015a.populationResidualWeight = @AronowAudit.P015.populationWeight := rfl

theorem conditionalTreatmentVariance_eq : @SAP.P015a.conditionalTreatmentVariance = @AronowAudit.P015.conditionalVariance := rfl

theorem logisticResponseLaw_eq : @SAP.P015a.logisticResponseLaw = @AronowAudit.P015.Wave1.bernoulliResponseLaw := rfl

theorem poissonLogResponseLaw_eq : @SAP.P015a.poissonLogResponseLaw = @AronowAudit.P015.Wave1.poissonResponseLaw := rfl

theorem rareWitness_eq : @SAP.P015a.rareWitness = @AronowAudit.P015.RareCounterexample := rfl

theorem multivaluedWitness_eq : @SAP.P015a.multivaluedWitness.{u} = @AronowAudit.P015.MultivaluedCounterexample.{u} := rfl

theorem fittedZeroWitness_eq : @SAP.P015a.fittedZeroWitness = @AronowAudit.P015.FittedZeroCounterexample := rfl

theorem oddsWitness_eq : @SAP.P015a.oddsWitness = @AronowAudit.P015.OddsCounterexample := rfl

theorem probitWitness_eq : @SAP.P015a.probitWitness = @AronowAudit.P015.ProbitCounterexample := rfl

theorem squareLinkWitness_eq : @SAP.P015a.squareLinkWitness = @AronowAudit.P015.RootLinkCounterexample := rfl

theorem positivityRepair_eq : @SAP.P015a.positivityRepair.{u,v} = @AronowAudit.P015.PositivityCorrection.{u,v} := rfl

theorem T2_correspondence : SAP.P015a.T2Statement.{u} ↔
  (AronowAudit.P015.MultivaluedCounterexample.{u} ∧
    (AronowAudit.P015.fCondMean AronowAudit.P015.multiLaw AronowAudit.P015.binaryX
      (AronowAudit.P015.fWeight AronowAudit.P015.multiLaw AronowAudit.P015.binaryX AronowAudit.P015.multiD) 0 = 1/4 ∧
     AronowAudit.P015.fCondMean AronowAudit.P015.multiLaw AronowAudit.P015.binaryX
      (AronowAudit.P015.fWeight AronowAudit.P015.multiLaw AronowAudit.P015.binaryX AronowAudit.P015.multiD) 1 = 1)) := Iff.rfl

theorem T1_correspondence : SAP.P015a.T1Statement ↔
  (RareCounterexample ∧
  (fCondProb (rareLaw (1/1000000)) binaryX binaryD 0 1 = 1/1000000 ∧
   fCondProb (rareLaw (1/1000000)) binaryX binaryD 0 0 = 1-1/1000000 ∧
   fCondProb (rareLaw (1/1000000)) binaryX binaryD 1 1 = 1/2 ∧
   fCondProb (rareLaw (1/1000000)) binaryX binaryD 1 0 = 1/2 ∧
   fCondMean (rareLaw (1/1000000)) binaryX
     (fWeight (rareLaw (1/1000000)) binaryX binaryD) 0 =
     (1/1000000)*(1-1/1000000) ∧
   fMass (fEffective (rareLaw (1/1000000)) binaryX binaryD) (fun a => binaryX a=0) =
     ((1/1000000)*(1-1/1000000))/((1/1000000)*(1-1/1000000)+1/4) ∧
   0 < fExpectation (rareLaw (1/1000000)) (fWeight (rareLaw (1/1000000)) binaryX binaryD))) := Iff.rfl

theorem T3_correspondence : SAP.P015a.T3Statement ↔
  (FittedZeroCounterexample ∧
  (fun i => sampleResidual zeroSampleV zeroSampleD (ols zeroSampleV zeroSampleD) i ^ 2) =
    (![0,0,1/4,1/4] : Fin 4 → ℝ)) := Iff.rfl

theorem T4_correspondence : SAP.P015a.T4Statement.{u,v} ↔
  (PositivityCorrection.{u,v} ∧
  (∀ {Ω : Type u} {B : Type v} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSingletonClass B] [Countable B] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → B) (D : Ω → ℝ) (hX : Measurable X) (hD : Measurable D)
    (h₂ : MemLp D 2 P) (x : B) (hx : 0 < P {s | X s=x}),
    (cellVar P X D x = 0 → ∀ d d' : ℝ, d ≠ d' →
      ¬ (0 < cellProb P X D x d ∧ 0 < cellProb P X D x d')) ∧
    ((∀ᵐ s ∂P, D s=0 ∨ D s=1) →
      cellProb P X D x 0 = 1-cellProb P X D x 1 ∧
      (0 < cellVar P X D x ↔ 0 < cellProb P X D x 0 ∧ 0 < cellProb P X D x 1)) ∧
    (0 < (∫ s, discreteWeight P X D s ∂P) →
      Integrable (discreteWeight P X D) P →
      IsProbabilityMeasure (discreteEffective P X D) ∧
      ((∀ᵐ s ∂P, D s=0 ∨ D s=1) →
        0 < discreteEffective P X D {s | X s=x} →
        0 < cellVar P X D x ∧
        0 < cellProb (discreteEffective P X D) X D x 0 ∧
        0 < cellProb (discreteEffective P X D) X D x 1)))) := Iff.rfl

theorem T5_correspondence : SAP.P015a.T5Statement ↔
  (OddsCounterexample ∧
  (∀ η : ℝ, 0 < η → scoreMultiplier oddsMean η = 1/η)) := Iff.rfl

theorem T6_correspondence : SAP.P015a.T6Statement ↔
  (ProbitCounterexample ∧
  (Set.Nonempty {a : ℝ | 3/4 ≤ normalCDF a} ∧
   BddBelow {a : ℝ | 3/4 ≤ normalCDF a}) ∧
  (∀ v : Fin 3 → ℝ,
    HasDerivAt (fun t => groupedLikelihood probitW (fun _ => 8) probitSuccess normalCDF
      (fun j => (![0,0,probitA] : Fin 3 → ℝ) j+t*v j))
      (∑ i, probitH (probitW.mulVec ![0,0,probitA] i)*
        (probitSuccess i-8*normalCDF (probitW.mulVec ![0,0,probitA] i))*probitW.mulVec v i) 0)) := Iff.rfl

theorem T7_correspondence : SAP.P015a.T7Statement ↔
  (RootLinkCounterexample ∧
  (∀ θ : Fin 3 → ℝ,
    let γ : Fin 3 → ℝ := ![θ 0-θ 1/2, θ 1, θ 2-θ 1/4]
    γ 1 = θ 1 ∧ ∀ i : Fin 6,
      dotProduct (![1,rootD i,rootX i] : Fin 3 → ℝ) γ = rootZ.mulVec θ i) ∧
  (∀ α β γ : ℝ, ∃ θ : Fin 3 → ℝ,
    (![θ 0-θ 1/2, θ 1, θ 2-θ 1/4] : Fin 3 → ℝ) = ![α,β,γ]) ∧
  Integrable rootUnitD rootUnitLaw ∧
  (∀ a ε : ℝ, Integrable (fun s => rootUnitY a ε (rootUnitD s) s) rootUnitLaw)) := Iff.rfl

end SAP.P015a.Bridge
